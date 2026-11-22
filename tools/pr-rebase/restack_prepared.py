#!/usr/bin/env python3
"""Move already-reviewed rebase candidates onto a newer documentation-only main."""
import json
import os
from pathlib import Path
import subprocess
import rebase_open_prs as worker

def main():
    cfg=json.loads((worker.HERE/'prepared.json').read_text())
    worker.ROOT.mkdir(parents=True,exist_ok=True)
    worker.OUT.mkdir(parents=True,exist_ok=True)
    if not worker.REPO.exists():
        subprocess.run(['git','init','--quiet',str(worker.REPO)],check=True)
    git,value=worker.git,worker.value
    git('config','user.name','github-actions[bot]')
    git('config','user.email','41898282+github-actions[bot]@users.noreply.github.com')
    git('config','gc.auto','0')
    git('fetch','--no-tags',worker.UPSTREAM,'refs/heads/main:refs/remotes/upstream/main',timeout=1800)
    base=value('rev-parse','refs/remotes/upstream/main')
    if base!=cfg['base']:
        raise RuntimeError('Main advanced; refresh and review the prepared snapshot first: '+base)
    git('fetch','--no-tags',worker.OWN,*['refs/heads/'+p['prepared_branch']+':refs/remotes/prepared/'+str(p['number']) for p in cfg['results']],timeout=1800)
    if value('rev-parse',base+':src')!=value('rev-parse',cfg['previous_base']+':src'):
        raise RuntimeError('Main source changed; a fresh source review is required')
    run=os.environ['GITHUB_RUN_ID']+'-restack'
    worker.BASE=base;worker.TAG=base[:10]
    results=[]
    for candidate in cfg['results']:
        n=candidate['number'];result=dict(candidate)
        print('RESTACK #'+str(n),flush=True)
        try:
            original=candidate['rebased_head']
            if value('rev-parse','refs/remotes/prepared/'+str(n))!=original:
                raise RuntimeError('Preparation branch advanced')
            git('checkout','--detach','--force',original,timeout=1800)
            old_metadata=value('log','--reverse','--format=%an%x00%ae%x00%aI%x00%B%x00',cfg['previous_base']+'..'+original)
            replay=git('rebase','--no-update-refs','--empty=drop',base,check=False,timeout=1800)
            if replay.returncode:
                paths=git('diff','--name-only','--diff-filter=U').stdout.splitlines()
                if paths==['README.md']:
                    temporary=worker.ROOT/'readme';temporary.mkdir(exist_ok=True)
                    for stage in (1,2,3):
                        (temporary/str(stage)).write_text(value('show',':'+str(stage)+':README.md')+'\n')
                    merged=subprocess.run(['git','merge-file','-p',str(temporary/'2'),str(temporary/'1'),str(temporary/'3')],capture_output=True,text=True)
                    if merged.returncode==0:
                        (worker.REPO/'README.md').write_text(merged.stdout)
                        git('add','--','README.md')
                        replay=git('rebase','--continue',check=False,timeout=1800)
            if replay.returncode:
                result.update(status='conflict',**worker.conflict_details())
                git('rebase','--abort')
            else:
                new=value('rev-parse','HEAD')
                result['previous_prepared_head']=original
                result['rebased_head']=new
                fingerprints={p:value('rev-parse',original+':'+p)==value('rev-parse',new+':'+p) for p in ['src','lean-toolchain','lake-manifest.json','lakefile.toml']}
                result['restack_source_unchanged']=fingerprints
                new_metadata=value('log','--reverse','--format=%an%x00%ae%x00%aI%x00%B%x00',base+'..'+new)
                result['author_and_message_metadata_unchanged']=old_metadata==new_metadata
                result['diff_check']=git('diff','--check',base,new,check=False).returncode==0
                if not all(fingerprints.values()) or not result['author_and_message_metadata_unchanged'] or not result['diff_check']:
                    raise RuntimeError('Restack invariant failed')
                branch='maintenance/rebased-pr-'+str(n)+'-'+worker.TAG+'-'+run
                result['prepared_branch']=branch
                result['status']='rebased'
                try:
                    worker.publish_ref(new,branch)
                except RuntimeError as error:
                    result['status']='publication-blocked'
                    result['publication_error']=str(error)
                print('PREPARED #'+str(n)+' '+new,flush=True)
        except Exception as error:
            result.update(status='error',error=str(error))
            git('rebase','--abort',check=False)
        results.append(result)
        (worker.OUT/('pr-'+str(n)+'.json')).write_text(json.dumps(result,indent=2))
    worker.finish_report(results,run)

if __name__=='__main__':
    main()
