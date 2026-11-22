#!/usr/bin/env python3
"""Replay prepared candidates after the reviewed cleanup batch entered main."""
import json,os,subprocess
import rebase_open_prs as w
from restack_trees import raw_commit

def keep_current_proofs(number,reviewed_paths):
    if number not in (9,97,98):return []
    details=w.conflict_details();resolved=[]
    for conflict in details['conflicts']:
        path=conflict['path'];stages=conflict['stages']
        if path not in reviewed_paths or not path.endswith('.lean') or set(stages)!={'1','2','3'}:continue
        (w.REPO/path).write_text(w.git('cat-file','blob',stages['2']).stdout)
        w.git('add','--',path)
        resolved.append({'path':path,'reason':'retain-new-main-proof-in-format-or-import-cleanup','ours':stages['2']})
    return resolved

def main():
    cfg=json.loads((w.HERE/'prepared.json').read_text());batch=os.environ['PR_BATCH']
    groups={'owned':[74,80,81,91,97],'wide':[9,10,79,98,104],
            'proofs-a':[33,54,62,69,71,75,76],'proofs-b':[82,83,86,87,90,92,94,95]}
    rows=[r for r in cfg['results'] if r['number'] in groups.get(batch,cfg.get('only',[]))]
    w.ROOT.mkdir(parents=True,exist_ok=True);w.OUT.mkdir(parents=True,exist_ok=True)
    subprocess.run(['git','init','--quiet',str(w.REPO)],check=True)
    git,value=w.git,w.value
    for key,v in [('user.name','github-actions[bot]'),('user.email','41898282+github-actions[bot]@users.noreply.github.com'),('gc.auto','0'),('core.quotePath','false')]:git('config',key,v)
    git('fetch','--no-tags',w.UPSTREAM,'refs/heads/main:refs/remotes/upstream/main',timeout=1800)
    base=value('rev-parse','refs/remotes/upstream/main')
    if any(p!='README.md' for p in git('diff','--name-only',cfg['base'],base).stdout.splitlines()):
        raise RuntimeError('Main proof or infrastructure changed again; review the new commits first')
    w.BASE=base;w.TAG=base[:10];run=os.environ['GITHUB_RUN_ID']+'-'+batch
    git('fetch','--no-tags',w.OWN,*['refs/heads/'+r['prepared_branch']+':refs/remotes/prepared/'+str(r['number']) for r in rows],timeout=1800)
    reviewed_paths=set(git('diff','--name-only',cfg['previous_base'],cfg['base'],'--','src').stdout.splitlines())
    for n,sha in cfg.get('contributor_heads',{}).items():
        git('fetch','--no-tags',w.UPSTREAM,'refs/pull/'+n+'/head:refs/remotes/latest-author/'+n,timeout=1800)
        if value('rev-parse','refs/remotes/latest-author/'+n)!=sha:raise RuntimeError('Contributor advanced again')
    cache={};results=[]
    for candidate in rows:
        result=dict(candidate);n=result['number'];old=result['rebased_head'];previous_base=result['base']
        print('REBASE #'+str(n),flush=True)
        try:
            if value('rev-parse','refs/remotes/prepared/'+str(n))!=old:raise RuntimeError('Preparation branch advanced')
            originals={raw_commit(c) for c in value('rev-list',previous_base+'..'+old).splitlines()}
            git('checkout','--detach','--force',old,timeout=1800)
            replay=git('rebase','--no-update-refs','--empty=drop',base,check=False,timeout=1800)
            resolutions=[]
            for sequence in range(500):
                if replay.returncode==0:break
                changed=w.resolve_manual_ports(n)
                changed+=keep_current_proofs(n,reviewed_paths)
                changed+=w.resolve_deprecated_identifiers(n)
                changed+=w.resolve_module_conflicts(n)
                resolutions.extend(changed)
                if git('ls-files','-u').stdout:
                    if not w.await_manual_review(n,run,sequence):break
                elif not changed:break
                replay=git('rebase','--continue',check=False,timeout=1800)
            result.update(previous_prepared_head=old,base=base,automatic_resolution_count=len(resolutions),automatic_resolutions=resolutions)
            if replay.returncode:
                result.update(status='conflict',**w.conflict_details(),rebase_head=value('rev-parse','REBASE_HEAD'))
                checkpoint=value('rev-parse','HEAD');branch='maintenance/checkpoint-pr-'+str(n)+'-'+w.TAG+'-'+run
                w.publish_ref(checkpoint,branch);result.update(checkpoint_head=checkpoint,checkpoint_branch=branch)
                git('rebase','--abort')
            else:
                new=value('rev-parse','HEAD');retained=[raw_commit(c) for c in value('rev-list',base+'..'+new).splitlines()]
                if any(c not in originals for c in retained):raise RuntimeError('A retained author or full commit message changed')
                source=value('rev-parse',new+':src')
                if source not in cache:cache[source]=w.import_check()
                result.update(rebased_head=new,changes=value('diff','--shortstat',base,new),
                              diff_check=git('diff','--check',base,new,check=False).returncode==0,
                              imports=cache[source],retained_commit_metadata_verified=True,retained_commit_count=len(retained),
                              protected_files={p:value('rev-parse',base+':'+p)==value('rev-parse',new+':'+p) for p in ['lean-toolchain','lake-manifest.json','src/Challenge.lean']})
                result.pop('restack_source_unchanged',None)
                result['status']='empty-after-rebase' if new==base or not result['changes'] else 'rebased'
                branch='maintenance/rebased-pr-'+str(n)+'-'+w.TAG+'-'+run;w.publish_ref(new,branch);result['prepared_branch']=branch
                if str(n) in cfg.get('contributor_heads',{}):
                    author=cfg['contributor_heads'][str(n)]
                    result['contributor_latest_source_preserved']=source==value('rev-parse',author+':src')
                    if not result['contributor_latest_source_preserved']:
                        result['contributor_source_differences']=git('diff','--name-only',author,new,'--','src').stdout.splitlines()
                        result['status']='needs-contributor-source-review'
            print('RESULT '+json.dumps({k:v for k,v in result.items() if k in ['number','status','changes','rebased_head','conflict_count','diff_check','imports']}),flush=True)
        except Exception as error:
            result.update(status='error',error=str(error));git('rebase','--abort',check=False)
        results.append(result);(w.OUT/('pr-'+str(n)+'.json')).write_text(json.dumps(result,indent=2))
    w.finish_report(results,run)

if __name__=='__main__':main()
