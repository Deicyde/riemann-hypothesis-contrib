#!/usr/bin/env python3
"""Rebase verified linear candidates across README-only main changes using Git trees."""
import json
import os
import re
import subprocess
import rebase_open_prs as worker

def raw_commit(sha):
    raw=worker.git('cat-file','commit',sha).stdout
    headers,message=raw.split('\n\n',1)
    author=next(line[7:] for line in headers.splitlines() if line.startswith('author '))
    return author,message

def replay_commit(sha,new_parent):
    old_parents=worker.value('show','-s','--format=%P',sha).split()
    if len(old_parents)!=1:
        raise RuntimeError('Expected a linear prepared history')
    merged=worker.git('merge-tree','--write-tree','--merge-base='+old_parents[0],new_parent,sha,check=False)
    if merged.returncode:
        raise RuntimeError('Tree merge conflict: '+merged.stdout[-4000:])
    tree=merged.stdout.splitlines()[0]
    author,message=raw_commit(sha)
    match=re.fullmatch(r'(.*) <([^>]*)> (\d+) ([+-]\d{4})',author)
    if not match: raise RuntimeError('Unrecognized author metadata')
    worker.ENV.update(GIT_AUTHOR_NAME=match[1],GIT_AUTHOR_EMAIL=match[2],
                      GIT_AUTHOR_DATE='@'+match[3]+' '+match[4])
    new=worker.git('commit-tree',tree,'-p',new_parent,input=message).stdout.strip()
    # commit-tree adds a final newline; GitHub's commit API also creates valid
    # commit messages without one. Preserve those original bytes as well.
    if raw_commit(new)==(author,message+'\n') and not message.endswith('\n'):
        headers=worker.git('cat-file','commit',new).stdout.split('\n\n',1)[0]
        new=worker.git('hash-object','-t','commit','-w','--stdin',input=headers+'\n\n'+message).stdout.strip()
    if raw_commit(new)!=(author,message):
        raise RuntimeError('Author or complete commit message changed')
    return new

def main():
    cfg=json.loads((worker.HERE/'prepared.json').read_text())
    worker.ROOT.mkdir(parents=True,exist_ok=True);worker.OUT.mkdir(parents=True,exist_ok=True)
    if not worker.REPO.exists():subprocess.run(['git','init','--quiet',str(worker.REPO)],check=True)
    git,value=worker.git,worker.value
    git('config','user.name','github-actions[bot]')
    git('config','user.email','41898282+github-actions[bot]@users.noreply.github.com')
    git('config','gc.auto','0')
    git('fetch','--no-tags',worker.UPSTREAM,'refs/heads/main:refs/remotes/upstream/main',timeout=1800)
    base=value('rev-parse','refs/remotes/upstream/main')
    git('fetch','--no-tags',worker.OWN,*['refs/heads/'+r['prepared_branch']+':refs/remotes/prepared/'+str(r['number']) for r in cfg['results']],timeout=1800)
    worker.BASE=base;worker.TAG=base[:10]
    run=os.environ['GITHUB_RUN_ID']+'-tree-restack'
    results=[]
    for candidate in cfg['results']:
        result=dict(candidate);n=result['number'];old=result['rebased_head'];previous_base=result['base']
        print('RESTACK #'+str(n),flush=True)
        try:
            if value('rev-parse','refs/remotes/prepared/'+str(n))!=old:
                raise RuntimeError('Preparation branch advanced')
            changed=git('diff','--name-only','--no-renames',previous_base,base).stdout.splitlines()
            if any(path!='README.md' for path in changed):
                raise RuntimeError('Main changes extend beyond README; a fresh review is required')
            commits=value('rev-list','--reverse','--topo-order',previous_base+'..'+old).splitlines()
            new=base
            for sha in commits:new=replay_commit(sha,new)
            paths=['src','lean-toolchain','lake-manifest.json','lakefile.toml']
            fingerprints={path:value('rev-parse',old+':'+path)==value('rev-parse',new+':'+path) for path in paths}
            changes=git('diff','--name-only','--no-renames',old,new).stdout.splitlines()
            if not all(fingerprints.values()) or any(path!='README.md' for path in changes):
                raise RuntimeError('Prepared source or non-README files changed')
            if git('diff','--check',old,new,'--','README.md',check=False).returncode:
                raise RuntimeError('README whitespace check failed')
            if n in cfg.get('revalidate',[]):
                git('update-ref','HEAD',new)
                diff=git('diff','--check',base,new,check=False)
                result['diff_check']=diff.returncode==0
                result['diff_check_output']=diff.stdout[-4000:]
                result['imports']=worker.import_check()
                result['changes']=value('diff','--shortstat',base,new)
                if not result['diff_check'] or result['imports']['missing_count'] or not result['imports']['acyclic']:
                    raise RuntimeError('Revalidation failed: '+json.dumps({k:result[k] for k in ['diff_check','diff_check_output','imports']}))
            result.update(previous_prepared_head=old,rebased_head=new,base=base,
                          restack_source_unchanged=fingerprints,
                          author_and_message_metadata_unchanged=True,
                          restack_commit_count=len(commits),status='rebased')
            branch='maintenance/rebased-pr-'+str(n)+'-'+worker.TAG+'-'+run
            result['prepared_branch']=branch
            worker.publish_ref(new,branch)
            print('PREPARED #'+str(n)+' '+new,flush=True)
        except Exception as error:
            result.update(status='error',error=str(error))
        results.append(result)
        (worker.OUT/('pr-'+str(n)+'.json')).write_text(json.dumps(result,indent=2))
    for key in ['GIT_AUTHOR_NAME','GIT_AUTHOR_EMAIL','GIT_AUTHOR_DATE']:worker.ENV.pop(key,None)
    worker.finish_report(results,run)

if __name__=='__main__':main()
