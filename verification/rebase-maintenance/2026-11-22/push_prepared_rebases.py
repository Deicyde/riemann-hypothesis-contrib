#!/usr/bin/env python3
"""Preview prepared RH rebases, or publish selected PRs with explicit Git leases.

Run after `gh auth setup-git`, with an account allowed to update each PR branch.
Default: read-only preview. `--apply 9 10` publishes those PRs; `--apply-all`
publishes every ready entry. No PR is merged or closed. Lean builds remain required.
The manifest and script must be in the same directory.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

UPSTREAM='leanprover-community/riemann-hypothesis'
OWN='Deicyde/riemann-hypothesis-contrib'

def run(*args,cwd=None):
    return subprocess.run(args,cwd=cwd,check=True,text=True,stdout=subprocess.PIPE).stdout.strip()

def git(repo,*args):
    return run('git','-c','core.hooksPath=/dev/null','-C',str(repo),*args)

def remote_head(url,branch):
    line=run('git','ls-remote','--exit-code',url,'refs/heads/'+branch)
    return line.split()[0]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--apply',nargs='+',type=int,metavar='PR')
    group.add_argument('--apply-all',action='store_true')
    args=parser.parse_args()
    manifest=json.loads(Path(__file__).with_name('rebase-manifest.json').read_text())
    ready={r['number']:r for r in manifest['results'] if r.get('ready_to_publish')}
    selected=set(ready) if args.apply_all else set(args.apply or [])
    if selected-set(ready):
        parser.error('Not a ready, reviewed candidate: '+str(sorted(selected-set(ready))))
    base=manifest['base']
    upstream_url='https://github.com/'+UPSTREAM+'.git'
    own_url='https://github.com/'+OWN+'.git'
    observed_base=remote_head(upstream_url,'main')
    if observed_base!=base:
        raise RuntimeError('Main changed from '+base+' to '+observed_base+'; refresh the rebases before publishing.')
    print('Reviewed main:',base)
    print('Validation: Git replay and structural checks; no Lean builds.')
    failed=[]
    with tempfile.TemporaryDirectory(prefix='rh-publish-rebases-') as temporary:
        repo=Path(temporary)/'repo.git'
        run('git','init','--bare','--quiet',str(repo))
        if selected:
            git(repo,'fetch','--no-tags',upstream_url,'refs/heads/main:refs/remotes/upstream/main')
        for number,candidate in sorted(ready.items()):
            if selected and number not in selected:
                continue
            try:
                live=json.loads(run('gh','api','repos/'+UPSTREAM+'/pulls/'+str(number)))
                expected=candidate['original_head'];target=candidate['rebased_head']
                if live['state']!='open':
                    print('#'+str(number)+': already closed; skipped');continue
                head=live['head']
                if head['repo']['full_name']!=candidate['original_repo'] or head['ref']!=candidate['original_branch']:
                    raise RuntimeError('PR source repository or branch changed')
                if head['sha']==target:
                    print('#'+str(number)+': already applied');continue
                if head['sha']!=expected:
                    raise RuntimeError('PR advanced to '+head['sha']+'; expected '+expected)
                if candidate['original_repo']!=UPSTREAM and not live['maintainer_can_modify']:
                    raise RuntimeError('Author has disabled maintainer edits')
                destination='https://github.com/'+candidate['original_repo']+'.git'
                branch=candidate['original_branch']
                print('#'+str(number)+': '+destination+' '+branch+' '+expected[:12]+' -> '+target[:12])
                if number not in selected:
                    continue
                if remote_head(upstream_url,'main')!=base:
                    raise RuntimeError('Main advanced during publication; stopping this candidate')
                prep=candidate['prepared_branch']
                git(repo,'fetch','--no-tags',own_url,'refs/heads/'+prep+':refs/remotes/prepared/'+str(number))
                if git(repo,'rev-parse','refs/remotes/prepared/'+str(number))!=target:
                    raise RuntimeError('Preparation branch changed')
                git(repo,'merge-base','--is-ancestor',base,target)
                if remote_head(destination,branch)!=expected:
                    raise RuntimeError('Source branch advanced immediately before push')
                backup='maintenance/before-rebase-pr-'+str(number)+'-'+expected[:10]
                git(repo,'fetch','--no-tags',destination,'refs/heads/'+branch+':refs/remotes/original/'+str(number))
                if git(repo,'rev-parse','refs/remotes/original/'+str(number))!=expected:
                    raise RuntimeError('Source branch advanced while creating backup')
                existing=git(repo,'ls-remote',own_url,'refs/heads/'+backup).split()
                if existing and existing[0]!=expected:
                    raise RuntimeError('Existing backup has an unexpected head')
                if not existing:
                    git(repo,'push',own_url,'--force-with-lease=refs/heads/'+backup+':',expected+':refs/heads/'+backup)
                git(repo,'push',destination,'--force-with-lease=refs/heads/'+branch+':'+expected,target+':refs/heads/'+branch)
                print('#'+str(number)+': published')
            except (RuntimeError,subprocess.CalledProcessError) as error:
                failed.append(number)
                print('#'+str(number)+': '+str(error),file=sys.stderr)
    if not selected:
        print('Read-only preview. Use --apply PR... or --apply-all to publish the listed commits.')
    return bool(failed)

if __name__=='__main__':
    try:
        sys.exit(main())
    except (RuntimeError,subprocess.CalledProcessError) as error:
        sys.exit(str(error))
