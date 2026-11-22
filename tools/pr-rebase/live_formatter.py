"""Follow current README-only main changes using a filtered object fetch."""
import base64,json,os
from pathlib import Path
from push_prepared_rebases import git,run,restack_readme

token=base64.b64encode(('x-access-token:'+os.environ['GH_TOKEN']).encode()).decode()
os.environ.update(GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='http.https://github.com/.extraheader',GIT_CONFIG_VALUE_0='AUTHORIZATION: basic '+token,GIT_TERMINAL_PROMPT='0')
repo=Path(os.environ['RUNNER_TEMP'])/'rh-live-formatter.git'
run('git','init','--bare','--quiet',str(repo))
for name,url in [('origin','https://github.com/Deicyde/riemann-hypothesis-contrib.git'),('upstream','https://github.com/leanprover-community/riemann-hypothesis.git')]:
    git(repo,'remote','add',name,url)
    git(repo,'config','remote.'+name+'.promisor','true')
    git(repo,'config','remote.'+name+'.partialclonefilter','blob:none')
git(repo,'config','core.repositoryformatversion','1')
git(repo,'config','extensions.partialclone','upstream')
git(repo,'fetch','--no-tags','--filter=blob:none','origin','refs/heads/format/port-4.36-lean-formatter:refs/remotes/origin/formatter')
git(repo,'fetch','--no-tags','--filter=blob:none','upstream','refs/heads/main:refs/remotes/upstream/main')
old=git(repo,'rev-parse','refs/remotes/origin/formatter')
if old!='885e54de662d0df57587901f55fded759f717fc9':raise RuntimeError('Formatter branch advanced')
base=git(repo,'rev-parse','refs/remotes/upstream/main')
new=restack_readme(repo,'611ce0b6301315e35f9642dfa1817e19d6dba2f1',old,base)
branch='maintenance/readme-live-97-'+os.environ['GITHUB_RUN_ID']
git(repo,'push','origin',new+':refs/heads/'+branch)
print(json.dumps({'base':base,'old':old,'head':new,'branch':branch}),flush=True)
