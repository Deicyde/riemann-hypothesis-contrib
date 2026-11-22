"""Add the completed comparator replay and normalize all remaining feature histories."""
import json
from pathlib import Path
import rebase_open_prs as worker
import restack_trees

report=json.loads((worker.OUT/'summary.json').read_text())
row=next(r for r in report['results'] if r['number']==88)
if row['status']!='rebased' or not row['diff_check'] or row['imports']['missing_count'] or not row['imports']['acyclic'] or not all(row['protected_files'].values()):
    raise RuntimeError('Comparator rebase still needs attention: '+json.dumps(row))
row['base']=report['base']
cfg=json.loads((worker.HERE/'prepared.json').read_text());cfg['results'].append(row)
(worker.HERE/'prepared.json').write_text(json.dumps(cfg,indent=2))
worker.OUT=worker.ROOT/'final-results'
restack_trees.main()
