#!/usr/bin/env python3
"""Assemble the public maintenance manifest from immutable per-run reports."""
import collections
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE='1334509aa7f1548cac4f2e68e9f631ed5ae4d7e7'
UPSTREAM='https://github.com/leanprover-community/riemann-hypothesis'
OWN='https://github.com/Deicyde/riemann-hypothesis-contrib'
ORDER=['owned','small-one','small-two','performance','structural','reviewed','remaining',
       'remaining2','88-recovered','imports','pruning-replay','imports-9','imports-10',
       'remaining3','remaining4','restack','75-repair','final-imports','imports-4','54-final']

def main():
    catalog={}
    for name in ORDER:
        path=HERE/('report-'+name+'.json')
        if not path.exists(): continue
        report=json.loads(path.read_text())
        for original in report['results']:
            row=dict(original)
            row['base']=report['base'];row['report_run']=report['run']
            row['report_url']=OWN+'/blob/maintenance/rebase-report-'+report['base'][:10]+'-'+report['run']+'/verification/rebase-maintenance/'+report['base'][:10]+'/summary.json'
            catalog[row['number']]=row
    for n,row in catalog.items():
        row['ready_to_publish']=bool(row['status']=='rebased' and row['base']==BASE and row.get('diff_check') and
                                     row.get('imports',{}).get('missing_count')==0 and row.get('imports',{}).get('acyclic',True) and
                                     all(row.get('protected_files',{}).values()))
        row['note']='Prepared on Jack’s fork; original branch publication requires maintainer credentials.' if row['ready_to_publish'] else ''
        if n in (55,58,61,67):
            row['note']='Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36.'
        elif n in (44,63):
            row['note']='Structural proof/module transformation requires regeneration against Lean 4.36.'
        elif n==4:
            row['note']='6,482 conflicts remain, including imports of modules removed by the port. Regenerate import minimization for current main; #98 is the active Lean 4.36 import-minimization effort.'
        elif n==54 and row['status']!='rebased':
            row['note']='Proof golf is being replayed with individually reviewed Lean 4.36 adaptations.'
        elif n==75:
            row['note']='Retained DzDifferentiableOn and NormCpowSubLePoint because current main still imports them; import existence and cycle checks pass.'
        elif n==98:
            row['note']='Retained main’s AutomorphicFormsFiniteGL proof route and imports in that one file; other import minimization/privacy changes are preserved.'
    applied=json.loads((HERE/'applied-final-own.json').read_text())
    for action in applied:
        if action['result'].get('structuredContent',{}).get('success'):
            row=catalog[action['n']];row['status']='applied';row['ready_to_publish']=False
            row['published_head']=action['new'];row['note']='Published to the original PR branch with a checked head and an original-head backup.'
    external=json.loads((HERE/'external-updates.json').read_text())
    for key,update in external.items():
        row=catalog[int(key)];row.update(update);row['ready_to_publish']=False
        if update['status']=='updated-by-contributor':
            row['report_url']=UPSTREAM+'/compare/'+BASE+'...'+update['head']
            for field in ['conflicts','conflict_count','rebase_head','rebased_head','prepared_branch']:
                row.pop(field,None)
        row['note']='Contributor incorporated the latest main during this maintenance pass; left their newer work in place.' if update['status']=='updated-by-contributor' else 'PR closed during the maintenance pass; no branch update is necessary.'
    catalog[85]['note']='Historical formatter demonstration against formatter-pilot-base, explicitly not for merging. Left its before/after comparison intact.'
    rows=[catalog[n] for n in sorted(catalog)]
    counts=dict(collections.Counter(r['status'] for r in rows))
    compact=[]
    keys=['number','title','status','base','original_head','original_repo','original_branch',
          'initial_head','rebased_head','prepared_branch','ready_to_publish','published_head','head','base_incorporated',
          'changes','imports','protected_files','diff_check','restack_source_unchanged',
          'author_and_message_metadata_unchanged','automatic_resolution_count','conflict_count',
          'rebase_head','note','report_url']
    for row in rows:
        compact.append({k:row[k] for k in keys if k in row})
    manifest={'base':BASE,'scope':'The 36 PRs open at the initial snapshot on 2026-11-22.',
              'validation':'Git replay, whitespace, project import existence and protected-file checks. Import cycles checked where recorded. No Lean builds.',
              'counts':counts,'results':compact}
    (HERE/'rebase-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    lines=['# Open PR rebase maintenance — 2026-11-22','',
           'Main: [`'+BASE[:12]+'`]('+UPSTREAM+'/commit/'+BASE+'). The pass covers all 36 PRs open at the initial snapshot; newer PRs were left to their current workers. Previously requested #66 has merged.','',
           'This is a branch maintenance result, not a successful Lean build. Conflicted proof edits were adapted individually; the current Lean 4.36 proof route, toolchain and dependency pins were retained. Real Git rebases preserve commit authors and messages, including coauthor trailers. The final documentation-only restack additionally checks exact source/configuration identity and exact author/message metadata.','',
           'GitHub allowed publication to Jack’s fork but rejected updates to contributor/upstream branches with “Resource not accessible by integration”. Prepared heads below remain available on the fork. No pull request was merged or closed by this maintenance pass.','',
           '| PR | Result | Prepared or published head | Detail |','|---|---|---|---|']
    for r in compact:
        sha=r.get('published_head') or (r.get('head') if r['status']=='updated-by-contributor' else r.get('rebased_head') if r.get('ready_to_publish') else None)
        link='[`'+sha[:10]+'`]('+OWN+'/commit/'+sha+')' if sha and r['status']!='updated-by-contributor' else ('[`'+sha[:10]+'`]('+UPSTREAM+'/commit/'+sha+')' if sha else '—')
        lines.append('| [#'+str(r['number'])+']('+UPSTREAM+'/pull/'+str(r['number'])+') | '+r['status']+' | '+link+' | '+r['note']+' |')
    lines += ['', '## Publishing prepared heads','',
              'Use an account that can update each original PR branch. Save this directory’s `push_prepared_rebases.py` and `rebase-manifest.json` together, then run:', '',
              '```sh','gh auth setup-git','python3 push_prepared_rebases.py          # read-only preview','python3 push_prepared_rebases.py --apply 9 10','```','',
              '`--apply-all` publishes every ready entry. The script refuses changed main or PR heads, verifies the prepared ref, creates original-head backups and uses exact force-with-lease updates. It skips PRs that have closed. It never merges or closes a PR. Lean build validation remains necessary.','',
              'Each manifest row links its immutable per-run report, with conflict stages, resolutions and checks. The preparation and checkpoint branches preserve reviewable Git histories.']
    (HERE/'README.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps(counts));print('Ready to publish:',[r['number'] for r in compact if r['ready_to_publish']])

if __name__=='__main__': main()
