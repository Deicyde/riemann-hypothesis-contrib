#!/usr/bin/env python3
"""Assemble the public maintenance manifest from immutable per-run reports."""
import collections
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE='611ce0b6301315e35f9642dfa1817e19d6dba2f1'
UPSTREAM='https://github.com/leanprover-community/riemann-hypothesis'
OWN='https://github.com/Deicyde/riemann-hypothesis-contrib'
ORDER=['owned','small-one','small-two','performance','structural','reviewed','remaining',
       'remaining2','88-recovered','imports','pruning-replay','imports-9','imports-10',
       'remaining3','remaining4','restack','75-repair','final-imports','imports-4','54-final','restack-8f','refreshed-three','final-main','54-revalidated','after115-proofs-a','after115-proofs-b','after115-owned','after115-wide','latest-proof-repairs','latest-wide-repairs','latest-docs','final-current','final-comparator','live-formatter']

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
        if row['status']=='empty-after-rebase':
            row['status']='already-in-main';row['ready_to_publish']=False
            row['note']='An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary.'
        if n in (55,58,61,67):
            row['note']='Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36.'
        elif n in (44,63):
            row['note']='Structural proof/module transformation requires regeneration against Lean 4.36.'
        elif n==4:
            row['note']='6,482 conflicts remain, including imports of modules removed by the port. Regenerate import minimization for current main; #98 is the active Lean 4.36 import-minimization effort.'
        elif n==54 and row['status']!='rebased':
            row['note']='Proof golf is being replayed with individually reviewed Lean 4.36 adaptations.'
        elif n==54 and row['status']=='rebased':
            row['note']='Retained original authors and messages; kept main’s shared Euler-factor proof and necessary local proofs where old shared replacements were pruned. Import, cycle and whitespace checks pass.'
        elif n==75:
            row['note']='Retained DzDifferentiableOn and NormCpowSubLePoint because current main still imports them; import existence and cycle checks pass.'
        elif n==98:
            row['note']='Retained main’s AutomorphicFormsFiniteGL proof route and the new main proofs in overlapping files; other import minimization/privacy changes are preserved.'
        elif n in (79,104):
            row['note']='Retained eight new main proofs and their instance budgets where global heartbeat removal overlapped them.'
        elif n==95 and row['status']=='rebased':
            row['note']='The entire proof source tree matches the contributor’s latest Lean 4.36 integration exactly; current main’s documentation and CI changes are included.'
        elif n==78 and row['status']=='rebased':
            row['note']='Preserved the current checking instructions and added the bibliography link.'
        elif n==88 and row['status']=='rebased':
            row['note']='Challenge.lean is moved byte-for-byte to comparator/Challenge.lean, as intended by this PR.'
    applied=json.loads((HERE/'applied-latest-owned.json').read_text())
    for action in applied:
        if action['result'].get('structuredContent',{}).get('success'):
            row=catalog[action['n']];row['status']='applied';row['ready_to_publish']=False
            row['published_head']=action['new'];row['publication_previous_head']=action['old'];row['backup_branch']=action['backup'];row['note']='Published to the original PR branch with a checked head and an original-head backup.'
            if action['n']==91:row['note']+=' Four unmerged cleanup commits remain after #115.'
            if action['n']==97:row['note']+=' Retained the 49 new main files where the older formatter patch overlapped proof changes.'
    external=json.loads((HERE/'external-updates.json').read_text())
    for key,update in external.items():
        row=catalog[int(key)];row.update(update);row['ready_to_publish']=False
        if update['status']=='updated-by-contributor':
            row['report_url']=UPSTREAM+'/compare/'+BASE+'...'+update['head']
            for field in ['conflicts','conflict_count','rebase_head','rebased_head','prepared_branch']:
                row.pop(field,None)
        row['note']='Contributor incorporated the latest main during this maintenance pass; left their newer work in place.' if update['status']=='updated-by-contributor' else 'PR closed during the maintenance pass; no branch update is necessary.'
        if int(key)==91 and update['status']=='closed':row['note']='Closed by another actor during this pass. Four unmerged cleanup commits remain available at the linked preserved head.'
    catalog[85]['note']='Historical formatter demonstration against formatter-pilot-base, explicitly not for merging. Left its before/after comparison intact.'
    rows=[catalog[n] for n in sorted(catalog)]
    counts=dict(collections.Counter(r['status'] for r in rows))
    compact=[]
    keys=['number','title','status','base','original_head','original_repo','original_branch',
          'initial_head','publication_previous_head','backup_branch','rebased_head','prepared_branch','ready_to_publish','published_head','head','base_incorporated',
          'changes','imports','protected_files','diff_check','restack_source_unchanged',
          'author_and_message_metadata_unchanged','automatic_resolution_count','conflict_count',
          'rebase_head','retained_commit_metadata_verified','retained_commit_count','challenge_relocated_unchanged',
          'contributor_latest_source_preserved','contributor_src_tree','note','report_url']
    for row in rows:
        compact.append({k:row[k] for k in keys if k in row})
    manifest={'base':BASE,'scope':'The 36 PRs open at the initial snapshot on 2026-11-22.',
              'validation':'Git replay, whitespace, project import existence and protected-file checks. Import cycles checked where recorded. No Lean builds.',
              'counts':counts,'results':compact}
    (HERE/'rebase-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    lines=['# Open PR rebase maintenance — 2026-11-22','',
           'Reviewed proof base: [`'+BASE[:12]+'`]('+UPSTREAM+'/commit/'+BASE+'). The pass covers all 36 PRs open at the initial snapshot; newer PRs were left to their current workers. Previously requested #66 has merged.','',
           'Main subsequently advanced through README-only edits. The publishing script follows these edits while checking that every other file and all retained author/message metadata remain identical. Any other main change stops publication.','',
           'Validation covers Git replay and structural checks; Lean builds remain required. Conflicted proof edits were adapted individually, retaining needed Lean 4.36 port fixes, toolchain and dependency pins. Edits to declarations already pruned from main were dropped. Retained original commits preserve their authors and full messages, including coauthor trailers. The final documentation-only restack additionally checks exact source/configuration identity and exact author/message metadata.','',
           'GitHub allowed publication to Jack’s fork but rejected updates to contributor/upstream branches with “Resource not accessible by integration”. Prepared heads below remain available on the fork. No pull request was merged or closed by this maintenance pass.','',
           'Upstream merged #115 during this pass. Empty rebases confirm that #71, #74, #76, #80, #81, #82, #90 and #92 are now fully incorporated in main. Their branches were left intact. #91 was subsequently closed by another actor; its four remaining cleanup commits and its pre-update heads are preserved in the preparation and backup branches.','',
           'Seven older transformations require regeneration against Lean 4.36: #4 (import minimization), #55/#58/#61/#67 (unused-declaration pruning), #44 (proof overhaul) and #63 (module consolidation). The last replay found 6,482, 4,029, 103,997 and 142,439 conflicts respectively; those reports precede #115. Retained proofs and imports overlap their deletion/transformation ranges.','',
           '| PR | Result | Prepared or published head | Detail |','|---|---|---|---|']
    for r in compact:
        sha=r.get('published_head') or (r.get('head') if r['status']=='updated-by-contributor' else r.get('rebased_head') if r.get('ready_to_publish') else None)
        link='[`'+sha[:10]+'`]('+OWN+'/commit/'+sha+')' if sha and r['status']!='updated-by-contributor' else ('[`'+sha[:10]+'`]('+UPSTREAM+'/commit/'+sha+')' if sha else '—')
        lines.append('| [#'+str(r['number'])+']('+UPSTREAM+'/pull/'+str(r['number'])+') | '+r['status']+' | '+link+' | '+r['note']+' |')
    lines += ['', '## Publishing prepared heads','',
              'Use an account that can update each original PR branch. Save this directory’s `push_prepared_rebases.py` and `rebase-manifest.json` together, then run:', '',
              '```sh','gh auth setup-git','python3 push_prepared_rebases.py          # read-only preview','python3 push_prepared_rebases.py --apply 9 10','```','',
              '`--apply-all` publishes every ready entry. The script stops if main changes outside README or a PR head changes. README-only main updates are replayed with exact file and author/message checks. It verifies prepared refs, creates original-head backups and uses exact force-with-lease updates. It skips PRs that have closed. It never merges or closes a PR. Lean build validation remains necessary.','',
              'Each manifest row links its immutable per-run report, with conflict stages, resolutions and checks. The preparation and checkpoint branches preserve reviewable Git histories. `final-verification.json` records the additional author, file-identity and concurrent-update audits.']
    (HERE/'README.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps(counts));print('Ready to publish:',[r['number'] for r in compact if r['ready_to_publish']])

if __name__=='__main__': main()
