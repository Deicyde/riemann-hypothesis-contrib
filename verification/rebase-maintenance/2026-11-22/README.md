# Open PR rebase maintenance — 2026-11-22

Reviewed proof base: [`611ce0b63013`](https://github.com/leanprover-community/riemann-hypothesis/commit/611ce0b6301315e35f9642dfa1817e19d6dba2f1). The pass covers all 36 PRs open at the initial snapshot; newer PRs were left to their current workers. Previously requested #66 has merged.

Main subsequently advanced through README-only edits. The publishing script follows these edits while checking that every other file and all retained author/message metadata remain identical. Any other main change stops publication.

Validation covers Git replay and structural checks; Lean builds remain required. Conflicted proof edits were adapted individually, retaining needed Lean 4.36 port fixes, toolchain and dependency pins. Edits to declarations already pruned from main were dropped. Retained original commits preserve their authors and full messages, including coauthor trailers. The final documentation-only restack additionally checks exact source/configuration identity and exact author/message metadata.

GitHub allowed publication to Jack’s fork but rejected updates to contributor/upstream branches with “Resource not accessible by integration”. Prepared heads below remain available on the fork. No pull request was merged or closed by this maintenance pass.

Upstream merged #115 during this pass. Empty rebases confirm that #71, #74, #76, #80, #81, #82, #90 and #92 are now fully incorporated in main. Their branches were left intact. #91 was subsequently closed by another actor; its four remaining cleanup commits and its pre-update heads are preserved in the preparation and backup branches.

Seven older transformations require regeneration against Lean 4.36: #4 (import minimization), #55/#58/#61/#67 (unused-declaration pruning), #44 (proof overhaul) and #63 (module consolidation). The last replay found 6,482, 4,029, 103,997 and 142,439 conflicts respectively; those reports precede #115. Retained proofs and imports overlap their deletion/transformation ranges.

| PR | Result | Prepared or published head | Detail |
|---|---|---|---|
| [#4](https://github.com/leanprover-community/riemann-hypothesis/pull/4) | conflict | — | 6,482 conflicts remain, including imports of modules removed by the port. Regenerate import minimization for current main; #98 is the active Lean 4.36 import-minimization effort. |
| [#9](https://github.com/leanprover-community/riemann-hypothesis/pull/9) | rebased | [`82759a791c`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/82759a791c4686556ed698c9900556ff3df3a923) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#10](https://github.com/leanprover-community/riemann-hypothesis/pull/10) | rebased | [`936b5f8de5`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/936b5f8de5bc9067ddc60d2aeaf148a6c930e09b) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#33](https://github.com/leanprover-community/riemann-hypothesis/pull/33) | rebased | [`3d3888b89f`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/3d3888b89f1d22169349b531b070f69548291256) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#44](https://github.com/leanprover-community/riemann-hypothesis/pull/44) | conflict | — | Structural proof/module transformation requires regeneration against Lean 4.36. |
| [#54](https://github.com/leanprover-community/riemann-hypothesis/pull/54) | rebased | [`f1e5d64492`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/f1e5d644924dfd1b668a00f68fbfc091957166aa) | Retained original authors and messages; kept main’s shared Euler-factor proof and necessary local proofs where old shared replacements were pruned. Import, cycle and whitespace checks pass. |
| [#55](https://github.com/leanprover-community/riemann-hypothesis/pull/55) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#58](https://github.com/leanprover-community/riemann-hypothesis/pull/58) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#61](https://github.com/leanprover-community/riemann-hypothesis/pull/61) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#62](https://github.com/leanprover-community/riemann-hypothesis/pull/62) | rebased | [`ecd7701a2b`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/ecd7701a2b3a9c72b416734b48ddd45111b4255a) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#63](https://github.com/leanprover-community/riemann-hypothesis/pull/63) | conflict | — | Structural proof/module transformation requires regeneration against Lean 4.36. |
| [#67](https://github.com/leanprover-community/riemann-hypothesis/pull/67) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#69](https://github.com/leanprover-community/riemann-hypothesis/pull/69) | rebased | [`5b8c109479`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/5b8c109479b78a576443e7baaa5e62ef99c67212) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#71](https://github.com/leanprover-community/riemann-hypothesis/pull/71) | already-in-main | — | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#74](https://github.com/leanprover-community/riemann-hypothesis/pull/74) | already-in-main | [`f31ab64353`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/f31ab6435355e24214ff0e86e24a59394322892e) | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#75](https://github.com/leanprover-community/riemann-hypothesis/pull/75) | rebased | [`d20f4e76b5`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/d20f4e76b58a3a7edbda5c88321572b5c5d1d888) | Retained DzDifferentiableOn and NormCpowSubLePoint because current main still imports them; import existence and cycle checks pass. |
| [#76](https://github.com/leanprover-community/riemann-hypothesis/pull/76) | already-in-main | — | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#78](https://github.com/leanprover-community/riemann-hypothesis/pull/78) | rebased | [`e372233646`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/e372233646002492115f22ca03cf2ec8efdcf332) | Preserved the current checking instructions and added the bibliography link. |
| [#79](https://github.com/leanprover-community/riemann-hypothesis/pull/79) | rebased | [`fb9636a200`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/fb9636a200c6a1ddc4b9670e888ce0d885b66d1a) | Retained eight new main proofs and their instance budgets where global heartbeat removal overlapped them. |
| [#80](https://github.com/leanprover-community/riemann-hypothesis/pull/80) | already-in-main | [`59057b1de2`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/59057b1de27671658ab87022f0899613f91ae3b4) | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#81](https://github.com/leanprover-community/riemann-hypothesis/pull/81) | already-in-main | [`6f3d67880d`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/6f3d67880dcd8dde6b76f6ec6d8a0b7fd2114145) | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#82](https://github.com/leanprover-community/riemann-hypothesis/pull/82) | already-in-main | — | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#83](https://github.com/leanprover-community/riemann-hypothesis/pull/83) | rebased | [`0c57d7b03d`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/0c57d7b03dc98bcc4a0186e953de7b7e504d8fa7) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#84](https://github.com/leanprover-community/riemann-hypothesis/pull/84) | closed | — | PR closed during the maintenance pass; no branch update is necessary. |
| [#85](https://github.com/leanprover-community/riemann-hypothesis/pull/85) | excluded-nonmerging-formatter-pilot | — | Historical formatter demonstration against formatter-pilot-base, explicitly not for merging. Left its before/after comparison intact. |
| [#86](https://github.com/leanprover-community/riemann-hypothesis/pull/86) | rebased | [`f5ef245174`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/f5ef2451745e25458d1bb0e8314a163020a0bc28) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#87](https://github.com/leanprover-community/riemann-hypothesis/pull/87) | rebased | [`36ab4482cd`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/36ab4482cd80ba7bf99f3839af5f4c94eb86f9f2) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#88](https://github.com/leanprover-community/riemann-hypothesis/pull/88) | rebased | [`fdf6baa027`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/fdf6baa027671ba5a51c0776043573156dabbafa) | Challenge.lean is moved byte-for-byte to comparator/Challenge.lean, as intended by this PR. |
| [#90](https://github.com/leanprover-community/riemann-hypothesis/pull/90) | already-in-main | — | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#91](https://github.com/leanprover-community/riemann-hypothesis/pull/91) | closed | [`3dbbac15c3`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/3dbbac15c31dca8edfa0f00039979b59d3ce05ca) | Closed by another actor during this pass. Four unmerged cleanup commits remain available at the linked preserved head. |
| [#92](https://github.com/leanprover-community/riemann-hypothesis/pull/92) | already-in-main | — | An empty rebase confirms that #115 already incorporated all remaining changes. No branch rewrite is necessary. |
| [#94](https://github.com/leanprover-community/riemann-hypothesis/pull/94) | rebased | [`8c0cb138b5`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/8c0cb138b5f8ea8fd8834369995e2d2d56d4db66) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#95](https://github.com/leanprover-community/riemann-hypothesis/pull/95) | rebased | [`ee2509a61e`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/ee2509a61e7984414ea8a976e7bb5b64506a0533) | The entire proof source tree matches the contributor’s latest Lean 4.36 integration exactly; current main’s documentation and CI changes are included. |
| [#97](https://github.com/leanprover-community/riemann-hypothesis/pull/97) | applied | [`885e54de66`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/885e54de662d0df57587901f55fded759f717fc9) | Published to the original PR branch with a checked head and an original-head backup. Retained the 49 new main files where the older formatter patch overlapped proof changes. |
| [#98](https://github.com/leanprover-community/riemann-hypothesis/pull/98) | rebased | [`0b9df676da`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/0b9df676dae5329f7aca9055d5440560df416de5) | Retained main’s AutomorphicFormsFiniteGL proof route and the new main proofs in overlapping files; other import minimization/privacy changes are preserved. |
| [#104](https://github.com/leanprover-community/riemann-hypothesis/pull/104) | rebased | [`08f4842adb`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/08f4842adbee1ce8f3f7cb2089f3915c980c2d38) | Retained eight new main proofs and their instance budgets where global heartbeat removal overlapped them. |

## Publishing prepared heads

Use an account that can update each original PR branch. Save this directory’s `push_prepared_rebases.py` and `rebase-manifest.json` together, then run:

```sh
gh auth setup-git
python3 push_prepared_rebases.py          # read-only preview
python3 push_prepared_rebases.py --apply 9 10
```

`--apply-all` publishes every ready entry. The script stops if main changes outside README or a PR head changes. README-only main updates are replayed with exact file and author/message checks. It verifies prepared refs, creates original-head backups and uses exact force-with-lease updates. It skips PRs that have closed. It never merges or closes a PR. Lean build validation remains necessary.

Each manifest row links its immutable per-run report, with conflict stages, resolutions and checks. The preparation and checkpoint branches preserve reviewable Git histories. `final-verification.json` records the additional author, file-identity and concurrent-update audits.
