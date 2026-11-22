# Open PR rebase maintenance — 2026-11-22

Main: [`1334509aa7f1`](https://github.com/leanprover-community/riemann-hypothesis/commit/1334509aa7f1548cac4f2e68e9f631ed5ae4d7e7). The pass covers all 36 PRs open at the initial snapshot; newer PRs were left to their current workers. Previously requested #66 has merged.

This is a branch maintenance result, not a successful Lean build. Conflicted proof edits were adapted individually; the current Lean 4.36 proof route, toolchain and dependency pins were retained. Real Git rebases preserve commit authors and messages, including coauthor trailers. The final documentation-only restack additionally checks exact source/configuration identity and exact author/message metadata.

GitHub allowed publication to Jack’s fork but rejected updates to contributor/upstream branches with “Resource not accessible by integration”. Prepared heads below remain available on the fork. No pull request was merged or closed by this maintenance pass.

| PR | Result | Prepared or published head | Detail |
|---|---|---|---|
| [#4](https://github.com/leanprover-community/riemann-hypothesis/pull/4) | conflict | — | 6,482 conflicts remain, including imports of modules removed by the port. Regenerate import minimization for current main; #98 is the active Lean 4.36 import-minimization effort. |
| [#9](https://github.com/leanprover-community/riemann-hypothesis/pull/9) | rebased | [`1139b7bca2`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/1139b7bca226ea52b2ff781863cd1cd5e9fefe5f) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#10](https://github.com/leanprover-community/riemann-hypothesis/pull/10) | rebased | [`3f21a3ec46`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/3f21a3ec46974c5d37c9bfcb5b7ae0d0214e98ad) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#33](https://github.com/leanprover-community/riemann-hypothesis/pull/33) | rebased | [`91036e7d33`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/91036e7d33dfcf07a38bd08c268e4be516257e6c) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#44](https://github.com/leanprover-community/riemann-hypothesis/pull/44) | conflict | — | Structural proof/module transformation requires regeneration against Lean 4.36. |
| [#54](https://github.com/leanprover-community/riemann-hypothesis/pull/54) | conflict | — | Proof golf is being replayed with individually reviewed Lean 4.36 adaptations. |
| [#55](https://github.com/leanprover-community/riemann-hypothesis/pull/55) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#58](https://github.com/leanprover-community/riemann-hypothesis/pull/58) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#61](https://github.com/leanprover-community/riemann-hypothesis/pull/61) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#62](https://github.com/leanprover-community/riemann-hypothesis/pull/62) | rebased | [`d637a71699`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/d637a716990574f2eefd9ef1fa1a6b24f646f40d) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#63](https://github.com/leanprover-community/riemann-hypothesis/pull/63) | conflict | — | Structural proof/module transformation requires regeneration against Lean 4.36. |
| [#67](https://github.com/leanprover-community/riemann-hypothesis/pull/67) | conflict | — | Shared pruning commit still has 4,029 conflicts; regenerate the unused-declaration analysis against Lean 4.36. |
| [#69](https://github.com/leanprover-community/riemann-hypothesis/pull/69) | rebased | [`403722220d`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/403722220d881dfcf630e2db30feeb57c0f8a532) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#71](https://github.com/leanprover-community/riemann-hypothesis/pull/71) | rebased | [`14bf9e628a`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/14bf9e628a20fa9f1adfd990c9e8b80fa898b960) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#74](https://github.com/leanprover-community/riemann-hypothesis/pull/74) | applied | [`74efb4e7db`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/74efb4e7dbcc9fd9368c11e126661ff9bf273be8) | Published to the original PR branch with a checked head and an original-head backup. |
| [#75](https://github.com/leanprover-community/riemann-hypothesis/pull/75) | rebased | [`d3ecd8eca4`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/d3ecd8eca4030408a832836bae657401ed86ce05) | Retained DzDifferentiableOn and NormCpowSubLePoint because current main still imports them; import existence and cycle checks pass. |
| [#76](https://github.com/leanprover-community/riemann-hypothesis/pull/76) | rebased | [`45350239f7`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/45350239f76cde18b8c8e7d3c5c11ff98c8b5689) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#78](https://github.com/leanprover-community/riemann-hypothesis/pull/78) | updated-by-contributor | [`25f9d796ce`](https://github.com/leanprover-community/riemann-hypothesis/commit/25f9d796ce67aa7c80a937df1074216005e21b06) | Contributor incorporated the latest main during this maintenance pass; left their newer work in place. |
| [#79](https://github.com/leanprover-community/riemann-hypothesis/pull/79) | rebased | [`c83cd7663a`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/c83cd7663ab4e6ec90959571146742f01d2599b8) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#80](https://github.com/leanprover-community/riemann-hypothesis/pull/80) | applied | [`2bab9a1e9b`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/2bab9a1e9bc8ee243c8c239de2174d9e9ed21d13) | Published to the original PR branch with a checked head and an original-head backup. |
| [#81](https://github.com/leanprover-community/riemann-hypothesis/pull/81) | applied | [`c35f536f32`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/c35f536f327025742b2d1f0851d4460772bf4e5b) | Published to the original PR branch with a checked head and an original-head backup. |
| [#82](https://github.com/leanprover-community/riemann-hypothesis/pull/82) | rebased | [`80587aa885`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/80587aa885f931d17f297bc8cfa825422fc0df97) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#83](https://github.com/leanprover-community/riemann-hypothesis/pull/83) | rebased | [`a48e44cca8`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/a48e44cca837dd149092a1c0bba563200a40e28f) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#84](https://github.com/leanprover-community/riemann-hypothesis/pull/84) | closed | — | PR closed during the maintenance pass; no branch update is necessary. |
| [#85](https://github.com/leanprover-community/riemann-hypothesis/pull/85) | excluded-nonmerging-formatter-pilot | — | Historical formatter demonstration against formatter-pilot-base, explicitly not for merging. Left its before/after comparison intact. |
| [#86](https://github.com/leanprover-community/riemann-hypothesis/pull/86) | rebased | [`40758c7d23`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/40758c7d23084783aebf72d7f44d52cf824ef9c8) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#87](https://github.com/leanprover-community/riemann-hypothesis/pull/87) | rebased | [`5c1ddf85d2`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/5c1ddf85d2f237c400404eed7d227468891c8630) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#88](https://github.com/leanprover-community/riemann-hypothesis/pull/88) | updated-by-contributor | [`1313f85cc0`](https://github.com/leanprover-community/riemann-hypothesis/commit/1313f85cc02255a652a7ce97477f3aa20731078d) | Contributor incorporated the latest main during this maintenance pass; left their newer work in place. |
| [#90](https://github.com/leanprover-community/riemann-hypothesis/pull/90) | rebased | [`9a0de63edc`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/9a0de63edc46583ab56948d38e2a8d609c2d6450) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#91](https://github.com/leanprover-community/riemann-hypothesis/pull/91) | applied | [`039a209ecb`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/039a209ecb5ccea56449f7ae63289f3b78e53246) | Published to the original PR branch with a checked head and an original-head backup. |
| [#92](https://github.com/leanprover-community/riemann-hypothesis/pull/92) | rebased | [`4df9079596`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/4df9079596c68c31260c1482147e8c9b97f82510) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#94](https://github.com/leanprover-community/riemann-hypothesis/pull/94) | rebased | [`90caca8709`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/90caca8709fa25db5da42cd4d91e9b8746f21388) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#95](https://github.com/leanprover-community/riemann-hypothesis/pull/95) | rebased | [`ecae7b331f`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/ecae7b331fb6c02cb5dc383fd8dee895c42e9c6f) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |
| [#97](https://github.com/leanprover-community/riemann-hypothesis/pull/97) | applied | [`79660a5763`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/79660a576307085788485c3cb7bc5c6464e8e14d) | Published to the original PR branch with a checked head and an original-head backup. |
| [#98](https://github.com/leanprover-community/riemann-hypothesis/pull/98) | rebased | [`1296236052`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/12962360526d0047b78dd63d12e5c4debfdcce65) | Retained main’s AutomorphicFormsFiniteGL proof route and imports in that one file; other import minimization/privacy changes are preserved. |
| [#104](https://github.com/leanprover-community/riemann-hypothesis/pull/104) | rebased | [`27425664ec`](https://github.com/Deicyde/riemann-hypothesis-contrib/commit/27425664ec0de3530a1e1c3f203231e0fe8aec7b) | Prepared on Jack’s fork; original branch publication requires maintainer credentials. |

## Publishing prepared heads

Use an account that can update each original PR branch. Save this directory’s `push_prepared_rebases.py` and `rebase-manifest.json` together, then run:

```sh
gh auth setup-git
python3 push_prepared_rebases.py          # read-only preview
python3 push_prepared_rebases.py --apply 9 10
```

`--apply-all` publishes every ready entry. The script refuses changed main or PR heads, verifies the prepared ref, creates original-head backups and uses exact force-with-lease updates. It skips PRs that have closed. It never merges or closes a PR. Lean build validation remains necessary.

Each manifest row links its immutable per-run report, with conflict stages, resolutions and checks. The preparation and checkpoint branches preserve reviewable Git histories.
