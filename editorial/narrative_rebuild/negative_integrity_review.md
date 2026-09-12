# Narrative supplement release integrity update

Edited only `editorial/verify_release_inputs.py` and this review note. The integrity gate was **not executed** in this task, as root requested; root owns execution after refreshing the current contract maps. No files were staged or committed.

The required full-library audit run is now `20260912_narrative`. Existing checks for unchanged research/corrected sources and dependencies, old article geometry audit, current theorem correspondence, all 172 companion spans and 3,087 exports, remaining obligations, resolved overflow-free PDF builds, and authoring placeholders remain in place. The final failure exit uses an explicit conditional rather than an assertion, so Python optimization cannot remove it.

The new checks require exactly the positive `20260912_mixed_benchmark_02` and negative `20260912_covariance_01` runs in `FORMAL_SUPPLEMENTS.json`, with their correct module names and all 3/11 module-owned declarations including helpers. They verify:

- Manifest hashes for both summaries and declaration artifacts; all recorded retained source/input/output and command-log hashes. Positive input verification includes each of the 761 frozen original inputs and the added supplemental inputs, rather than confusing the original-input count with the larger combined input manifest.
- Actual successful compile/audit commands; the compiler version log agrees with the pinned version and summary; the actual audit-log JSON agrees with the raw audit summary and final summary.
- Exact root type/value agreement recorded by the hashed kernel auditor, per-root ordinary collector agreement, and safe/nonpartial root and transitive declarations. The ordinary axiom collector is not confused with a namespace sample.
- Unique root/graph names, complete owned-module coverage, closed dependency edges, root-to-graph dependency agreement, and full graph reachability. Positive type/value/structural edge partitions are checked against the retained graph. A fresh traversal of each retained root's full graph must recover its reported axiom set, with only `propext`, `Classical.choice`, and `Quot.sound` allowed.

Integration issue found and resolved by policy coordination: the positive summary records an `.olean` hash, while the source archive deliberately excludes compiled caches. When present, the cache must match that hash. When absent, the gate reports that only its historical hash is retained and makes no fresh-compilation claim. Root explicitly approved this handling and assigned actual supplemental compilation/audit replays in the extracted archive to the positive agent. Retained source/log/graph/declaration artifacts remain mandatory in both environments.

This remains an integrity check over authenticated retained evidence, not an independent replacement for Lean's kernel or a new full-library build. Its hash manifests are checked against current files, and its graph checks independently test the internal consistency of the retained dependency reports. Final execution, malformed-artifact rejection checks, current source-map refresh, and extraction replay are root's integration work.

Independent read-only review: the bibliography agent inspected the final extended gate and both actual supplement summary/command schemas and reported no actionable integration blocker. It confirmed the exact run/module counts, source/output/version/audit-log checks, complete graph reachability and axiom agreement, and the honest omitted-cache classification. That reviewer did not execute the gate or rerun Lean.
