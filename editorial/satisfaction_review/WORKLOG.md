# Skeptical refinement worklog

12 September2026. Started from clean tracked commit dbe14e9 and preserved the prior narrative release. Fresh mathematical, editorial and formal-contract reviews were commissioned alongside a root review of the matrix/energy proof. One introductory scope omission was corrected, repetition was pruned, citations/proof headings clarified, and two short proof deductions expanded. Builds give46 article pages and107 companion pages without errors/overfull boxes. All46 article pages have been freshly seen; changed companion pages have been seen, with unchanged pages to carry forward only by exact pixel hash.

A stricter full structural geometry audit freshly compiled14 unchanged declarations and checked26,496transitive dependencies. All contracts and axioms agree with the earlier audit. The release checker and extraction runner now authenticate and replay this third article supplement; an actual gate run passed19checks.

The new skeptical correspondence pass identified that the canonical lower-negative theorem's first-three-branches non-second-differentiability clause is proved in prose via scalar restriction but is not literally a field of SmoothLocalFailureTarget. An additional exact wrapper is being compiled for the actual branches and their one fixed whitening. This is an explicit proof-composition/correspondence refinement, not a changed theorem or a mathematical counterexample to it. The task remains active until that refinement and the revised archive/push gates are complete.

The exact branch wrapper is now compiled and fully audited:3owned declarations,37,525transitive declarations, standardaxioms only. Its combined theorem conjoins the unchanged actual failure target with non-differentiability of the derivative map for each of the three actual whitened branches. Current full evidence gate passes20checks. The source/proof refinement is a major milestone. A further reproducibility code review requests exact reused-library object hashes and explicit source/Lake-trace linkage; this is being added before the final archive replay, without a clean Mathlib rebuild claim.

The additional `lake --rehash build` attempt failed at ProofWidgets' JS extra
target. Diagnosis found that the pinned upstream repository tracks an obsolete
hash sidecar for its unchanged package-lock.json; rehash rewrote that sidecar to the actual
lockfile hash and the build failed at the pinned errorOnBuild guard. The retained
diagnosis distinguishes these observations from a simplified exploratory hash
fold, which did not reproduce the complete target-trace hash. The failed build/log and exact hash diagnosis are retained.
The controlled hash-sidecar mutation from this attempted build is restored to
the original pinned bytes. No user change or proof source is discarded.

The cache-binding method therefore uses an ordinary pinned Lake build plus
independent read-only recomputation of every cached .olean output hash and
comparison with every existing Lake .olean.hash, together with SHA-256 of
objects, paired source/trace files and compiler executables. Lake hashes source
inputs directly; the independent output pass removes reliance on unexamined
proof-output hash sidecars. The JS guard and all pinned Git revisions remain
intact. This is explicitly not a successful --rehash build, a clean rebuild or
independent re-typechecking of imported objects. A new unique successful run,
if obtained, will be recorded separately from the failed cache_binding_01.

Final cache_binding_04 passed: 8,853 objects, all paired source paths, 32,470 cached files, and 7,382 independently recomputed existing Lake output hashes. The ordinary pinned build and the later read-only check both passed. All nine dependency revisions are clean. Seven adverse-input guard tests passed. No successful --rehash or empty-cache build is asserted. All 153 final PDF pages are approved by actual visual review, with unchanged companion pages carried only by exact pixel hashes. The manuscript is satisfactory as an author-review candidate; the current source archive replay and final push remain execution gates.
