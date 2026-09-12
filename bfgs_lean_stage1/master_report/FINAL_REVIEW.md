# Final review of the rigorous corrected BFGS master edition

The delivered edition contains reviewed Lean counterparts for every retained
mathematical assertion. Its scope is the corrected report: false unrestricted
formulas, missing qualifications and unsupported historical execution claims
have explicit corrections. Definitions, hypotheses, conditional lemmas,
execution records and open questions are classified separately. Lean checks the
formal statements and proof terms; the correspondence with the mathematical
prose is an independently reviewed interpretation, not a parser theorem about
English. The citation revision adds bibliographic and historical comparisons,
which are explicitly editorial scholarship, not further Lean-certified
assertions or independently verified proofs of external publications.

The complete source map covers 14 modules, 172 disjoint spans and all 4,323
original chapter lines. The current 114 guarded edits are recorded with
both original and corrected text. This includes the integration of 41 attribution
notes and five corrections to unqualified novelty wording; the bibliography
contains 38 external works and 15 internal topic labels (53 unique keys). The
3,087 distinct linked exports have an
8,249-declaration project dependency closure in the searchable proof index,
including exact types, universe parameters, source excerpts and links, and
48,690 distinct dependency edges (66,681 occurrences distinguished by role).
The index exposes named proposition definitions through their source bodies;
an opaque theorem alias alone is not treated as statement review.

The principal foundation is about actual full-BFGS matrices and actual principal
determinants in arbitrary finite dimension. The scalar hierarchy is derived
from that matrix result. The qualitative reciprocal-mean divergence,
finite-horizon bounds and superquadratic reciprocal-sum growth under summable
predicted decreases have checked formal proofs. Main convergence and failure
results retain ordinary full BFGS, Armijo–weak-Wolfe and differentiable accepted
iterates; they do not assume iterate or matrix convergence. Helper implications
retain their explicit hypotheses, and the main applications discharge the run
and matrix obligations they use.

The preserved pinned compiler run from the preceding mathematical release uses
Lean 4.19.0, mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, and nine clean pinned dependency trees.
That release's module-wide audit covers 9,672 safe main declarations and 9,781 safe
main-plus-supplement declarations, including 7,954 theorems. It includes private
and generated declarations omitted by the older namespace-only enumeration.
Every one of the prior 7,813 namespace theorem statements and axiom sets is
reconciled with the wider audit. Actual commands, exit codes, compiler output,
source identities and both complete declaration inventories are delivered in
[audit/](audit/README.md); this is not a predicted or simulated compiler log.

No new Lean compiler run was performed for the citation-only revision. Its
preservation check recovers every preceding corrected chapter exactly after
removing the attribution blocks and reversing the five wording substitutions.
All 172 formal export lists and the entire declaration index remain unchanged,
as do Lean and pinned toolchain inputs. The new notes retain their source IDs
and an explicit nonformal status in the claim register and proof index. This
check preserves the existing formal evidence; it does not prove publication
priority or validate all external papers.

All transitive axiom dependencies belong to `propext`, `Classical.choice` and
`Quot.sound`. There are no custom mathematical axioms, sorry/admit proof holes,
missing dependencies or unsafe/partial artifacts reachable from a safe
mathematical declaration. Compiler implementation-only unsafe artifacts are
separately enumerated and excluded by a checked reachability boundary. Python,
JavaScript, decimal displays and external numerical computations do not supply
mathematical proof terms. This audit identifies the foundations used; it does
not prove the consistency of Lean or those foundations.

Corrections include the homogeneous reference formula and compact optimizer
argument in R, the accessible-jump/full-active distinction in G, the determinant
orientation and regularity qualifications in C, the exact Armijo endpoint and
all-parameter family in Q, the nonzero-coupling condition for the U nonsplitting
claim, explicit zero-dimensional cases, and corrected explanatory decimals.
Alternative formal proof routes and reconstructed examples are disclosed.
The general-dimensional conjecture in A and remaining higher-rank zero-value
iterate question in H remain explicit open questions. They are not counted as
proved conclusions. Original research sources, all 737 main Lean files, and the
closed milestone 19/20 records remain preserved.

The current PDF has 98 pages. Its actual LaTeX render returned PASS with no
selected warnings, empty pages or extracted words outside page bounds. The
revision's visual inspection set comprises seven contact sheets and 13 enlarged
samples (pages 1, 3, 15, 21, 33, 55, 60, 70, 75, 82, 94, 96 and 98). The separate
[visual review](render/VISUAL_REVIEW.json) records the findings and binds the
inspection to the exact current PDF and images; its page count and PDF hash must
match this revision. The preceding 92-page inspection is historical evidence,
not a visual certification of the changed edition. The functional HTML test
exercises actual claim filters, search, theorem detail, dependency navigation
and escaping in a Node DOM harness. The preceding desktop browser attempt timed
out; no real-browser visual or accessibility certification is claimed.

Independent reviews are retained in `review/ac_tfh/`, `review/pre_release/`,
`review/audit_final/` and `review/release_gate/`. Preparatory failures remain
identified as failures, including the repaired overly broad LaTeX warning
classifier. The preceding release replays in `review/release/` remain historical evidence, including the authoring
verification marked `before_seal: true`. Current citation-revision reviews,
preservation checks, render attempts, index checks and final release gates are
recorded separately in [review/citation_revision/](review/citation_revision/).
Their recorded statuses and PDF hashes determine the current release outcome;
a preceding PASS does not certify a changed artifact. The default public gate
additionally checks the complete artifact manifest. Run:

```sh
python3 scripts/verify_rigorous_master_report.py
```

The final [manifest](MANIFEST.json) seals the report, proof/audit evidence,
review records, rendering/visual evidence, generated index, PDF and these public
scripts:

- `scripts/build_rigorous_master_report.py`
- `scripts/render_rigorous_master_report.py`
- `scripts/make_master_report_visual_evidence.py`
- `scripts/verify_rigorous_master_report.py`
- `scripts/apply_report_attributions.py`
- `scripts/verify_report_attributions.py`

The attribution application script is a guarded, one-use baseline migration;
normal reproduction assembles the already updated edit ledger. The read-only
preservation checker requires the full Git history, including immutable
baseline commit `06ee12f7e7661437b8481fcab3b5bd26cff60130`; a source archive or
shallow checkout without that commit cannot perform the comparison. Fresh
compiler runs use new timestamped directories; they do not overwrite the closed evidence. Read-only milestone 19 and 20 checks
are retained alongside the final review evidence. Git records the reviewed
release and its publication separately from the historical compiler records.

At the preceding 11 September mathematical release, an independent read-only
packaging review found no tracked source changes, release caches, symlinks,
compiled Lean binaries or credential-pattern matches. Those dated findings
remain historical; they do not describe the intentional citation-revision
changes.

All 8,249 indexed source links resolve inside the repository; public scripts use
repository-relative or PATH-based runtime locations. The largest individual
artifact is approximately 16.7 MB. Fresh reproduction is documented as a separate
checkout because new run directories intentionally change the sealed inventory.

The preceding sealed public release gate returned PASS with
`before_seal: false`. Its staging whitespace check reported only verbatim LaTeX
logs (including preserved preparatory logs) and one generated chapter's terminal
blank line; no authored Python, Lean or editorial input whitespace defect was
reported then. These historical output-format findings are retained to preserve
exact evidence and deterministic generation. The citation revision's final gate
and packaging results are recorded under `review/citation_revision/`; they are
separate executions rather than a relabeling of the earlier logs.

The citation revision's sealed public gate returned PASS with
`before_seal: false`; its exact output is [final_gate.json](review/citation_revision/final_gate.json).
The final replay after recording that output and resealing reproduced it exactly.
The separate [literature audit validation](../literature_audit/review/validation.log)
also returned PASS against its immutable historical report baseline.

A subsequent ZIP extraction check found three macOS `.DS_Store` entries in the
artifact manifest. Those ignored, untracked metadata files were available in
the original working directory but absent from a committed-source archive.
The portable release manifest and its inventory check now explicitly exclude
that fixed basename, while retaining all report, proof and audit artifacts.
The report/PDF, mathematical exports, pinned inputs and compiler evidence did
not change. The packaging failure, correction and fresh extraction checks are
recorded under [packaging/review/](../../packaging/review/).
