# Report verification overview

The eighteenth complete pinned Lean build and transitive axiom audit passed:
**5,126 explicit theorems, 7,704 total theorem declarations, 251 exact targets,
729 frozen Lean files**. Only propext, Classical.choice and Quot.sound occur.
No sorry/admit, custom mathematical axioms or unchecked mathematical computation
is used. Every original research source is preserved.

The entire original report is **not yet verified**: the older R numerical
attribution lacks its defining objective, and E's historical execution archive
is absent. M's additional literal Gram-sum identity and sharp potential-degree/root-limit
exports are now also proved; the original principal theorem chain is preserved.

| Module | Verified scope / remaining item |
|---|---|
| M | Actual full-BFGS principal determinants and matrix hierarchy, derived normalized hierarchy, reciprocal means, finite horizon and superquadratic growth; actual objective-run bridges. Literal Gram-sum equality, sharp potential degree and actual root limit are also proved. |
| T | Transported-certificate convergence and stated variants, with explicit certificate hypotheses. |
| R | Recoverable current radial/inward/supporting-plane theory, families and boundaries; older four-piece attribution at lines 182–187 remains unresolved. |
| F | Stated structural families, local basins, affine lifting and rates, with documented proof replacements. |
| H | Homogeneous value dichotomy, recurrent affine geometry, stated low-rank convergence and examples; explicit higher-rank questions remain questions. |
| Q | Actual parabolic envelope, ordered pruning, printed certificate field, convergence and radial separation. |
| G | Scalar convergence, certificate geometry and nonnecessity, with the documented accessible/all-active-span correction. |
| A | Actual affine-critical geometry, general semialgebraic projection, literal paths/composition/components, finite critical values and original low gap. |
| C | Stated planar convergence/basins and proof ingredients, with the documented C2-to-C1 regularity qualification. |
| U | Stated fixed-normal/parallel-interface results and examples, with the nonzero-jump qualification. |
| D | Actual exact seed, all deterministic search decisions, infinite failure and embeddings; five displayed rounding corrections documented. |
| L | Actual return-map dynamics, stable-orbit construction, infinite failure, regularity and embeddings; Jacobian rounding correction documented. |
| I | Current mathematical synthesis and supersession implications; inherited R attribution and historical evidence remain qualified. |
| E | Current analytic claims reconciled against actual Lean results; original 19-job outcomes, counts, timings and archive identities remain unverified. |

Conditional energy/frame/cover/value helpers remain identified in STATUS.json.
Their hypotheses are retained as criterion hypotheses or discharged by their
actual objective applications as documented. The source's explicit conjectures
and expressly unclaimed blanket BFGS/robustness conclusions are not theorem
completion targets.

The source register covers all 14 modules, 172 disjoint spans and 4,323 chapter
lines. See [REPORT_STATUS.json](REPORT_STATUS.json) for exact exports and source
hashes, [the geometric statement review](REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md) and [the literal M/audit review](REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md) for
the final geometric hypotheses and definitions, and
[STATUS.json](STATUS.json), [the complete checker transcript](report_literal_foundation_check.log)
and [axioms.log](axioms.log) for actual compiler and dependency evidence.

To finish the unresolved original-source claims, recover the older four-piece
objective used in R182–187 and the verification archive identified by E. The
current D objective and newly executed Lean proofs do not identify those
missing inputs. Any correction or retirement must be explicit and preserve
the original record.

Reproduce with the pinned toolchain using `bash scripts/bootstrap.sh`, or run
`python3 scripts/check.py` once dependencies are available. The default command
timeout is 7,200 seconds. Stage intended delivery files only after logs close,
regenerate MANIFEST.json, review the source/status correspondence, then commit
and push the completed milestone.
