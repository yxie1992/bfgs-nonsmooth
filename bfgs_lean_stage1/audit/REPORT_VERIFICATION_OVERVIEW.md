# Corrected report verification overview

The corrected report is verified: **5,195 explicit/7,813 total theorem
declarations, 255 exact targets,737 frozen Lean sources**, and **19 new jobs with
107 strict literal checks across 93 distinct theorems**. All permitted transitive
axioms are propext, Classical.choice and Quot.sound.

[CORRECTED_REPORT.md](../CORRECTED_REPORT.md) is the mandatory correction companion
to the unchanged original master report. It defines the new R objective and
actual full-BFGS run, preserves the nine earlier mathematical corrections, and
specifies every replacement for unavailable historical inputs. Original history
is neither recovered nor certified; the original-snapshot flags remain false.

| Module | Verified scope / remaining item |
|---|---|
| M | Actual full-BFGS principal determinants and matrix hierarchy, derived normalized hierarchy, reciprocal means, finite horizon and superquadratic growth; actual objective-run bridges. Literal Gram-sum equality, sharp potential degree and actual root limit are also proved. |
| T | Transported-certificate convergence and stated variants, with explicit certificate hypotheses. |
| R | All radial/inward/supporting-plane theory, families and boundaries; new explicit four-piece realization of lines182–187 with actual bad run and SP/RS failure. |
| F | Stated structural families, local basins, affine lifting and rates, with documented proof replacements. |
| H | Homogeneous value dichotomy, recurrent affine geometry, stated low-rank convergence and examples; explicit higher-rank questions remain questions. |
| Q | Actual parabolic envelope, ordered pruning, printed certificate field, convergence and radial separation. |
| G | Scalar convergence, certificate geometry and nonnecessity, with the documented accessible/all-active-span correction. |
| A | Actual affine-critical geometry, general semialgebraic projection, literal paths/composition/components, finite critical values and original low gap. |
| C | Stated planar convergence/basins and proof ingredients, with the documented C2-to-C1 regularity qualification. |
| U | Stated fixed-normal/parallel-interface results and examples, with the nonzero-jump qualification. |
| D | Actual exact seed, all deterministic search decisions, infinite failure and embeddings; five displayed rounding corrections documented. |
| L | Actual return-map dynamics, stable-orbit construction, infinite failure, regularity and embeddings; Jacobian rounding correction documented. |
| I | All corrected mathematical synthesis and explicit supersession implications; historical record clearly distinguished. |
| E | All retained analytic claims and new 19-job execution evidence; unsupported original outcomes/counts/timings/archive identities explicitly superseded. |

Conditional criteria retain their actual hypotheses; their report applications
discharge the required premises as recorded. Explicit conjectures and unclaimed
blanket convergence/robustness results remain outside theorem claims.

The source register covers 14 modules, 172 disjoint spans and 4,323 chapter lines.
See [REPORT_STATUS.json](REPORT_STATUS.json),
[complete compiler evidence](report_reconstruction_check.log),
[all transitive axiom reports](axioms.log),
[new execution results](../verification/reconstructed/fresh/SUMMARY.json), and
[independent completion review](REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md).

Reproduce with `bash scripts/bootstrap.sh`, then
`python3 verification/reconstructed/run_all.py` and
`python3 scripts/validate_report_reconstruction_19.py`.
