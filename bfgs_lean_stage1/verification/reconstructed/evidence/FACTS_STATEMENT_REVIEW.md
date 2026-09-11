# New reconstructed theorem counterparts

This frozen one-file scope adds five proved facts, one proposition definition and one wrapper, all in `BfgsVerification.EReconstruction`. It imports existing checked objective/run modules directly, without importing the root library.

* The inverse secant equation uses the literal ordinary full inverse-BFGS update with arbitrary finite dimension and nonzero actual curvature. Expanding the right factor kills its product with `y`; the rank-one term is exactly `s`.
* The Hessian secant equation derives positivity/invertibility of that actual update from initial SPD and positive curvature, then applies its checked inverse identity. No inverse or update is supplied as a hypothesis.
* The generic tolerance lemma unfolds eventual convergence to zero on `atTop` and returns a natural tail index for every positive tolerance.
* The planar specialization preserves the original literal objective and actual admissible-run hypothesis, and the exact initial-value basin `<1/100`. It applies the already checked full-BFGS convergence theorem and proves positivity of `10^(-45)`.
* The spike specialization preserves arbitrary dimension and a unit normal, and uses the actual full-series objective. It derives eventual value `<10^(-28)` from the checked actual-run theorem.

The last two conclusions are existential tail results, not computed stopping times. They do not certify historical numerical runs, floating-point trajectories, iteration counts, trial counts or decimal precision. Their hypothesis is the ordinary actual `AdmissibleBFGSRun`; no matrix or iterate limit is assumed.

`lean/FactsAudit.lean` independently writes the complete four-clause public proposition and strictly checks the wrapper against both this literal proposition and the public target definition. It also enumerates all seven declarations using the pinned ordinary `Lean.collectAxioms`, permitting only `propext`, `Classical.choice`, and `Quot.sound`. `design/verify_facts.sh` rebuilds the three direct main dependencies and the owned source before running those checks. This is separate from the evolving nineteen-job orchestration.

Historical assertions are unsupported AI-generated evidence and are superseded by this authored reconstruction; their truth or falsity is not established by missing inputs. The original report remains unchanged.
