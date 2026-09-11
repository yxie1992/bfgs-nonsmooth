# Module F quadratic-plus-coercive-gauge verification

Status: compiler checked and independently axiom audited; root integration is
performed separately. These files prove the concrete family in the “Quadratic
plus coercive gauge” paragraph of `report/chapters/families.tex`, rather than
assuming the objective-specific correction bound in `ObjectiveLogRates.lean`.
Original research sources are preserved.

## Exact objective and assumptions

`QuadraticGauge.objective Q γ` is the actual function
`x ↦ (left x)ᵀ Q (left x)/2 + γ(right x)` on `Fin (m+p) → ℝ`, with actual
finite-coordinate left/right projections and `Fin.append` reconstruction.
The source assumptions are symmetric positive-definite Q, a finite convex
positively degree-one homogeneous γ, and `0 < μ` with
`μ‖v‖₂ ≤ γ(v) ≤ Λ‖v‖₂`. The run is the existing actual
`AdmissibleBFGSRun (m+p) (objective Q γ)`.

No bounded iterates, bounded matrices, matrix limits, step bounds, path-length
bounds, uniform Hessian condition numbers, pre-assumed corrections, or accepted
gradient decomposition enter the final theorems. Run convexity is already an
ordinary field of the objective-run definition. Separately,
`QuadraticGauge.objective_convex` derives this convexity from PSD Q and convex γ.
`coerciveGauge_sublevel_compact` gives compactness directly from the model
assumptions, independently of any run.

The internal lower/upper inequalities use `Real.sqrt (sqNorm v)`, the exact
Euclidean norm. `sqrt_sqNorm_eq_euclidean_norm` proves this equality, and
`quadraticGauge_euclidean_value_log_orders` states the rate using the explicit
Euclidean norm. No finite-Pi sup norm is silently substituted. Either coordinate
block may have dimension zero. No unnecessary sign hypothesis on Λ is added.

## Discharged proof chain

1. `quadratic_hasGradient` proves the actual derivative of the quadratic.
   `hasGradient_right` restricts the actual full Fréchet derivative to the gauge
   slice. `quadraticGauge_gradient_split` proves the accepted gradient is
   `(Q u, h)` with h the actual accepted gauge derivative. Differentiability at
   nonsmooth centers or rejected line-search points is never assumed.
2. Actual supporting vectors restrict to the coordinate slices. Homogeneity
   gives gauge Euler/support identities, `0 ≤ ζ ≤ b`, and `ζ ≤ C γ(v')`.
   PSD Cauchy–Schwarz proves `ξ² ≤ a u'ᵀQ u'`.
3. The proved weighted-square inequality includes a=0 and b=0. It yields the
   actual pair correction and then
   `R.referenceCorrection 0 k ≤ C*objective Q γ (R.x(k+1))`, with the source's
   exact `C = max 2 (1+Λ/μ)`.
4. Positive definiteness and the positive gauge lower bound derive the unique
   minimum 0 at x=0. Finite convexity and this unique minimum derive compactness
   of every sublevel; the accepted initial sublevel is therefore compact.
5. `quadraticGauge_finite_budget` proves
   `F_N² S_N ≤ E_0 + C Σ_{k<N} F_{k+1}` using the actual Hessian recurrence.
   `quadraticGauge_finite_sqrt_bound` divides by actual `S_N>0` for N>0.
6. The compact sublevel supplies bounded actual gradients, and Armijo supplies
   summable predicted decreases. The previously checked actual principal-minor
   theorem supplies superquadratic reciprocal sums. The root's harmonic-budget
   proof then gives `sqrt(A_N)/log N → 0`, `F_N=o(log N/N)`, and the weaker
   `F_N=O(log N/N)`. `quadraticGauge_convergence` derives F_N→0 and x_N→0.

The source's intermediate notation ξ²/a can be undefined when the quadratic
block does not move, and similarly the gauge curvature b can vanish. The
formal proof uses the division-free inequalities and explicitly proves both
zero-weight cases. This fills that case distinction without weakening the
conclusion, changing C, or introducing a positive-block-curvature assumption.

## Files and reproducibility

Seven modules, 39 public theorems and five definitions:

- `QuadraticGaugeAlgebra.lean`
- `QuadraticGaugeSupports.lean`
- `QuadraticGaugeCorrection.lean`
- `QuadraticGaugeGeometry.lean`
- `QuadraticGaugeDerivatives.lean`
- `QuadraticGaugeConvex.lean`
- `QuadraticGaugeRates.lean`

From `bfgs_lean_stage1`, using the pinned toolchain:

```bash
source scripts/env.sh
lake build BfgsVerification.QuadraticGaugeRates
lake env lean audit/QuadraticGaugeAxiomChecks.lean
```

Actual logs are `audit/quadratic_gauge_full_build.log` and
`audit/quadratic_gauge_axioms.log`. The latter prints the transitive axiom
closure of all 44 declarations. Every closure is exactly a subset of
`propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`, a custom
mathematical axiom, or unchecked external computations. The seven source files
contain no sorry/admit/axiom/native_decide/unsafe declaration or invocation.

This tranche does not verify the other Module F family descriptions, examples,
ray-search existence claim, or Module H.C. Those remain separately tracked by
the whole-report inventory and subsequent tranches.
