# Source F:transform — statement and dependency review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/families.tex`, transformed-gauge theorem and proof, lines 25–50. Original sources are unchanged.

## Compiled main convergence theorem

`BfgsVerification/TransformedGauge.lean` formalizes every hypothesis in the displayed theorem. `IncreasingTransform Φ` constrains a real extension of Φ only on `[0,∞)` (continuity, convexity, strict increase, value zero) and `(0,∞)` (`ContDiffOn ℝ 2`, strictly positive actual derivative). Values at negative arguments have no role. The gauge is everywhere real-valued, convex and nonnegatively degree-one homogeneous. Coercivity is the standard `Tendsto γ (cocompact (Vec n)) atTop`, not an additional assumed norm estimate.

The file derives positivity of γ away from zero by the actual homogeneous ray, and derives convexity, nonnegativity, the unique attained minimizer, and compactness of every transformed-objective sublevel. Dimension zero is allowed in these geometric statements; an actual infinite admissible run already implies positive dimension through the existing library.

Euler's identity is proved from the actual Fréchet derivative of F by differentiating the radial curve `t ↦ star+t*(x−star)` near `t=1`. It does not assume differentiability of γ. The C² assumptions derive a positive lower bound for Φ′ and a derivative bound for `r*Φ′(r)` on each positive gauge annulus. Scalar mean-value estimates then prove the actual endpoint pairing bound. A compact positive objective band supplies the annulus, including an empty band without an added nonemptiness assumption.

`transformedGauge_correction_on_positive_band` proves the exact source coefficient

`R_k ≤ ((1+C)^2 / ((1−c₂)*c₁)) * (F_k−F_(k+1))`.

The algebra uses actual Armijo, convexity and weak-Wolfe inequalities and the exact accepted-step pairing identity. `transformedGauge_corrections_summable_on_positive_band` derives summability. `transformedGauge_values` and `transformedGauge_convergence` yield objective convergence to zero and accepted-iterate convergence to the unique center for the actual full-BFGS run. There is no assumed iterate, matrix, step, gauge-gradient or correction convergence.

The proof uses the previously verified actual principal-determinant hierarchy through the Module M correction criterion. It does not assert invariance of BFGS under the nonlinear scalar transform.

## Separately proved inverse and regularity interpretations

The main proof avoids a global inverse. These source proof interpretations are independently compiled in `BfgsVerification/TransformedGaugeInverse.lean`:

| Source statement | Declaration |
| --- | --- |
| Φ is unbounded above | `transform_tendsto_atTop` |
| Every nonnegative value has a preimage | `transform_surjOn` |
| Actual inverse on `[0,∞)` | `inverse`, `transform_inverse`, `inverse_transform` |
| Positivity, continuity and derivative of inverse at positive arguments | `inverse_positive`, `inverse_continuousAt`, `inverse_hasDerivAt` |
| Literal definition `Θ(t)=Φ⁻¹(t)Φ′(Φ⁻¹(t))` | `theta` |
| Literal formula `Θ′(t)=1+rΦ″(r)/Φ′(r)` | `theta_hasDerivAt` |
| Continuous/bounded Θ′ and the source interval MVT | `theta_derivative_continuousOn`, `theta_derivative_bounded`, `theta_lipschitz_on_positive_interval` |
| Source coercivity of the composed objective | `objective_coercive` |
| Gauge differentiability follows at actual differentiable endpoints | `gauge_hasFDerivAt_of_objective`, `transformedGauge_actual_gauge_derivative` |
| Every accepted radius is positive and `a_k=r_kΦ′(r_k)=Θ(F_k)` | `transformedGauge_radius_pos`, `transformedGauge_euler` |

The inverse is constructed with `Function.invFunOn` restricted to the nonnegative half-line. Its behavior at negative target values is not used. The bounded derivative theorem imposes only a positive lower interval endpoint; an empty interval is handled without an added nonemptiness hypothesis. No derivative bound at zero is assumed, and no global differentiability of γ is inferred. All inverse, derivative and MVT interpretations in the displayed F:transform proof are now proved independently of the main convergence route. No mathematical correction to this source theorem was needed.

This unit does not relabel the subsequent differently-powered-gauge family as a consequence of a single scalar transform, nor assert nonlinear-transform invariance of BFGS. Those are different source statements.

## Reproduction and audit

From `bfgs_lean_stage1`, source the pinned `scripts/env.sh` and run:

```sh
lake build BfgsVerification.TransformedGauge
lake env lean audit/TransformedGaugeAudit.lean
lake build BfgsVerification.TransformedGaugeInverse
lake env lean audit/TransformedGaugeInverseAudit.lean
```

The actual logs are `audit/transformed_gauge_build.log`, `audit/transformed_gauge_axioms.log`, `audit/transformed_gauge_inverse_build.log` and `audit/transformed_gauge_inverse_axioms.log`. All 46 explicit declarations (21 main and 25 inverse) were printed with their transitive dependencies; dependencies are a subset of `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom mathematical axiom or `native_decide` occurs. The global audit/register is maintained separately by the coordinator.
