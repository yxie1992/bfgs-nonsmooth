# Module Q source-to-formalization map

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/Q.tex`. The source is
preserved. This map distinguishes the literal claims from alternative
proof constructions used to establish them. The new continuations require
the normal whole-project integration audit in addition to their scoped
audits before the next release is marked verified.

| Source assertion | Checked declaration/module |
|---|---|
| Arbitrary finite family, positive a_i, both slope signs, arbitrary duplicates and zero b_i | `Parabolic.Family`; no pruning/calibration witness is an input. |
| Every actual admissible unmodified full-BFGS run converges in values and iterates to zero | `AdmissibleBFGSRun.parabolic_convergence` in `ParabolicCertificate`. |
| Convexity, actual differentiable active gradients, quadratic lower bound, compact sublevels, unique zero minimizer | `objective_convex`, `active_eq_gradient`, `quadratic_lower_bound`, `sublevel_compact`, `unique_minimum` in `ParabolicFamily`. |
| Literal removal of redundant and tie-only pieces and merging duplicate/equal-slope pieces | `Essential`, `essential_strict_interval`, `essential_same_slope_maximal`, `essential_slopes_injective`; `prunedFamily` is derived. |
| Removal preserves the objective and its differentiable gradients, including u=0 | `prunedFamily_objective`, `prunedFamily_gradient`, `essential_active_gradient`. |
| Retained slopes strictly increase, both slope signs survive | `prunedFamily_slopes_strictMono`, `exists_essential_positive_slope`, `exists_essential_negative_slope`. |
| Actual neighboring breakpoints strictly increase and have positive envelope values | `orderedBreakpoint_strictMono`, `adjacent_breakpoint_active`, `adjacent_breakpoint_value_pos`; packaged in `ordered_pruning_specification`. |
| Q.7 exact neighboring calibration | `adjacent_calibration`; the stronger original-index tie identity is `calibration_active_eq`. |
| Q.8 selector-free positive bounded continuous scale across all positive-level ties | `calibratedScale_eq_active`, `calibratedScale_continuousOn`, `calibratedScale_uniform_bounds`; actual vector/matrix continuity in `ParabolicCertificate`. |
| Q.9--Q.12 exact pair identities; small eligible horizontal/deficit bounds; weighted secant inequality | `ParabolicPairs`; exact active endpoint derivatives come from the original objective. |
| Visibility and uniform secant correction (V), (S) | `positive_visibility`, `exists_uniform_secant_bound`, assembled with the actual scale in `exists_bandCertificate`. |
| Q.13 uniform d and horizontal-step bounds by absolute determinant, derived determinant nonzero | `exists_small_denominator_bounds` in `ParabolicDenominator`. |
| Q.14 identity including zero old normal slope | `slope_determinant_identity`; `horizontal_from_determinant` never divides by b_i. |
| Exact quotient multiplier, displacement-parallel difference, Q.15 cancellation | `radial_direction_transport`, `quotient_cancellation` in `ParabolicTransportAlgebra`. |
| Logarithm remainder and old-index exponent increment | `log_remainder_bound`, `exponent_increment`, the scalar and rational bounds in `ParabolicScalarTransport`/`ParabolicQuantitativeAlgebra`. The latter uses an exact identity instead of an assumed Taylor remainder. |
| Q.16 uniform finite-cell bound for arbitrary old/new original branches | `exists_calibration_deficit_bound` in `ParabolicEnvelopeBound`; includes duplicates, singleton cells, and normalized quadratic coordinate zero. |
| Q.17 uniformly compensated logarithm and resulting projected transport (T) | `exists_uniform_log_transport`, `exists_uniform_vector_transport`, actual `rankOneCertificate`, and `exists_bandCertificate`. |
| Q.18 exact explicit maximum | `Parabolic.Example.objective_eq_max`. |
| Explicit middle region, including its normal-coordinate flatness | `objective_middle_region`, `objective_middle_closed`; the objective there is exactly 3u². |
| Printed piecewise theta, exact bounds and continuity across both interfaces | `sourceScale`, `sourceScale_bounds`, `sourceScale_continuousOn`. |
| Printed field is an actual certificate, not just endpoint formulas | `sourceScale_eq_normalized`, `sourceVector_eq_normalized`, `exists_source_bandCertificate`. |
| Printed/generalized actual gradients, values, SPD matrix, unit BFGS step, d=t and radial numerator | `ParabolicExamplePairs`. |
| Printed Armijo range and strict acceptance; weak Wolfe is strict for c2>0 | `printed_armijo_iff`, `printed_strict_acceptance`, `strict_weak_wolfe`. |
| Literal radial quotient divergence, d to zero, positive limiting objective value for fixed u!=0 | `radial_quotient_tendsto`, `pair_decrease_tendsto`, `pair_values_tendsto` with `sq_pos_of_ne_zero`. |
| RS fails in every neighborhood and every positive sublevel | `not_radial_secant_on_neighborhood`, `not_radial_secant_on_sublevel`. |
| Failure persists under arbitrarily small eligible d for every ordinary fixed line-search pair, with actual SPD first-step witnesses | `eligible_radial_unbounded_on_neighborhood`: eta is fixed before delta and C. The rho extension is documented separately. |
| Printed transported correction vanishes, quotient multiplier is one, exact compensated log formula | `transported_numerator`, `transported_quotient`, `transported_quotient_tendsto`, `quotientMultiplier_eq_one`, `source_compensated_log`. |
| Strict nonnecessity: actual runs converge although original RS fails | `converges_without_radial_secant`. |

## Proof routes and parameter scope

The principal Q theorem uses a compact normalized lower-envelope/ramp
construction to derive calibration for every original index. This proves
Q.7/Q.16 without requiring pruning. Literal source pruning and ordering are
now independently formalized by the four `ParabolicEnvelopePruning`,
`ParabolicEnvelopeOrdered`, `ParabolicEnvelopePrunedFamily`, and
`ParabolicEnvelopeBreakpoints` modules. The source's adjacent-proportional
versus nonadjacent-positive-deficit argument for Q.16 is subsumed by a
proved affine-segment lemma that also covers zero endpoints and singleton
cells. No unproved cell geometry is assumed.

The original epsilon/2 pair obeys Armijo exactly when c1<=2/3 and strict
Armijo when c1<2/3, as the source itself states. The extended rho pair
covers every original 0<c1<c2<1. See `PARABOLIC_EXAMPLE_SOURCE_SCOPE.md`.
The matrices vary with epsilon; these are individual accepted first steps,
not a constructed single infinite bad run. Actual infinite runs converge
by the main theorem.

The printed field's separate global normalization and continuity are now
checked, so the earlier fifth-milestone presentation obligation is closed.
No mathematical correction to Q's principal theorem was necessary.
