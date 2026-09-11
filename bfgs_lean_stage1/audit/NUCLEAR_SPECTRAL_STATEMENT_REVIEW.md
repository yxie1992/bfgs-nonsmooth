# Module R symmetric nuclear-norm boundary example: statement review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/R.tex`, lines 274–296. Original source is unchanged.

Reviewed import: `BfgsVerification.NuclearRotatedPairs`, importing `BfgsVerification.NuclearSymmetric2`.

## Actual matrix and norm model

`nuclear A hA` is the sum of absolute values of the **actual mathlib Hermitian eigenvalues** of the actual real symmetric 2×2 matrix A. There is no eigenvalue-oracle premise, stipulated norm formula, axiom, or numerical eigensolver. The spectral theorem proves the trace identity; the existing determinant/eigenvalue theorem proves the determinant identity. Those identities prove `nuclear_eq_max`:

`sum |eigenvalue| = max |A00+A11| sqrt((A00-A11)^2+4*A01^2)`.

The pinned mathlib has no separate named nuclear-norm implementation; the standard spectral definition for real selfadjoint matrices is used directly. This review does not claim a nonexistent comparison theorem with another library norm.

The coordinate map is `x ↦ [[x0,x1/sqrt(2)],[x1/sqrt(2),x2]]`. Its inverse on every actual symmetric matrix is proved. The sqrt(2) scaling is essential: `frobenius_matrix` proves that the sum of all four entrywise products is precisely the Euclidean coordinate dot product. Thus neither the derivatives nor the radial numerator substitute the ambient Pi norm for the Frobenius inner product. `gradientFunctional_frobenius` explicitly identifies every derivative functional's pairing with the Frobenius pairing.

`objective_on_symmetric` identifies the literal objective on every actual symmetric A; `matrix_center` and `matrix_minimizer` identify diag(2,0) and diag(1,0). All actual coordinates, including off-diagonal perturbations, are included.

## Source statements and exports

| Source | Exact checked statement |
|---|---|
| Strong convexity and unique optimizer (line 280) | `objective_frobenius_strong` gives the literal modulus-one Frobenius inequality. `objective_gap` gives half the squared Euclidean/Frobenius distance below the objective gap. `objective_minimum`, `objective_unique`, and `objective_sublevel_compact` follow without assumed coercivity. |
| Nuclear subgradient and cancellation (line 280) | `nuclear_minimizer_support` proves the actual global supporting inequality for diag(1,0); `minimizer_gradient_cancellation` proves cancellation with the smooth gradient. |
| Actual orthonormal trigonometric vectors and W=vvᵀ, U=uuᵀ (lines 282–288) | `Rotation.vectors_orthonormal`, `matrix_W`, `matrix_U`, `pair_matrix_form`; `trigRotation` supplies actual cosine/sine values and proves the unit-circle identity. |
| Both endpoints differentiable with nonzero eigenvalues (line 290) | `pair_determinants` proves determinants −ε and ε. `pair_eigenvalues_nonzero` proves every actual eigenvalue nonzero for ε>0. `pair_gradients` independently derives the actual Fréchet derivatives from the checked closed nuclear formula; no gradient identity is assumed. |
| Descending pair and exact objective difference | `pair_values` and `pair_descent` prove the full endpoint values and the difference −4 s² ε. Descent is strict when s≠0 and ε>0. |
| Gradient jump, T and N (lines 290–294) | `gradient_difference`, `pair_curvature`, `radial_numerator`, and `pair_frobenius_identities`. The latter explicitly uses actual matrix differences and Frobenius products. |
| Exact quotient and divergence (line 294) | `radial_quotient` and `radial_quotient_tendsto`; the limit filter is ε→0 through strictly positive reals. |
| Positive base gap and arbitrarily small rotations (line 296) | `base_value`, `trigRotation_base_continuous`, `trigRotation_base_zero`, `exists_rotated_base`. |
| A fixed positive band in every neighborhood with no uniform RS constant | `unbounded_radial_pairs` chooses θ and η before the arbitrary proposed bound C. Its witnesses remain the literal rotated pairs, lie in the given neighborhood, have actual derivatives, positive curvature, and strictly descending values. `not_radial_secant_on_neighborhood` is the exact RS negation. |
| Actual Frobenius neighborhoods and compact positive sublevels | `not_radial_secant_on_frobenius_ball` and `not_radial_secant_on_sublevel` remove any topology/model ambiguity. |

The general `Rotation` algebra assumes only c²+s²=1; the final neighborhood theorem discharges that premise using actual sine/cosine, and chooses 0<θ<π so sin²θ>0. No sequence of algorithm iterates or matrices is introduced or assumed convergent.

## Scope boundary

This is a failure of the original radial sufficient condition. It neither constructs nor claims a nonconvergent BFGS trajectory, and does not export BFGS convergence for this shifted nuclear example.

The last sentence contrasting the nuclear norm **centered at zero** belongs to the separate degree-one family instantiation. The generic finite sublinear/degree-one machinery is already checked, but an explicit positive-homogeneity/norm instantiation for this new spectral definition is not part of the frozen two-file counterexample tranche. It remains named separately rather than being inferred as a formally exported theorem. General-dimensional nuclear/spectral norm family identifications also remain separate.

No mathematical correction to this source counterexample was needed. The finite-max central `J|t|+O(t²)` bookkeeping remains a distinct R obligation and is not claimed by these modules.

## Reproduction and dependency review

- `source scripts/env.sh; lake build BfgsVerification.NuclearRotatedPairs`
- `source scripts/env.sh; lake env lean audit/NuclearExampleAudit.lean`
- Build logs: `nuclear_symmetric2_build.log`, `nuclear_rotated_pairs_build.log`.
- Axiom log: `nuclear_example_axioms.log`; validated names/hashes: `nuclear_example_validation.log`.
- 80 explicit theorems, 20 actual definitions and one structure: 101 scoped declarations. Every returned name matches the audit request, and every transitive dependency is within `{propext, Classical.choice, Quot.sound}`. No forbidden proof placeholders, mathematical axioms or unchecked evaluators occur in either file.

The scoped audit is not a substitute for the pending whole-project audit or a claim that all of Module R/the report is verified.
