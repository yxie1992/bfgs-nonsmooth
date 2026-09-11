# Module G individual pair and finite sample peer review

Reviewed `PairRealizability.lean` and `FiniteSampleCertificates.lean` against source G.3 and G.9. Read-only review by the scalar/example agent. No mathematical gap was found in these theorem statements or their scope.

## Individual eligible-pair realization

`realizingMetric` is exactly the source matrix, reordered as `I-gg^T/(g^Tg)+ss^T/d`, with `d=-g^Ts`. Its positive definiteness is proved from `d>0` using the already established positive inverse-BFGS update and exact Hessian-update identity, so it does not assume positivity of the new matrix or a BFGS trajectory. The same premise implies `g!=0` and permits the denominators used in the exact calculation.

`realizingMetric_mul_gradient` proves `Hg=-s` exactly. `realizingMetric_step` therefore proves the unit-length step is `s`. `eligible_pair_realizable` exports an actual SPD matrix with this step and the same predicted decrease for every actual `EligiblePair`. Differentiability and the Armijo/weak-Wolfe endpoint inequalities remain in the `EligiblePair` premise, so the produced step realizes those very endpoints with alpha one. This is appropriately an individual first-step result; it never joins different predecessors into a common history or claims an infinite admissible extension.

The theorem is dimension independent. Dimension zero is harmless: its positive-decrease premise is impossible, not an omitted nontriviality assumption.

## Free-constant finite sample feasibility

`finite_sample_identity_certificate` proves the visibility, suppression, and exact projected-transport comparisons for one constant identity field. Each sample gradient is nonzero; each listed pair is actually eligible; `c2<1` derives positivity of every pair's curvature denominator. No hidden finite precision or external maximization is used.

The visibility constant is a finite positive minimum constructed inductively. For the suppression constant the proof uses the sum of the finitely many nonnegative quotients instead of the source's maximum; this is an equally valid finite common upper bound and does not change the existential claim. The empty endpoint set receives the explicit visibility choice one; an empty pair set receives suppression constant zero. Thus the edge cases omitted by the informal minimum/maximum notation are covered without excluding them.

Transport is the PSD zero difference of the same projected identity matrix, for every step vector, and therefore is exact nonexpansion. The identity field itself is finite and positive definite by existing mathlib facts. The theorem does not assert a continuum certificate or a bound uniform across an increasing sequence of finite samples.

`positive_band_finite_sample_feasible` derives nonstationarity from actual derivatives of a convex objective at points with values strictly above a fixed comparison point, using the proved zero-gradient global-minimum criterion. The comparison point need not already be a minimizer; this strengthens the finite-sample theorem and includes the source's positive bands. The algebraic finite theorem permits arbitrary nonzero endpoint vectors even when unused by any pair; the objective specialization supplies actual derivatives at every endpoint.

The interpretive source conclusion is preserved: arbitrary finite samples with free constants cannot certify continuum nonexistence, and success on those samples does not establish a single uniform continuum field.
