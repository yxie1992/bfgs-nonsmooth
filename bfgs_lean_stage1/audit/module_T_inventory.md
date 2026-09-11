# Module T source-to-proof inventory

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/T.tex`, read in full. Original source is unchanged.

The primary compact-sublevel theorem is now compiler-checked, including value, solution-set distance, and unique-minimizer iterate convergence. All 22 explicit theorems across the four new `TransportedCertificate*.lean` files were independently axiom-audited; only `propext`, `Classical.choice`, and `Quot.sound` occur. See `audit/module_T_build.log` for build commands, compiler output, axiom reports, and printed exact certificate/eligibility definitions. Global checker integration is performed by the root task.

## Exact primary theorem

For a finite convex real-valued objective with attained minimum, a compact sublevel `K = {F ≤ b}`, `b > F*`, and fixed `0 < c1 < c2 < 1`, assume a certificate on every **nonempty** positive band `Kη = {x ∈ K | F*+η ≤ F(x)}` (`η > 0`). The certificate is a finite matrix field on differentiable band points. Its only matrix regularity is symmetry and positive semidefiniteness; neither continuity, uniform boundedness, fixed rank, nor positive definiteness is assumed.

* Visibility: `gᵀ W(x) g ≥ m > 0` at each differentiable band point.
* Secant: `yᵀ W(z)y ≤ C t`.
* Projected transport: `Πs W(z) Πs ≤ (1+L d) Πs W(x) Πs`, with `L ≥ 0`.
* The last two bounds are quantified only over eligible pairs **whose two endpoints lie in the band**, and only when `d ≤ δ`, for `δ > 0`.
* Eligibility is exactly `d>0`, `c1*d ≤ F(x)-F(z) ≤ d`, `t ≥ (1-c2)*d`, with derivatives at both endpoints, `s=z-x`, `d=-gᵀs`, `y=gz-g`, and `t=yᵀs`.
* Field and constants may depend on the band and on fixed line-search parameters. `C` is merely a real finite constant; replacing it by a nonnegative upper bound in a proof does not strengthen the hypothesis.

Conclusion for every infinite admissible ordinary full-BFGS run starting in K: values converge to `F*`, distance to the solution set tends to zero, and uniqueness implies entire iterate convergence. This does not assert line-search existence at every trial ray.

## Proof obligations and dependencies

| Claim | Required formal dependencies | Current implementation boundary |
|---|---|---|
| Every accepted pair is eligible | Actual step, convex supporting inequality, Armijo, weak Wolfe, derived positive energy | Verified: `accepted_pair_eligible`, with actual pair step/decrease/curvature identities |
| `Mk = Πsk Mk Πsk` | Actual Hessian update, PSD annihilated part, `Mk sk=0`, explicit projector | Verified: `annihilated_projector`, `projected_transport_trace` |
| PSD certificate trace recurrence T.6 | PSD trace monotonicity, actual Hessian update, projected transport, visibility, secant correction | Verified: `certificate_trace_step` |
| Summable predicted decreases and bounded gradients on K | Existing objective-level Armijo and finite-convex compact bounds | Already available Module M inputs |
| Eventual eligibility within a positive band and `d≤δ` | Monotone bounded objective values, derived `d→0`, positive-band choice | Verified inside `transported_certificate_values`; finite limit and small-step tail are derived |
| Value convergence | T.6 and actual Module M reciprocal growth | Verified: `transported_certificate_values`, `transported_certificate_values_on_sublevel` |
| Distance to argmin convergence | Compactness and value convergence, possibly multiple minimizers | Verified in `transported_certificate_convergence_on_sublevel` using `CompactConvergence` |
| Unique-minimizer iterate convergence | Value convergence plus existing localization/unique-minimum theorem | Verified: `transported_certificate_iterates_of_unique_minimizer` and combined sublevel theorem |

## Additional source claims, not silently covered by the primary theorem

1. **Local structural version:** a low initial sublevel stays inside a neighborhood of the unique minimizer (or the entire compact solution set); rejected trials need not stay there. Existing Module M localization covers the unique-minimizer mechanism, but a certificate-local corollary must instantiate it.
2. **One-sided-shell weakening:** certificates only on a one-sided neighborhood of each possible positive limiting level suffice. Exact shell quantifiers need a separate statement and proof.
3. **Rank-one specialization:** `W=vvᵀ`, `v(z)=λv(x)+βs`, `λ²≤1+Ld` gives projected transport. Neither λ invertibility nor a positive lower bound is required.
4. **Bounded-potential rescaling:** multiplier `exp(Ld+Ψ(x)−Ψ(z))` becomes `exp(Ld)` under `W↦exp(Ψ)W`; bounded Ψ preserves visibility/secant constants; small-d gives a linear multiplier. Requires explicit bounds and an exponential estimate.
5. **RS inclusion:** radial `W=(x−x*) (x−x*)ᵀ`, visibility from convexity, secant condition from RS, exact projected transport with L=0. Requires objective-pair RS definition and a formal implication.
6. **Strict separation from RS:** delegated by T to Module Q's curved example; cannot be certified by T's algebra alone.
7. **Perpendicular quadratic characterization:** projected Loewner inequality is equivalent to the quadratic inequality for all `a` with `aᵀs=0`; requires actual projection image/kernel facts.
8. **Affine covariance:** invertible affine coordinate changes send gradients by inverse transpose and certificates by `AWAᵀ`; preserve the three conditions after deriving all transformed pair quantities. No preferred coordinates or matrix-limit assumptions.

## Scope notes

The initial formal field may be represented as a total function `Vec n → Mat n`, with certificate properties required only at differentiable band points. Values elsewhere are unconstrained; total extension imposes no continuity or boundedness condition. The source's finite-valued requirement is represented by ordinary real matrix entries.

The table distinguishes the verified primary chain from secondary claims still open. The primary proof invokes Module M's stronger summable-budget reciprocal theorem instead of the source's arithmetic-mean contradiction; this changes the proof route only, since summability is derived under the same compact-sublevel hypotheses. The source assumption `b > F*` is unnecessary in the exported sublevel theorem, which remains valid when `b ≤ F*`; this is a proved generalization, not an added assumption or weakened conclusion. No objective-pair certificate condition is imposed on rejected trials or on arbitrary chains as if they were BFGS runs.
