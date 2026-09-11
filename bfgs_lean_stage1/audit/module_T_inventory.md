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

## Secondary T claims and Module G normalization

The following additions compile in `TransportedNormalization.lean` and `TransportedCertificateVariants.lean`. All 31 declarations (including certificate-producing definitions, not just named theorems) are independently checked for transitive axiom dependencies in `audit/module_T_variants_axioms.lean`; the output is `audit/module_T_variants_axioms.log`. Only `propext`, `Classical.choice`, and `Quot.sound` occur. `audit/module_T_variants_build.log` retains actual compiler-feedback history and ends with a successful build.

| Source claim | Verified declaration and exact scope |
|---|---|
| Rank-one scalar transport | `rank_one_transport`, `rankOneCertificate`: actual `W=vvᵀ`; transport scalar may be zero; no invertibility, fixed-rank, continuity, or lower scalar bound. All small eligible-pair quantifiers remain exact. |
| Bounded-potential absorption | `PotentialBandCertificate.absorb`: exact multiplier `exp(Ld+Ψ(x)−Ψ(z))`; arbitrary band-bounded Ψ; field becomes `exp(Ψ(x)) W(x)`. Proved constants are `m′=exp(ψlo)m`, `C′=exp(ψhi)max(C,0)`, `L′=2L`, `δ′=min(δ,1/(L+1))`. Inner field remains unconstrained except source PSD. |
| Exact L=0 normalization (Module G) | `BandCertificate.normalize`, `normalize_field`, `normalize_budget`, `hasBandCertificates_iff_zero_budget`: field exactly `exp((L/c1)(F(x)−F*)) W(x)`. The original δ is retained. The sole bound needed is the original upper value bound `F≤b`; no uniform W bound. Both existential directions are verified. |
| RS inclusion | `radial_implies_band_certificates`: root `HasRadialSecantBounds` implies the exact T predicate with radial field, `m=η²`, and `L=0`. Convexity provides visibility, and the original positive-curvature RS condition is applied to eligible pairs using derived curvature positivity. |
| Structural-region restriction | `BandCertificate.restrict`, `hasBandCertificates_restrict`: same field and constants on a subset. This covers a specified initial compact sublevel contained in the structural region, also with multiple minimizers. |
| Local basin | `local_transported_certificate_basin`: certificates only on the intersection of original sublevel K and minimizer neighborhood U. A positive initial gap is chosen before quantifying over every actual admissible run and hence every SPD initialization. Accepted iterates are proved to stay in K∩U. `..._on_neighborhood` is an additional simpler specialization. |
| One-sided-shell weakening | `HasShellCertificates`, `transported_shell_certificate_values`, `transported_shell_certificate_convergence_on_sublevel`: a separate ε and certificate for each possible positive finite limiting level; the matrix conditions apply only inside `ell≤F≤ell+ε`. The actual objective limit, eventual shell membership, and eventual small decrease are derived; values, distance to argmin, and unique-minimizer iterates all converge. |
| Perpendicular quadratic characterization | `projected_transport_iff_perpendicular`: exact equivalence for symmetric field values between the projected PSD difference and quadratic comparison for every vector perpendicular to the step. Actual Euclidean projector algebra includes dimension zero and even zero step. |

Remaining T obligations are explicit:

1. **Strict separation from RS:** Module Q must supply its complete curved objective certificate and RS failure. No such separation follows from the T algebra alone.
2. **Compact nonunique solution-set neighborhood:** the direct structural-sublevel restriction is proved, but deriving a uniform low basin from an open neighborhood of the entire compact minimizer set still needs an explicit theorem. The current neighborhood-basin exports assume uniqueness.
3. **Affine covariance:** derive transformed objective derivatives, accepted-pair quantities, field congruence, and the transport equivalence under every invertible affine coordinate change. The perpendicular characterization is now available but the whole coordinate-change theorem is not yet formalized.

Reproduce this secondary milestone from the project directory with the pinned toolchain:

```bash
source scripts/env.sh
lake build BfgsVerification.TransportedCertificateVariants
lake env lean audit/module_T_variants_axioms.lean
```

## Scope notes

The initial formal field may be represented as a total function `Vec n → Mat n`, with certificate properties required only at differentiable band points. Values elsewhere are unconstrained; total extension imposes no continuity or boundedness condition. The source's finite-valued requirement is represented by ordinary real matrix entries.

The table distinguishes the verified primary chain from secondary claims still open. The primary proof invokes Module M's stronger summable-budget reciprocal theorem instead of the source's arithmetic-mean contradiction; this changes the proof route only, since summability is derived under the same compact-sublevel hypotheses. The source assumption `b > F*` is unnecessary in the exported sublevel theorem, which remains valid when `b ≤ F*`; this is a proved generalization, not an added assumption or weakened conclusion. No objective-pair certificate condition is imposed on rejected trials or on arbitrary chains as if they were BFGS runs.

The third tranche completes the nonunique entire-solution-set neighborhood-to-basin deduction in CompactSolutionBasin.lean. Affine covariance and Q strict separation remain open.
