# Completed reverse radial equivalence: statement and dependency review

The complete reverse half of Module R, R:thm:equiv, is now compiler-checked. The final equivalence is `BfgsVerification.RadialCertificate.radial_iff_inward_on_compact_sublevel` in `RadialReverse.lean`. This replaces the earlier *remaining obligation*; it does not reinterpret the earlier both-differentiable pair estimate as a full proof.

## Exact hypotheses and conclusion

The theorem assumes exactly the source finite convex objective, an attained global minimum at star, and compact positive sublevel `K={x | F x≤b}` with `F star<b`. It concludes equivalence between the existing `HasRadialSecantBounds F K star` and `HasInwardTaylorBounds F K star` on that **same K**.

The predicates have been printed into `audit/radial_reverse_axioms.log` beside the exact elaborated theorem statements:

- RS uses each positive band, two actual differentiable endpoints, `F star+η≤F z≤F x`, both endpoints in K, and positive actual secant curvature. Its constant may depend on η.
- IR uses each positive band and a differentiable outer x in K, with all fractional inward steps `0≤t≤θ`, `0<θ≤1/2`. Its conclusion is the two-sided Taylor-error inequality. **There is no derivative hypothesis at the inward point.**
- Both predicates impose only vacuous pointwise obligations on empty bands. No nonempty-band, rank, dimension-positivity, unique-minimizer, gradient-continuity, or enlarged-domain assumption was added.
- `inward_iff_intercept_on_compact_sublevel` additionally combines the now-complete RS↔IR theorem with the previously verified same-domain RS↔SP theorem.

## Proof-chain review

1. `gradientFunctional_coordinates` proves that every actual continuous linear derivative functional is represented by the stated Euclidean dot product. The selected vectors are coordinates of `fderiv`, and `hasFDerivAt_coordinateGradient` proves they are actual gradients wherever differentiability is known.
2. `convex_ae_differentiable` derives local Lipschitz bounds on natural-number balls from finite convexity and continuity, then invokes mathlib's kernel-checked Rademacher theorem. A countable intersection gives full-space almost-everywhere differentiability. The canonical measure on `Fin n→ℝ` provides the Haar and positive-open-set instances; dimension zero is allowed.
3. For fixed `t≠1`, both F and its composition with the actual affine homothety are finite convex functions. Their almost-everywhere differentiability properties are intersected, then the explicit differentiable inverse homothety proves differentiability at the inner endpoint. The intersection is proved full measure before concluding density; the proof never assumes arbitrary dense sets have dense intersection.
4. `exists_inward_pair_approximation` works on the exact original sublevel. Continuity and `F star<b` place star in its interior; closed convexity makes the sublevel the closure of its interior. The chosen sequence stays in the interior, in any specified open condition true at x, and in the joint differentiability set. This handles x on the top boundary without enlarging the sublevel.
5. The original outer supporting plane and the derived Euclidean gradient/radius bounds give the source margin `F(inward x t)≥Fstar+3η/4`. This needs no derivative at the inner point. Continuity then permits approximation inside the open condition `F(inward w t)>Fstar+η/2`.
6. The minimum and convexity order every approximating inward pair, so both endpoints remain in K. Their gradients are actual derivative coordinates. RS at η/2 yields the existing paired bound, including zero-curvature cases handled by `inward_error_le_of_pair_radial`.
7. The outer approximating gradients converge to the given derivative at x by the previously proved `convex_gradients_tendsto_at_differentiable`. Inner-gradient convergence is never required. Continuous function values and dot products pass the uniform error estimate to the limit, removing the inner differentiability restriction.

The proof chooses the source `θ=min(1/2,η/(4GR))` and `M=8C′`, where `C′=max(C_{η/2},0)`. The maximum simply selects a nonnegative upper constant from the source finite real constant; it does not strengthen RS. All constants are chosen before the universally quantified x, g, and t. The t=0 case is proved directly.

No mathematical correction to the research statement was necessary. The alternative use of the outer supporting plane for the value margin and of Rademacher on a composed convex function for joint density changes the proof route only. Full-dimensional interior follows from the source strict upper-level gap; it is not assumed independently.

## Actual build and axiom evidence

New files and declaration counts:

| File | Audited declarations |
|---|---:|
| `ConvexDifferentiability.lean` | 7 |
| `RadialApproximation.lean` | 8 |
| `RadialReverse.lean` | 3 |

The actual compiler history is retained in `audit/radial_reverse_build.log`, ending in a successful pinned-toolchain build. The scoped heartbeat increase on the long reverse theorem changes elaboration resources only; all resulting proof terms are checked normally by Lean's kernel.

All 18 declarations, including the coordinate-gradient definition and all auxiliary approximation theorems, were independently queried with `#print axioms`. Only `propext`, `Classical.choice`, and `Quot.sound` occur. There are no sorry/admit dependencies, custom mathematical axioms, or unchecked computations. Exact statements, predicate definitions, and transitive axiom reports are in `audit/radial_reverse_axioms.log`; the reproducible audit source is `audit/RADIAL_REVERSE_AXIOMS.lean`. The validation count and allowed-axiom summary are in `audit/radial_reverse_validation.log`.

Reproduce from the Lean project with the pinned environment:

```bash
source scripts/env.sh
lake build BfgsVerification.RadialReverse
lake env lean audit/RADIAL_REVERSE_AXIOMS.lean
```

This milestone completes the full RS↔IR claim and its combination with SP. The later derivative-free central-difference formulation and structural-family claims are distinct report obligations; no completion claim for those follows merely from this equivalence.

Subsequent milestone: the separate local central-difference obligation mentioned above is now proved in RadialCentralDifference.lean; see RADIAL_CENTRAL_STATEMENT_REVIEW.md for its explicitly nested upper/lower band scope.
