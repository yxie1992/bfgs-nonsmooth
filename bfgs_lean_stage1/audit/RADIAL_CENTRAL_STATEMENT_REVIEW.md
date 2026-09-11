# Radial central-difference local equivalence

The derivative-free claim in Module R (`R.tex:130–155`) is now compiler-checked in `RadialCentralDifference.lean`. The scope is explicitly local in the upper sublevel. No outward coverage beyond the structural region is asserted, and the original research source is unchanged.

## Exact definition and statements

`centralDifference F star x t` is the actual expression

`F(star+(1+t)(x−star)) + F(star+(1−t)(x−star)) − 2F(x)`.

`HasNestedCentralBounds F star b` means: for every positive η there are finite C and `0<θ≤1/2` such that, for every center x and `0≤t≤θ`, the central difference is at most `C t²` whenever the **outer** sample satisfies `F≤b` and the **inner** sample satisfies `F≥Fstar+η`. No point in this definition is required to be differentiable. Convexity and the minimum order these radial points, so the whole triple then lies in the specified upper sublevel and positive band.

This precise predicate expresses the source's “slightly nested positive bands where both dilations remain in K.” The threshold may depend on the positive band. It does not silently require a central bound at an outer point outside K.

Verified exports:

- `central_difference_le_five_of_pair_radial`: exact `centralDifference≤5 C t²` for actual differentiable outer/middle/inner triples, given the same constant C for the two relevant RS pair bounds. The outward remainder is at most `Ct²`; the inward remainder is at most `4Ct²`. Both zero-curvature and t=0 cases are covered.
- `central_of_radial_on_sublevel`: RS on the original `{F≤b}`, with `Fstar<b`, implies `HasNestedCentralBounds` on that same upper sublevel. This forward implication even needs no compactness once the RS constants are supplied. It selects the RS constant at η/2, replaces it by a nonnegative upper constant, and obtains a central constant `5 max(C,0)` with `θ=1/2`.
- `inward_of_central_on_smaller_sublevel`: central bounds on compact `{F≤b}` imply the exact IR predicate on **every strictly smaller** upper sublevel `{F≤b′}`, `b′<b`.
- `radial_of_central_on_smaller_sublevel`: the same local converse to RS, using the already-proved IR→RS theorem.
- `local_radial_iff_nested_central`: existence of a positive compact structural sublevel carrying RS is equivalent to existence of one carrying the derivative-free nested central condition. The reverse direction explicitly chooses `b′=(Fstar+b)/2`. This is the source local equivalence, not a claim that an outward probe at the original top boundary remains in K.

## Derivative removal and domain checks

Joint differentiability of all three sampled points is derived by applying Rademacher to F and its two actual affine compositions. Their three full-measure sets are intersected before concluding density; explicit inverse homotheties recover the endpoint derivatives. There is no assumed gradient continuity and no unproved intersection-of-dense-sets argument.

For fixed t, the approximation is performed in the positive sublevel of the composed finite convex function `w↦F(outwardPoint star w t)`. This keeps the **outer** approximating sample in the original K even if the target outer sample is on its boundary. An open lower-value margin preserves the inner η/2-band. Convexity and the minimum keep the remaining two endpoints in K and order the RS pairs. All approximate gradients are coordinates of actual derivatives. Only function-value continuity is needed to pass the central inequality to the limit, so all three limiting points may be nonsmooth.

The reverse direction shrinks the upper level. To obtain one uniform allowed outward fraction on the smaller compact sublevel, it bounds the continuous function `x↦F(2x−star)` there and applies convexity between x and `2x−star`. This may evaluate F outside the structural region, which is permitted because F is finite convex everywhere; **no RS or central hypothesis is imposed outside the original K**. The lower-band margin follows from the existing outer supporting-plane estimate. Both restrictions and the original central threshold are combined into one positive θ chosen before x,g,t.

The direct identity expressing the central difference as the sum of the two supporting remainders proves that it bounds each remainder at a differentiable center. Thus the converse introduces no derivative assumptions at the sampled inner or outer points.

## Compiler and axiom evidence

All 19 declarations in this file, including the function-value and nested-band definitions, have been individually checked for transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` occur; there are no placeholders, custom mathematical axioms, or unchecked computations.

- `audit/radial_central_build.log`: actual compiler-feedback history, ending with a successful pinned build.
- `audit/RADIAL_CENTRAL_AXIOMS.lean`: reproducible all-declaration statement and axiom query.
- `audit/radial_central_axioms.log`: exact elaborated theorem statements, printed definitions, and transitive axiom output.
- `audit/radial_central_validation.log`: declaration count and allowed-axiom validation.

Reproduce from the project directory:

```bash
source scripts/env.sh
lake build BfgsVerification.RadialCentralDifference
lake env lean audit/RADIAL_CENTRAL_AXIOMS.lean
```

This completes the stated local central-difference equivalence. The later piecewise-smooth, gauge-power, smooth-max, and spectral-family claims remain distinct report obligations.
