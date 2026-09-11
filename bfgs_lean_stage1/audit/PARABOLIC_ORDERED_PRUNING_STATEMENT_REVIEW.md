# Literal ordered/pruned Q envelope: statement review

These four modules separately verify the source's ordered-pruning assertions.
The principal arbitrary-family certificate was already proved through the
normalized compact-cell/ramp construction; it never assumed this reduction.
The present reduction is derived for every original `Parabolic.Family m`.

## Retained indices and actual-objective preservation

`Essential i` means that i is the canonical copy of its coefficient pair
and has a strictly active profile point against every other canonical
pair. `essential_strict_interval` strengthens this to an actual nonempty
open interval, so tie-only pieces are removed. Exact duplicates have one
canonical copy. `essential_same_slope_maximal` proves that any retained
piece has the largest quadratic coefficient among all original pieces
with its slope; `essential_slopes_injective` prevents repeated retained
normal slopes.

The finite set of possible unequal-slope crossings has dense complement.
Off that set, a maximal canonical profile is strictly active. The finite
union of closed active cells is closed, which supplies retained coverage
at every real profile coordinate, including every tie. This argument uses
actual finite affine profiles and ordinary topological theorems; it has
no external cell enumeration or unproved geometry witness.

`exists_essential_active` transfers coverage to every actual point of the
original two-dimensional objective. Division by u² is restricted to u!=0.
The u=0 case follows from closedness and a continuous horizontal
perturbation, not from an assumption about activity or differentiability.
`prunedObjective_eq`, `essential_active_gradient`, and
`prunedFamily_objective/gradient` provide literal objective equality and
preservation of actual differentiable gradients.

Both positive and negative slope witnesses survive, proved at the actual
points (0,1) and (0,-1). `prunedFamily` is therefore an actual input family
with inherited positive quadratic coefficients. Zero normal slopes are
allowed throughout. The finite count is derived; it is not a rank or
genericity assumption.

## Ordered switching geometry

`prunedOrder` sorts the finite image of retained slopes using mathlib's
actual finite order embedding, then recovers their unique retained
indices. Its slope order is strictly monotone and covers all and only the
retained indices. `PrunedOrder.adjacent` derives the absence of intermediate
retained slopes from consecutive finite indices.

For an adjacent pair the actual crossing is
`(a_i-a_j)/(b_j-b_i)`. The denominator is proved positive from slope order.
Both branches are active there, and the actual envelope value is positive
from the original quadratic lower bound. Q.7 follows with the previously
derived calibration constants. `orderedBreakpoint_strictMono` proves full
strict monotonicity of the entire finite sequence of neighbor switching
locations; the index subtype just expresses that the index has a successor.
It is not an assumption that breakpoints are distinct or correctly ordered.

`ordered_pruning_specification` collects the literal source conclusions:
actual objective equality, increasing slopes, increasing switching
locations, activity, positive envelope values, and the exact Q.7 constants.
The switching locations themselves need not be positive. The positive
quantities in the source are the envelope values at those locations.

All 46 explicit declarations, including the derived order structure and
definitions, are covered by the scoped axiom audit. The three expected-type
contracts expose a derived ordered input family, preserved actual
gradients, and the strict order of switching locations. See
`parabolic_ordered_pruning_{build,axioms,contracts,validation}.log`.
