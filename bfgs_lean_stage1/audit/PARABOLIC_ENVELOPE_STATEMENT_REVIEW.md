# Parabolic envelope calibration: statement and dependency review

Reviewed source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/Q.tex`, Q.7,
Q.8, and Q.16. The original research source is unchanged.

## Verified statements

All five `ParabolicEnvelope*.lean` modules quantify over the original
`Parabolic.Family m`: every `a_i` is positive and the finite family contains
one negative and one positive `b_i`. No envelope regularity, nonredundancy,
nonzero individual slope, or calibration witness is an input hypothesis.

* `calibration_active_eq` matches the original-index exponents at every
  positive-level active tie. `calibration_interface_identity` gives Q.7 at
  every common active interface `(1,xi)`; positivity of its denominator is
  derived from the actual objective's quadratic lower bound.
* `exists_calibration_deficit_bound` proves Q.16 with one positive finite
  constant for every original pair of indices and every positive-level
  point where the second index is active. Activity of the first index at
  another endpoint, adjacency, and differentiability are unnecessary.
* `calibratedScale` is defined without selecting an active index.
  `calibratedScale_eq_active` supplies the exact Q.8 exponent at each active
  index; `log_calibratedScale` exposes the exponent. Its positivity is
  unconditional, its continuity is proved on `{F > 0}`, and
  `calibratedScale_uniform_bounds` provides global positive lower and upper
  bounds on that set. No continuity at the minimizer is claimed.

The two expected-type examples in `PARABOLIC_ENVELOPE_CONTRACTS.lean`
check the existence of the actual constants and scale directly from an
arbitrary original family. They contain no retained-index or cell premise.

## Constructive replacement for sorting and pruning

The formal proof uses the normalized coordinate `v/F` and the affine
functions `T_i(v) = (1-b_i*v)/a_i`. A cell is the set where `T_i` is minimal
among these functions on a compact interval bounded using the two signed
slope witnesses. This interval may be wider than the feasible normalized
arc, and these cells do not impose `T_i >= 0`. That choice is harmless:
`active_normalized_cell` derives membership for every actual positive-level
active point, including normalized quadratic coordinate zero. Final results
specialize only to such actual points.

Each nonempty cell is proved to be a closed interval. Exact duplicate
coefficient pairs use their least original index as canonical representative.
Distinct canonical cells intersect in at most one point. A finite sum of
clipped ramps, weighted by `-b_i/2`, consequently has exactly this slope on
each cell. The calibration constants are its offsets from `a_i*T_i/2`.

Empty cells are omitted, with their inability to contain actual active
points proved. Singleton cells remain and have zero-length ramps. Equal
positive-length cells are counted exactly once. `active_retained_representative`
proves actual active coverage and preservation of the explicit branch
gradient. Thus exact duplicates, tie-only pieces, and triple ties do not
require a source-side regularity assumption. The construction yields the
source's calibration and finite-cell conclusions directly; it does not
claim to formalize the source's particular ordered-pruning algorithm.

For Q.16, the deficit and exponent discrepancy are affine on each cell.
The deficit is nonnegative, and every zero is proved to be a common active
tie where the discrepancy is zero. `Envelope.affine_deficit_bound` proves
the ratio bound from endpoint interpolation, including zero endpoints and
singleton intervals. A finite sum of the resulting positive constants
gives the uniform bound. No unproved computation or geometric cell witness
enters the argument.

## Boundary and dependency checks

The proof never divides by `u`, by a general `b_i`, or by the normalized
quadratic coordinate. It divides by the two selected slope witnesses only
after proving their signs, by `a_i > 0`, and by an actual value `F > 0`.
Hence `u = 0`, zero-slope branches, and ties at normalized quadratic
coordinate zero are included. The two signed witnesses already imply the
necessary finite-family nonemptiness; no hidden inhabited hypothesis is
added to the final theorems.

All 70 declarations were included in the scoped transitive axiom audit.
Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The actual pinned compiler output and expected-type output are retained in
`parabolic_envelope_axioms.log` and `parabolic_envelope_contracts.log`.
The sources contain no `sorry`, `admit`, custom axiom, `native_decide`, or
unchecked external calculation.

This tranche verifies calibration, the scale, and Q.16. Q.15--Q.17
quantitative transport, the assembled objective-pair certificate, actual
run convergence, and the explicit three-branch RS separation belong to
separate modules and are not claimed by this scoped review.
