# F:active and F:basin statement review

Canonical source: `report/chapters/families.tex`, lines 51–74. Original sources
remain unchanged. `BfgsVerification/MaxAffineBasin.lean` models an actual finite
nonempty family of affine pieces with arbitrary real slopes and offsets, the
literal finite maximum, and the actual subset active at the reference point.
No distinctness, transversality, strict complementarity, or nondegenerate Hessian
is assumed.

`local_active_identity` proves the exact finite reduction on a neighborhood of
any reference point. `inactive_radius_domination` gives the source's explicit
Euclidean gap/(2*norm(slope difference)) formula for every nonparallel inactive
piece. `parallel_inactive_domination` handles parallel pieces globally without
division by zero. The resulting active slope maximum is proved finite convex
and degree-one homogeneous; component differentiability is not a premise.

The closed convex region where each piece is active is derived from the finite
linear inequalities; activeRegion_convex also exports convexity directly. `badRegion` is the finite union of these closed regions for pieces
inactive at the minimizer. `threshold` is the complete-lattice EReal infimum of
actual objective values over this union. `threshold_eq_inactive_infima` proves
its exact equality to the inactive-index infimum of the region infima. Thus
empty indices and empty regions have value +infinity, with no real-infimum
convention substituted. `exists_min_on_closed` and `threshold_attained` derive
attainment whenever the union is nonempty, from actual compact sublevels.
`threshold_gt_minimum` proves the strict gap using the unique minimizer and its
exclusion from every inactive region.

`local_basin` derives a positive starting-level basin before all actual admissible
full-BFGS runs. `threshold_convergence` proves convergence for every starting
value strictly below the literal extended-real threshold. It chooses a strictly
larger finite level still below that threshold, so the full compact initial
sublevel has an open convex neighborhood where the exact active representation
holds. This discharges, rather than assumes, the neighborhood condition of the
centered smooth-plus-sublinear theorem. The smooth summand is convex and locally
C1,1 on the full space, as stated in this source section. No differentiability
of the max-affine term away from accepted endpoints is imposed.

`threshold_tail_convergence` applies to the actual current tail and its actual
positive matrix when the threshold is entered after a finite prefix. The whole
original sequence then converges. No reset, altered update, or matrix/iterate
convergence premise is inserted. The threshold is sufficient; no converse or
characterization of all successful starts is claimed.

The main unit has 32 explicit theorems and seven concrete definitions, with
actual pinned build and scoped transitive-axiom logs in
`max_affine_basin_build.log` / `max_affine_basin_axioms.log`. Whole-project
integration and source register updates are a separate release gate.
