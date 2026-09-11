# Independent review: exact rational spike oracle

Reviewed all of scratch `NormalSpikeRational.lean` and its explicit target
against U.7.1 and the previously reviewed scalar infinite-series construction.
Snapshot: `rational_source_hashes.json` in `audit/scratch/normal_spike`.
No unresolved mathematical or statement defect was found.

The three algorithms use rational arithmetic, decidable piecewise polynomial
branches, a finite prefix, and exact geometric tails. For every positive query
the proved terminating `Nat.find` search selects a scale below half the query.
The support-width bound then proves that every tail bump is wholly below the
query. The full tail mass is `(64/45)*a_N^2` and the moment is
`(128/105)*a_N^3`, including the selected index; these constants correctly
differ from the source's strictly-smaller-than-a-peak tail. All prefix terms,
including a possible partial bump, are evaluated by the exact splines.

The real-cast identities are proved for every spline branch and all boundary
queries. The resulting three outputs equal the integral-defined source
function, its actual first derivative and its actual second derivative at
every rational query. The finite density prefix accounts for the whole second
derivative because all tail densities vanish at the query. Nonpositive queries
are handled separately, with the previously checked actual second derivative
at zero. The proof does not infer derivative existence from the default value
of Lean's total derivative operator.

The reviewed source has no `noncomputable` declaration or floating-point
operation. Real limit arguments prove termination and correctness, while the
program itself operates on decidable rational comparisons. No external
evaluation supplies mathematical evidence. The scoped certificate records
32 declarations, standard transitive axioms, one exact target and an unchanged
source hash; its structural check was independently rerun during review.

This closes the rational-valued-query corollary omitted from the earlier
nine-module scalar target. It verifies the Lean rational algorithms. It does
not assert correspondence with the separate experimental Python program or
verification of recorded numerical BFGS experiments, as the source mapping
correctly states.
