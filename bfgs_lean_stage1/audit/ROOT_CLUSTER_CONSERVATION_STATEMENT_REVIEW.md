# Finite root-cluster conservation infrastructure

This is a finite combinatorial prerequisite, with no assumed or asserted polynomial projection, root continuity or semialgebraic decomposition. The main API uses arbitrary finite sets `s` and `t`, a label map `c`, natural-number point weights `w`, and natural-number capacities `m`.

`fiberWeight s c w b` is the actual finite sum of weights of members of `s` mapped to `b`. If every point maps into `t`, every fiber weight is at most its capacity, and the total point weight equals the total capacity, every fiber weight equals its capacity. This follows from the exact finite fiberwise sum identity and equality of sums under termwise inequalities.

Positive capacities then imply each fiber is nonempty. If `s.card=t.card`, the induced map between the actual finite subtypes is surjective and therefore bijective. The public conclusions are actual `Set.BijOn` for the original map, singleton filtered fibers and equality of each sole point weight to its cluster capacity. The subtype cardinality argument is internal; applying the finite-set results does not require converting the user's weighted sums to subtype sums.

Natural weights are automatically nonnegative. The core theorem deliberately permits zero weights, proving a stronger result than the intended positive-multiplicity application; the equal-cardinality conclusion forces each sole weight to equal a positive capacity. No positive-weight premise is silently consumed. Empty alphabets are handled without a nonempty premise: positive capacities and conservation exclude missing nonempty target fibers; when both alphabets are empty the exact statements are vacuous and the empty map is bijective.

`fintype_bijective_and_weights` supplies the ordinary arbitrary-Fintype formulation. The two separate strict infrastructure contracts instantiate arbitrary finite cardinalities `n,m`, retaining the same exact conservation/bijection conclusions. They do not claim actual polynomial clustering; the analytic root bounds and multiplicity estimates must separately discharge the mapping, capacity and total-weight hypotheses.

`verify.sh` freshly compiles the two frozen modules and checks every explicit declaration's actual type and standard transitive axioms, both exact contract types, and the two source hashes. No mathematical computation outside Lean is used.
