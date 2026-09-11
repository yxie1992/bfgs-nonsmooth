# Independent H recurrent-cardinality sharpness review

Reviewed the complete frozen `SeedRecurrentRank.lean` (seven explicit declarations), its actual-run dependencies, exact target, and H.tex lines410–415. No mathematical or statement defect was found. The target is the concrete rank-two sharpness example, not a new claim that every rank is attained or that a general many-piece run finitely terminates.

Every actual phase recurs arbitrarily late, by the explicit index 3N+j. The reverse inclusion uses the actual run gradient range, so the recurrent set is proved equal to the actual three-slope image; it is not supplied as an alphabet assumption. The first coordinate bounds distinguish the algebraic third slope from both first slopes, proving actual injectivity and therefore cardinality three, without identifying potentially coincident entries.

The first two literal slopes (1,0) and (-1,-1/8) span every vector v through coefficients v[0]-8v[1] and -8v[1]. The proof places both in the actual recurrent span, obtaining the whole plane and actual real finrank two. Thus cardinality equals rank plus one. No assumed matrix limit, rank, or abstract recurrence hypothesis appears in the final contract.

The final theorem uses the existing actual unmodified full-BFGS seed run for every source choice 0<c1<=1/3 and c1<c2<1. Initial identity, actual iterates and finite objective limit zero, strictly positive values, and actual nonstationarity of the limit are inherited from the proved source run. That run's objective is the finite convex homogeneous three-piece maximum and is not lower bounded globally. This is precisely the source's stagnation sharpness example, and it does not purport to provide a coercive sharpness theorem.

Fresh independent checking uses `peer_axioms_contract.log`: all seven actual declaration types and transitive axiom reports plus the strict target check. `peer_validation.log` records the manifest hash and standard-axiom checks. Only propext, Classical.choice, and Quot.sound are allowed; the proof source was not edited.
