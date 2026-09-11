# Boundary signs: actual finite semialgebraic refinement

The two frozen files prove ten declarations, with one exact joint contract and two strict source/wrapper comparisons. Reproduce with `bash audit/scratch/boundary_sign_strata/verify.sh` from the Lean project.

For arbitrary finite polynomial family `P : Fin m → MvPolynomial (Option (Fin n)) ℝ`, arbitrary real boundary functions `f : Fin r → Vec n → ℝ`, and base `S`, the literal stratum `boundarySignStratum P f S ω` consists of the points of `S` where every actual value `parameterEval (P j) (x, f i x)` has the prescribed sign `ω j i`.

The hypotheses are only actual semialgebraicity of the base and of each restricted boundary graph. Every individual sign fiber is proved semialgebraic by intersecting that actual graph with the literal polynomial sign condition and applying the already proved scalar projection theorem. Two finite universal intersections then give the stratum. This uses no sign-query oracle or assumed projection closure.

The strata are pairwise disjoint and their union is exactly `S`; the actual sign array at any base point supplies its witness. Since `Fin m → Fin r → SignType` is a finite type, this is a finite partition. Empty bases, `m = 0`, `r = 0`, arbitrary degrees, identically zero polynomials, repeated roots, and coincident/unordered boundary functions are all permitted. Base semialgebraicity is retained explicitly because empty boundary or polynomial families cannot imply it from the other hypotheses.

Every boundary graph restricted to a stratum remains semialgebraic by intersection. Every actual point on that restricted graph has the prescribed sign for every input polynomial. The exact `BoundarySignPartitionTarget` includes all five conclusions for the same literal strata and original boundary functions.

This is a dimension-induction ingredient. It does not assert that strata are connected or smooth, that boundaries are roots, or that a complete polynomial cell decomposition has already been built. Those properties must be supplied by the separately proved root-chart and lower-dimensional-cover steps. No new assumptions are made about smoothness, ordering, root membership, degree, or genericity.

Source hashes, actual compiler logs, complete transitive axiom reports, and exact target checks are recorded by the delivered validator. Original research and shared root audit files are unchanged.
