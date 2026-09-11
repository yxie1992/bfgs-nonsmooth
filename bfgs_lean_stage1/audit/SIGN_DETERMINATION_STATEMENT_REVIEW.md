# Finite simultaneous sign determination from actual Tarski queries

This four-file, 34-declaration scratch tranche implements the finite combinatorial inversion in step 3 of `audit/scratch/general_semialgebraic/GENERAL_PROJECTION_PATH_PLAN.md`. It supports the outstanding general Module A semialgebraic proof. It does not establish global polynomial projection, finite path decomposition, or the final affine-critical-value gap by itself. Main milestone14 sources remain untouched.

## Actual coefficients and finite identity

`signIndicatorCoeff` is an explicit rational coefficient table for the three indicator polynomials on signs: the zero indicator is 1−s², the positive indicator is (s²+s)/2, and the negative indicator is (s²−s)/2. `sign_indicator_identity` proves all nine sign cases. The proof uses exact rational arithmetic and kernel-checked finite constructor inequalities; no native decision procedure or numerical inverse is used.

`signPatternCoeff` is the actual product of these scalar coefficients. `sign_pattern_indicator` expands a finite product of sums with the proved `Fintype.prod_sum` identity and derives the exact simultaneous indicator. The exponent index type is `Fin m → Fin 3`; its actual cardinality is proved to be 3^m.

For any actual finite set S and any assignment of sign vectors to its elements, `finite_sign_count_from_moments` expresses the actual filtered-set cardinality as the explicit rational linear combination of power moments. The count is for a single complete sign vector at each common element. It does not combine separate witnesses for different atoms. The empty pattern and empty set are included. Equality of all moments determines every sign count.

## Actual polynomial/root/query bridge

`signQueryPolynomial q e` is the actual product of q_i raised to exponents e_i in {0,1,2}. The actual polynomial evaluation, multiplicativity of the sign map, compatibility of integer and rational sign casts, and finite sum identities prove that each root sign moment equals the integer-valued `tarskiQuery` cast to Q. The imported `tarskiQuery` is the actual sum of signs on `p.roots.toFinset`, not an assumed query oracle or sign table.

`root_sign_count_from_tarskiQueries` therefore returns the exact rational reconstruction formula for the cardinality of the actual filtered distinct-root set. `root_sign_counts_eq_of_queries_eq` allows different root polynomials, degrees, multiplicities, and branch families, provided their actual finite query vectors agree. The count and recovered expression are proved nonnegative and bounded by the actual polynomial degree.

`exists_root_sign_pattern_iff_query_positive` proves an actual existential statement: one real a satisfies p(a)=0 and every requested branch sign exactly when the displayed query expression is positive. It has the necessary hypothesis p≠0. No simplicity, squarefreeness, genericity, fixed degree, nonvanishing branch values, or distinctness of branch polynomials is assumed. Repeated roots contribute once, matching the actual Tarski-query definition.

## Zero and empty cases

The actual mathlib root multiset of the zero polynomial is empty. The counting/reconstruction identities hold under that explicit finite-list convention, and `rootSignCount_zero_polynomial` exports it. They do not identify that empty list with the zero polynomial's complete real zero set. The actual-real-root existential theorem explicitly requires p≠0; omitting this condition would be false. An identically zero root polynomial remains a separate terminal case of the future global projection algorithm.

The m=0 pattern is empty and unique, its count is exactly the distinct-root cardinality, its query polynomial is 1, and its coefficient is 1. Consequently the construction retains root existence for nonzero p in the empty-pattern case. No positive m or nonempty queried family is silently imposed.

## Contracts, dependencies and reproduction

The exact targets are `BfgsVerification.RootSignReconstructionTarget`, `SimultaneousRootSignsTarget`, and `SignQueryDeterminationTarget`, with wrappers `rootSignReconstruction`, `simultaneousRootSigns`, and `signQueryDetermination`. The audit strictly compares both each source theorem and its wrapper with its corresponding target.

The frozen manifest is `declarations.json`; it includes four owned source hashes and six immutable root-sign/index dependency hashes supplied by armijo. Run `bash audit/scratch/sign_determination/verify.sh`. This rebuilds those dependency sources into this tranche's own `dependencies/` directory, then builds the four owned modules, checks all 34 type/transitive-axiom reports and six strict contract comparisons, and validates all ten hashes. It does not modify another agent's source or audit logs. Only propext, Classical.choice, and Quot.sound are allowed in transitive dependencies.

The remaining general algorithm must compute the actual queries through signed remainder/index identities and construct finite parameter decision trees, then cover intervals as well as roots and establish general Boolean projection. Those mathematical obligations are not hidden in or relabeled by the present finite inversion theorem.
