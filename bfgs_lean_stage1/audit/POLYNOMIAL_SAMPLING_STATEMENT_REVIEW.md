# Actual all-real polynomial sign sampling

This six-file, 29-declaration scratch tranche implements the root/critical-point/tail sampling step of the general Module A projection plan. It follows the reviewed finite sign-inversion tranche. Its final import is `PolynomialSamplingTargets`. No main source is changed while milestone14 is frozen.

## Constructed finite sample set

For an arbitrary finite family q_i of real univariate polynomials, `nonzeroFamilyProduct` is the actual product of exactly those q_i that are nonzero polynomials. The empty product is one, and its nonvanishing is proved. Its actual distinct real roots are proved equal to the union of the original family's root boundaries. Zero queried polynomials therefore remain in the requested sign vector while contributing no spurious boundary.

For any finite boundary B, `signSampleRadius B=1+sum_{b in B}|b|` is strictly positive and strictly exceeds the absolute value of every boundary member. Thus its positive and negative values are actual tail points outside the boundary, with respectively full and empty cut profiles.

`polynomialSignSamples P` is the explicit finite union of the actual distinct roots of P, the actual distinct roots of P', and these two tail points for P's root boundary. No ordering, gap, critical sample, or coverage oracle is assumed. The proof selects the greatest boundary point below x and the least boundary point above x when both exist, proves their whole open gap root-free with the same cut profile, and applies actual Rolle's theorem to P on that interval. The resulting derivative root has the same profile as x. The nonzero derivative polynomial needed to include this root in its actual root list is derived from P≠0 and an actual real root. If P'=0, there is no bounded gap requiring such a sample. The other two cases use the explicit tails. If x itself is a root, x is already a sample.

The existing actual polynomial sign-constancy theorem transfers all original branch signs on a root-free profile. Consequently every x has one sample with exactly the same entire sign vector. The equivalence `exists_family_signs_iff_sample` preserves a single common witness; it never combines separately realized signs.

## Literal tail signs and finite queries

The imported generic `polynomial_sign_atTop` and `polynomial_sign_atBot` are actual polynomial asymptotic sign theorems. They include zero and constant polynomials. A point farther into the same root-free tail is selected from each eventual sign statement, and exact profile constancy transfers its sign to the fixed explicit sample. Therefore the right sample has the sign of the actual leading coefficient, and the left sample has that sign multiplied by (−1) raised to the actual degree. The sample radius was fixed by the whole original family before all these identities; it is not reselected separately for each sign query.

`signQueryExpression` is the actual rational linear combination of the 3^m actual Tarski queries from the reviewed finite inversion. Its positivity is proved equivalent to an actual root-list witness. The final `exists_real_sign_pattern_iff_queries_and_tails` reduces existence anywhere on R to the disjunction of: positivity of the root-product query expression, positivity of the derivative-product query expression, the exact left coefficient/parity sign vector, or the exact right coefficient sign vector. The product and derivative in both queries are actual polynomials. No root-count or query-value oracle is an assumption.

## Exceptional cases and scope boundary

No nonzero queried polynomial, positive family size, simple-root, squarefree, fixed-degree, nonzero-derivative, or genericity hypothesis is present in the final theorem. The product is made nonzero by its literal definition and proof. Its derivative may be zero; that polynomial's actual root list and query expression are empty/zero, so it contributes no false root witness. Empty families have product one and vacuous tail tests, correctly realizing their unique empty pattern. Repeated roots are handled by distinct-root lists, exactly as in the actual Tarski-query definition.

This is a fixed-fiber identity for arbitrary real polynomial coefficients. It is not yet a quantifier-free parameter formula or general semialgebraic projection theorem. The remaining algorithm must calculate the query values by signed remainder/index identities and construct finite parameter branches that handle nullification and degree changes. It must then convert Boolean formulas and prove the general projection and path theorems needed by Module A. Those obligations are not assumed or renamed here.

## Evidence and exact contracts

The three exact targets are `FinitePolynomialSignSamplingTarget`, `PolynomialTailSamplesTarget`, and `RealPolynomialSignReductionTarget`, with wrappers `finitePolynomialSignSampling`, `polynomialTailSamples`, and `realPolynomialSignReduction`. There are five strict source-theorem/wrapper comparisons (both source and wrapper for the first and third; the joint tail wrapper for the second).

The frozen manifest `declarations.json` contains six owned source hashes and eleven immutable dependency source hashes: six root-sign/index files, the generic polynomial infinity-sign file, and four finite sign-inversion files. Run `bash audit/scratch/polynomial_sampling/verify.sh`. It rebuilds all eleven dependencies into this tranche's own `dependencies/` directory, builds the six owned modules, checks all 29 actual declaration types and transitive axioms, checks the five exact comparisons, and validates every source hash. Other agents' sources and logs are not modified. Only propext, Classical.choice, and Quot.sound are permitted.
