# Arbitrary-degree positive pseudo-division and finite root remainders

This frozen six-file, 26-declaration tranche implements the first general-degree algebra stage of `audit/scratch/general_semialgebraic/GENERAL_PROJECTION_PATH_PLAN.md`. It is not restricted to quadratic polynomials or simple roots. It does not yet prove Sturm–Tarski root counts, simultaneous sign determination, arbitrary Boolean projection, or Module A's final semialgebraic gap theorem.

## Actual pseudo-division

`PositivePseudoDivision` works over an arbitrary commutative integral domain. Its leading-term cancellation is a concrete polynomial expression. Both terms have the same actual degree and leading coefficient; `Polynomial.degree_sub_lt` proves strict degree decrease. Strong induction on the actual dividend degree, with a separate zero-polynomial branch, constructs k,Q,r with `C(lc q)^k*p=q*Q+r`, where r is zero or has actual degree smaller than q. No monicity or field division is assumed. Constant nonzero divisors are included and force zero remainder.

Multiplying the identity by the same leading-coefficient power gives `C(lc q)^(2*k)*p=q*Q'+r'`; scalar polynomial multiplication does not increase remainder degree. This even exponent is deliberate. Under every real specialization where the actual leading coefficient is nonzero, its multiplier is strictly positive, independently of the coefficient's sign.

## Exact specialization and exceptional branches

`PositivePseudoSpecialization` applies an actual ring homomorphism to the entire polynomial identity. At every actual root of the specialized divisor, the specialized remainder equals the positive multiplier times the actual dividend value. It proves equality-to-zero, strict-positive and nonnegative tests equivalent in both directions. The specialized divisor retains its symbolic degree when the leading coefficient is nonzero; the remainder degree can only decrease. Both conditions are derived from actual coefficient/map theorems.

`LeadingCoefficientStrata` handles the exceptional branch. If the actual leading coefficient specializes to zero, erasing that symbolic leading term preserves the complete specialized polynomial exactly and lowers the symbolic degree strictly. For polynomial parameter coefficients, the zero and nonzero leading-coefficient loci are actual Boolean polynomial sets. This does not treat a vanished leading coefficient as nonzero or silently retain the old fiber degree.

## Finite coverage of every nonzero fiber

`FiniteDegreePrefixes` supplies an explicit finite family of symbolic coefficient prefixes, with indices from zero through the original divisor degree. For any ring specialization with nonzero resulting polynomial, choose its actual resulting degree N. The corresponding prefix specializes to exactly the original resulting polynomial, and its own actual leading coefficient specializes nonzero. The coefficient at N cannot vanish symbolically because its specialization does not vanish. The proof includes arbitrary degree drops, nonzero constant fibers, zero high coefficients and empty discarded coefficient ranges.

`FiniteRootRemainders` precomputes one pseudo-remainder for each nonzero symbolic prefix; zero symbolic prefixes receive an arbitrary unused remainder. It obtains one family indexed by `Fin (q.natDegree+1)` **before** quantifying over all real specializations. For every specialization at which q is not identically zero, one family member has smaller actual degree (or is zero) and preserves all three actual sign tests at every actual root of q. The selected index may depend on the parameter, as it must when degree changes, but the finite family does not.

The final `FiniteRootRemaindersTarget` therefore has no fixed-leading-coefficient or fixed-degree premise. The only fiber-specific premise is that the divisor fiber itself is not the zero polynomial. An identically zero divisor fiber is a separate terminal branch in the planned sign algorithm, because its root set is all of the real line and a strict degree-lowering root reduction is not applicable. The theorem never claims otherwise.

## Exact scope and evidence

The three exact contracts are `PositivePseudoDivisionTarget`, `PseudoDivisionSpecializationTarget`, and `FiniteRootRemaindersTarget`. They instantiate the general algebra with actual polynomials over multivariate real parameter polynomials in every finite dimension. The generic proofs also allow arbitrary coefficient integral domains and every actual ring homomorphism into the reals.

`RootRemainderSigns` is a transparent predicate stating actual degree decrease and the three actual root sign equivalences. It does not contain a root-count, projection, desired sign table or semialgebraic-decomposition premise. All final instances construct its proof from the polynomial identities. Classical choices select the finite proved remainders; no external computation or unchecked division algorithm is used.

Run `bash audit/scratch/polynomial_pseudodivision/verify_pseudodivision.sh`. The fresh pinned compiler builds all six frozen sources, all 26 actual type/transitive-axiom reports are checked, the three target types are compared strictly with `Meta.isDefEq`, and the six source hashes are validated. Only `propext`, `Classical.choice`, and `Quot.sound` may occur in the dependencies. One unused-section-instance linter warning in the generic specialization lemma is harmless. All work remains scratch-only during milestone13's main-source freeze.

## Delivered main integration

Final import: `BfgsVerification.PseudoDivisionTargets`. Reproduce with `bash audit/verify_a_polynomial_pseudodivision.sh`. The delivered manifest is `audit/a_polynomial_pseudodivision_declarations.json`; actual build/type/axiom/contract/hash outputs use the same prefix. Reproduction requires no scratch files. All 26 declarations and 3 exact contracts retain the independently reviewed statements. This adds supporting algebra and geometry; the general arbitrary-degree Boolean projection and finite smooth-path decomposition required for the final Module A semialgebraic theorem are still open.
