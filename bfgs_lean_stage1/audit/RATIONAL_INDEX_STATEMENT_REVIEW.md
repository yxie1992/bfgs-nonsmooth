# Arbitrary-degree rational index and exact Euclidean Tarski computation

This eleven-file tranche completes the fixed-fiber rational-index computation stage of the general Module A plan. It imports the independently reviewed six-file actual root-sign/local-index tranche. It does not yet prove parameter-uniform semialgebraic index fibers, arbitrary nonlinear projection, or finite semialgebraic smooth paths. The general A source theorem remains open.

## Root orders and all local pole cases

`RationalRootOrder` factors numerator and denominator by their actual root multiplicities. It derives the exact quotient expression when the numerator order is at least the denominator order, and the normalized quotient when the denominator order is larger. The nonvanishing remaining denominator factor is derived from actual monic division, and cancellations are performed only at punctured points with the required nonzero values. The former case has a finite punctured limit and zero local index.

`PowerPoleIndex` proves actual infinite limits for positive integer pole orders, separating odd and even orders and positive and negative leading quotients. Even-order poles have the same infinite direction on both sides and index zero. Odd-order poles have opposite directions and index equal to the actual quotient sign. These are actual real-function limits, not a symbolic pole annotation.

`RationalLocalReciprocity` applies those limits to actual polynomial quotients. Its exact local order formula allows numerator and denominator to share roots with arbitrary multiplicity. Adding the quotient and reciprocal indices gives the signed contribution when the sum of root orders is odd, and zero otherwise. Equality of orders, common roots and zero evaluations are retained; neither coprimality nor square-freeness is assumed.

## Remainders and global endpoint signs

`RationalRemainderInvariance` proves punctured polynomial nonvanishing, invariance of the local index under actual eventual equality and under adding a continuous real function. Adding a polynomial multiple of the denominator therefore preserves the actual rational index. The ordinary polynomial remainder theorem follows from the exact Euclidean division identity, with no root-count premise.

`PolynomialInfinitySigns` proves actual eventual signs at both infinities from leading coefficient and degree parity, including zero and constant polynomials. Reflection by the actual polynomial substitution `-X` supplies the left-tail formula.

`FiniteStepSums` and `FiniteJumpTelescoping` prove a generic finite-jump identity. Subtract the finite sum of closed right-hand jump steps from a function with specified constant left and right germs. Away from each cut the other step terms are locally constant; the matching germ identities also make the corrected function locally constant at the cut. Connectedness of the real line then proves it constant. Actual tail values yield the total jump sum, without assuming an ordering of the cuts or a telescoping identity.

`PolynomialSignJumps` discharges every germ hypothesis for the right-hand sign of an actual nonzero polynomial. At a root it uses the nonvanishing remaining factor sign; away from roots that equals the sign of the actual polynomial value. This right-hand extension is used deliberately: the raw sign value zero at a root need not equal either one-sided value. The finite exceptional set is exactly the actual distinct real roots. The final polynomial jump sum equals the difference of the actual leading-coefficient/parity tail signs.

`RationalGlobalReciprocity` identifies twice each reciprocal local-index sum with the actual product-polynomial sign jump. Each separate denominator-root sum is enlarged to the product's actual root union by proving the extra terms have index zero. The polynomial jump identity then gives full-line rational reciprocity from leading coefficient and parity. Integer division by two is justified by the proved doubled identity. Common roots are treated by their actual local orders rather than counted twice or discarded.

## Terminating actual Euclidean computation

`EuclideanIndexComputation` derives the recurrence by combining remainder invariance and reciprocal-index equality. The finite recursive function uses only actual real-polynomial remainders, actual leading coefficients and natural degrees, sign tests and integer arithmetic. A nonzero remainder has strictly smaller actual degree than the denominator. Induction proves that fuel larger than the denominator's natural degree suffices, and the exported definition uses exactly `natDegree+1`. It does not assume termination, supply a query table, or import an external calculation.

Zero denominators follow the explicitly defined empty-root index convention; zero numerators and zero remainders return zero and are proved separately. Constant nonzero denominators force the zero-remainder branch. The final query theorem assumes only that its root polynomial is nonzero and derives the exact integer Tarski query as the Euclidean index of `q*p'/p`. Repeated roots, vanishing weights and arbitrary degrees are included through the reviewed local residue theorem and the new exact index calculation.

## Contracts and reproducibility

The five exact contracts are `FiniteJumpTelescopingTarget`, `PolynomialSignJumpTarget`, `RationalIndexReciprocityTarget`, `RationalIndexRemainderTarget` and `EuclideanIndexComputationTarget`. Generic finite-jump assumptions appear only in the reusable intermediate contract; the polynomial and final query contracts derive them from actual polynomials. This is a proved fixed-fiber computation, not a conditional substitute for parameter projection or the final A theorem.

Run `bash audit/scratch/rational_index/verify_rational_index.sh`. The script rebuilds the six frozen root-sign dependencies into a separate local dependency output directory and then rebuilds all eleven sources. It prints every actual type and transitive dependency set, checks five exact contracts by strict `Meta.isDefEq`, and validates all own and dependency hashes. Only standard `propext`, `Classical.choice` and `Quot.sound` dependencies are allowed. This tranche remains scratch-only during the milestone14 main audit.
