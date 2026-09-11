# Actual polynomial degree and multiplicity strata

This frozen five-file, 39-declaration tranche advances the outstanding general real-algebraic infrastructure for Module A. It proves actual semialgebraic degree/multiplicity partitions and derived local charts at multiple roots. It does not claim general nonlinear projection closure, a finite global chart decomposition, or the source's final affine-critical finite-value theorem.

The input is an arbitrary real multivariate polynomial in `Option (Fin n)` coordinates. The `some i` coordinates are parameters and `none` is the scalar fiber variable. No uniform nonzero-fiber, degree-stability, simple-root, or multiplicity-stability premise is imposed on the partition theorems. Arbitrary finite parameter dimension, including zero, and arbitrary degree are allowed.

## Coefficients and degrees

`PolynomialFiberDegree` uses the actual `MvPolynomial.optionEquivLeft` algebra equivalence to regard the input as a univariate polynomial whose coefficients are parameter polynomials. It proves that specializing those coefficients gives exactly the previously defined actual fiber polynomial. Evaluation equality is proved through the algebra equivalence and polynomial extensionality; no coefficient oracle is assumed.

Every fiber has natural degree at most the input's degree in the eliminated coordinate. An identically zero fiber is characterized by the vanishing of finitely many actual coefficient polynomials up to that uniform bound. A nonzero fiber of exact degree k is characterized by its kth coefficient being nonzero and all higher coefficients through that bound vanishing. These give actual Boolean polynomial witnesses for the zero-fiber locus and every exact degree locus, together with their finite cover of all parameter space. Zero fibers are explicitly separate because a polynomial's total natural degree alone does not distinguish the zero polynomial from a nonzero constant.

## Actual derivative tests and multiplicities

`PolynomialFiberDerivatives` proves that differentiating the multivariate polynomial in the eliminated coordinate commutes with specialization to an actual univariate fiber. Induction gives the same identity for every iterated derivative. Evaluations of these derivatives are therefore actual polynomial functions of both the parameter and scalar variables.

`PolynomialRootMultiplicity` uses mathlib's actual polynomial root multiplicity. For a nonzero real polynomial, the derivative at exactly its root order evaluates to a nonzero factorial times the nonvanishing remaining factor. Derivatives of all smaller orders vanish. Conversely, these finite tests determine the actual root order exactly. The proof includes order zero, corresponding to nonroots of nonzero fibers.

The exact-multiplicity stratum requires a nonzero fiber and equality of its actual root multiplicity to m. It is proved equal to the finite derivative-test locus. Nonvanishing of the mth derivative itself rules out an identically zero fiber, so the equivalence does not hide any additional nonzero condition. Each stratum is semialgebraic. The zero-fiber cylinder is independently semialgebraic by polynomial preimage of the proved parameter locus.

All distinct multiplicity strata are disjoint and disjoint from the zero-fiber cylinder. Divisibility by the actual power of `X−b` bounds multiplicity by the actual fiber degree, hence by the uniform eliminated-coordinate degree. These loci form a finite partition of the entire parameter/scalar space. The original polynomial zero set is exactly the zero-fiber cylinder union the positive-multiplicity strata, with indices from 1 through the uniform degree bound. Thus the identically zero input, identically zero special fibers, degree drops, constants and repeated roots are all included correctly.

## What the local chart does and does not say

`MultiplicityRootCharts` proves that at a point of positive multiplicity m, the `(m−1)`st derivative polynomial has a simple root. The previously verified actual implicit-function construction therefore gives positive fixed parameter/scalar radii, a smooth function g on the parameter ball, and a semialgebraic graph. In that same fixed box, the selected derivative vanishes exactly on the graph. Every nearby point belonging to the same multiplicity-m stratum lies on that graph.

The final wrapper starts with only a nonzero actual fiber and an actual root. It derives m as that root's actual multiplicity, its positive uniform bound, the derivative's simplicity, and the entire local chart. No selector, nonzero derivative, or smoothness input remains in that wrapper.

Crucially, the graph describes the selected derivative's roots. It is not asserted to equal the original polynomial zero set in the box, nor to contain points of other multiplicity strata. For instance, a multiple root can split into roots of smaller multiplicity nearby. The graph is semialgebraic only on the stated parameter ball. The function is `ContDiffOn ℝ ∞` there; an analytic-selector conclusion is not added. This supplies a local containing graph for each positive multiplicity stratum without claiming that its parameter projection is semialgebraic.

## Exact contracts and remaining obligations

The four strict contracts are `PolynomialDegreeStrataTarget`, `PolynomialDerivativeSpecializationTarget`, `PolynomialMultiplicityStrataTarget`, and `PolynomialMultipleRootChartTarget`. They are supporting real-algebraic contracts, not substitutes for Module A's research theorem. The entire partition target has no hypotheses beyond the actual polynomial input. The multiple-root chart contract has exactly the nonzero-fiber and actual-root hypotheses described above.

The general parameter projection of multiplicity strata, handling of all Boolean sign conditions under nonlinear elimination, global finite chart/path decomposition, and the final general semialgebraic affine-critical-value theorem remain open. Finite multiplicity indices alone do not prove a finite global chart cover. No source conclusion has been weakened or marked complete by this tranche.

## Reproduction

Run `bash audit/scratch/polynomial_multiplicity/verify_multiplicity.sh` from the Lean project. It rebuilds all five frozen sources with the pinned compiler, compiles all 39 actual declaration types and transitive-axiom reports, checks the four exact target types using `Meta.isDefEq`, and verifies all five SHA-256 hashes. The reports allow only `propext`, `Classical.choice`, and `Quot.sound`. The source uses no external root or coefficient computation. Evidence is in `source_hashes.json`, `declarations.txt`, `MULTIPLICITY_AXIOMS.lean`, `MULTIPLICITY_CONTRACTS.lean`, and the four build/axiom/contract/validation logs.

## Delivered main integration

Final import: `BfgsVerification.PolynomialMultiplicityTargets`. Reproduce with `bash audit/verify_a_polynomial_multiplicity.sh`. The delivered manifest is `audit/a_polynomial_multiplicity_declarations.json`; actual build/type/axiom/contract/hash outputs use the same prefix. Reproduction requires no scratch files. All 39 declarations and 4 exact contracts retain the independently reviewed statements. This adds supporting algebra and geometry; the general arbitrary-degree Boolean projection and finite smooth-path decomposition required for the final Module A semialgebraic theorem are still open.
