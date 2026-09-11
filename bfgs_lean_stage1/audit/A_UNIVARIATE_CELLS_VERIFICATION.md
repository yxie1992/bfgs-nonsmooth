# Constructed one-dimensional semialgebraic cells

This frozen six-file scope proves actual one-dimensional real-algebraic geometry from the existing quantifier-free Boolean polynomial syntax. It supplies a bounded part of the missing Module A real-algebraic infrastructure. It does not by itself prove the source's general semialgebraic finite-critical-values theorem.

## Exact proved chain

1. `rootBoundary P` is the finite union of the actual real roots of the actual polynomials in a finite family. A nonzero polynomial vanishing at a point puts that point in this boundary. The zero polynomial contributes no boundary and has constant sign everywhere.
2. On an interval avoiding this finite boundary, polynomial continuity and the intermediate value theorem prove constancy of both equality-to-zero and strict-positive tests. Equal finite root-cut profiles imply that the interval between two nonboundary points avoids every root.
3. Every actual `MvPolynomial Unit ℝ` is converted to an actual univariate `Polynomial ℝ` by substitution. Evaluation equivalence is proved using ring-hom composition. Structural induction then proves constant truth of the original Boolean formula on every nonboundary profile cell, including arbitrary negations.
4. All subsets of the finite boundary label a finite family of root-free cells. Adding the singleton boundary cells covers the entire real line. The construction includes unbounded intervals and handles an empty boundary; impossible profiles merely produce empty cells. Each root-free cell is convex, proved directly by its order interval property.
5. Retaining exactly cells containing a point satisfying the formula gives a finite convex cover equal to the formula's actual truth set. The corresponding theorem for an arbitrary actual `IsSemialgebraic S`, where `S : Set (Unit → ℝ)`, extracts its Boolean witness and lifts the real-line cells to the one-coordinate space. No finite component or cell-cover premise appears.
6. A root-free profile cell is exactly a finite intersection of strict affine inequalities against its boundary points. This proves it open and semialgebraic. Boundary singletons are polynomial equality sets. The final stronger cover consists of nonempty convex semialgebraic cells, each open or singleton, and is exactly the actual truth set.

All real coefficients are allowed, as in the existing semialgebraic definition. There is no degree bound or nonzero-polynomial assumption on the input formula. Constant formulas, empty truth sets, singleton cells, multiple/repeated roots, and unbounded components are included. The contract is a finite cover; pairwise disjointness is not separately asserted by the final target.

## Exact infrastructure targets

- `UnivariateSignBoundaryTarget`: a constructed finite boundary with constant actual Boolean truth on equal nonboundary cut profiles.
- `UnivariateConvexCoverTarget`: every genuine one-dimensional semialgebraic set is a finite union of convex subsets of its actual one-coordinate space.
- `UnivariateCellCoverTarget`: the stronger real-line cover by nonempty convex semialgebraic pieces, each open or singleton.

The three proof constants have precisely these types, checked with `Meta.isDefEq`. They are real-algebraic infrastructure contracts, not replacements for or weakened versions of Module A's final research theorem.

## Remaining mathematical boundary

This argument concerns fixed univariate polynomials. It does not derive a finite partition uniform in additional polynomial parameters, closure under general nonlinear coordinate projection, continuity or analytic parameterization of varying roots, or higher-dimensional semialgebraic paths. In particular the existing quantified support-graph projection obligation and the general affine-critical finite path-cover obligation remain. Only the previously delivered affine-in-the-eliminated-variable projection fragment and the fixed one-dimensional cell geometry are now established.

## Reproduction

Run `bash audit/verify_a_univariate_cells.sh` from the Lean project. The script rebuilds all six source files using the pinned toolchain, compiles all actual-type/transitive-axiom reports and the three strict target checks, and compares all six frozen SHA-256 hashes. `source_hashes.json`, `declarations.txt`, `UNIVARIATE_AXIOMS.lean`, `UNIVARIATE_CONTRACTS.lean`, `build.log`, `axioms.log`, `contracts.log`, and `validation.log` record this scope. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in transitive axiom reports. No external computation is used to locate roots or certify polynomial signs.


## Main delivery

The six delivered main sources differ from the reviewed scratch snapshot only by qualifying owned imports with `BfgsVerification.`. The self-contained main driver, manifest and logs are `verify_a_univariate_cells.sh`, `a_univariate_cells_declarations.json` and `a_univariate_cells_{build,axioms,contracts,validation}.log`. The driver needs no scratch sources or scratch proof imports. Main source hashes are independently frozen in the delivered manifest.
