# General finite smooth cover: exact scope and proof review

## Contract

The eleven frozen sources contain 41 theorems and five definitions. The final theorem `BfgsVerification.RealAlgebraicGeometry.semialgebraic_finite_smooth_cover` proves, for every finite real-coordinate type and every genuinely Boolean-polynomial semialgebraic set S, the existence of an actual finite set of semialgebraic subsets whose union is exactly S. Every two points in each piece are joined inside that piece by an actual real-parameter continuous path, smooth of all orders at every interior parameter except a finite set. The exact target `GeneralSemialgebraicSmoothCoverTarget` spells out these paths, their endpoints, containment, and exceptions directly.

There is no compactness, regularity, nondegeneracy, constant-degree, squarefree-polynomial, nonempty-set, cell-decomposition, chart-existence, root-enumeration, or projection-closure premise in the final theorem. Zero-dimensional and empty sets are included. The cover need not be a partition; its exact union and internal path connectivity suffice for the later component and critical-value arguments. Auxiliary induction lemmas explicitly take the lower-dimensional theorem, discharged by natural-number induction in the final theorem.

## Construction checked

`FiniteSmoothCovers` supplies genuine finite covers, finite unions and selection of entire compatible pieces. It never infers connectivity of an arbitrary subset. `ConnectedNonzeroSign` derives sign constancy by the intermediate value theorem on a preconnected set.

`PolynomialZeroPatterns` branches on every original polynomial fiber being identically zero and proves the literal product of the remaining fibers is nonzero. The empty product is one. Nonzero original factors can vanish only at actual roots of that product. This handles zero polynomials and all coefficient degree drops.

`FiniteRootSignatureCover` uses finite range of actual degree, actual distinct-root count and actual total real-root multiplicity to choose a finite set of attained parameter representatives. `ActualRootGapSigns` uses the actual ordered root enumeration and the proved multiplicity-preserving smooth branches on the corresponding signature. Root counts, smoothness and semialgebraicity all come from previously kernel-checked main modules.

`FiniteCoverOnSignature` refines the actual semialgebraic signature/zero pattern by signs of every input polynomial at every ordered product root. These sets are semialgebraic by actual graph intersection and the proved general projection theorem. The dimension induction applies to each finite refinement. Actual ordered graph/gap cells over the resulting base pieces cover the cylinder, including all unbounded gaps and the no-root full cylinder. Boundary signs are fixed by refinement; gap signs are constant by continuity and absence of actual roots. Thus each Boolean formula is constant on every produced cell.

`ActualCellFormulaCover` and `CylinderCoordinateCovers` transport these actual cells and paths into literal Option coordinates and select whole satisfying cells. `SemialgebraicSmoothCover` takes finite unions over all refinements and uses actual coordinate equivalences to discharge the successor dimension. The dimension-zero base case and induction prove all finite dimensions. `ReindexedSmoothCovers` then proves the arbitrary finite-coordinate API.

## Relationship to the research sources

The source A semialgebraic-criticality proof cites semialgebraic path decomposition. This tranche proves an adequate replacement: the pieces are semialgebraic and the paths are actual piecewise smooth paths. It does **not** claim semialgebraicity of those paths' graphs. Applying this cover to the actual lifted critical graph permits differentiation of both the point and objective coordinates without that stronger claim. Root-owned final application theorems must still discharge their affine-critical support arguments; this scope alone is geometry, not a claimed BFGS convergence theorem. Source C's finite piecewise smooth connectivity input is obtained directly. Original research sources are unchanged.

## Reproduction and trust boundary

Run `bash audit/scratch/finite_smooth_cover/verify.sh` from the Lean project. It builds the actual main dependencies, then recompiles every frozen owned source using the pinned compiler, prints every owned definition/theorem type and transitive axiom set, checks the final contract using strict `Meta.isDefEq`, and checks source/dependency SHA-256 values. Its proof imports depend only on delivered main modules and the eleven owned sources, never another scratch scope. The 147 transitive project source hashes are recorded separately. Allowed transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no external algebra computation is trusted.
