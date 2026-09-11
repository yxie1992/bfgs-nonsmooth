# Exact ordered cylindrical graph/gap partition

This bounded CAD ingredient is conditional on actual ordered boundary functions. It does not assume or assert that arbitrary input polynomials already admit such boundary functions on a finite base decomposition. The original research source is unchanged.

The frozen manifest contains four files, 24 actual declarations, two exact contracts and four strict source/wrapper checks. `verify.sh` builds the main general-projection dependency, rebuilds the three frozen smooth-path dependencies into this scope's own directory, and freshly compiles every owned file before actual type/axiom/contract validation. It preserves the prior five-file smooth-path snapshot. The fresh result is recorded in `validation.log`.

## Literal cells and finite partition

For `f : Fin r → E → ℝ`, the exact tag set is `Fin r ⊕ Fin(r+1)` and has cardinality `2*r+1`. A graph tag `i` denotes

`{(x,t) | x∈S ∧ t=f_i(x)}`.

A gap tag `j` denotes

`{(x,t) | x∈S ∧ (∀i, i.val<j.val → f_i(x)<t) ∧ (∀i, j.val≤i.val → t<f_i(x))}`.

Assuming strict ordering of the actual values at every `x∈S`, `orderedCylindricalCell_cover` proves the union of **all** these actual cells equals the whole cylinder `S×ℝ`. A height equal to a boundary is put in its actual graph. Otherwise the proof takes the least index whose boundary is strictly above that height; all preceding values are strictly below by the least-index property and absence of equality, and all following values are above by monotonicity. If there is no such index, the height lies in the final gap. This explicitly includes empty boundary families.

The disjointness proof separately handles graph/graph, graph/gap and gap/gap. Strict order makes distinct graph values unequal. Every graph index falls on one side of a gap's index split, yielding an immediate strict-inequality contradiction. Between two different gaps, the boundary at the smaller gap index separates the two heights. Existence of that boundary index is derived from the larger gap index being at most `r`; it is not assumed when the smaller gap is the final tail. Thus no missing end case is hidden in the finite partition.

## Actual paths in every cell

The base is assumed `PiecewiseSmoothConnected` and each actual boundary function is `ContDiffOn ℝ ∞` within the base. Four proved gap identities reduce all cases to the previously checked path constructions:

- `r=0`: the unique gap is the entire cylinder;
- bottom gap: strictly below the first boundary;
- top gap: strictly above the last boundary;
- interior gap: strictly between the preceding and following boundaries.

The hypotheses needed to form each `Fin r` index are derived explicitly. Interior strict separation follows from the actual boundary-order hypothesis. The resulting theorem proves every tag's literal cell has actual piecewise-smooth paths with correct endpoints and finite exceptional parameter sets. It does not conjoin paths in a different existential partition. Empty bases and empty cells remain permitted by the path predicate.

The ambient smooth-path theorem is generic over real normed vector spaces. For the finite-dimensional real-coordinate applications, these are actual Euclidean-topology paths; no smoothness of an objective or external root selector is assumed here.

## Semialgebraicity of the same cells

`IsSemialgebraicCylinder T` is only coordinate notation for the already defined genuine semialgebraic predicate on

`{v : Option (Fin n) → ℝ | (v∘some, v(none))∈T}`.

It does not build any desired projection or path conclusion into the predicate. The `some` coordinates are exactly the base vector and `none` is exactly the vertical scalar.

Given semialgebraicity of the actual restricted graph of `f` over `S`, `restricted_graph_sides_semialgebraic` derives both strict graph-side sets. It introduces one actual graph-value coordinate, imposes the literal polynomial strict inequality between that value and the retained height, and applies the proved scalar projection theorem. The graph equation then discharges the existential value exactly. No global semialgebraicity of `f` outside `S` is assumed or inferred.

Each literal gap is the finite intersection of the base pullback and the required graph-side inequalities, using the precise index split above. Consequently every graph and gap in the partition is semialgebraic when the base and actual boundary graphs are semialgebraic. This definability theorem itself needs no ordering or smoothness hypothesis, a valid strengthening because its finite Boolean description exists regardless of overlap.

## Remaining mathematical boundary

This proves the exact finite combinatorics, path construction and definability of a cylinder once actual smooth ordered boundary functions are available. The root-delineability strata, ordered-root functions, finite base partition and compatibility of original polynomial signs with each cell remain separate proofs. It does not declare a complete CAD or finite-path decomposition of arbitrary semialgebraic sets merely from these conditional ingredients. The path predicate, as in its prior scope, does not assert semialgebraicity of the curve itself; the finite piecewise-smooth paths suffice for the subsequent affine-critical-value argument.

All source expressions, finite minima, inequalities, coordinate equations, smooth path constructions and projection applications are Lean proofs. The audit allows only standard `propext`, `Classical.choice` and `Quot.sound` transitive axioms and checks the full two contracts, including the common actual cell family, arbitrary `r`, and all endpoints and tail cases.
