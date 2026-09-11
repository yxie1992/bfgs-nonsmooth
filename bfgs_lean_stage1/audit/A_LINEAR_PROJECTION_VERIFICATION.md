# Constructive projection of one affine coordinate

This seven-file tranche proves a genuine special case of semialgebraic
projection. It eliminates one real variable from arbitrary finite Boolean
combinations of strict and weak inequalities affine in that variable. All
coefficients in the retained variables may be arbitrary real polynomials.
It does not assume a projection theorem and does not redefine semialgebraicity.
The existing `PolynomialFormula` and `IsSemialgebraic` definitions remain the
actual finite Boolean polynomial syntax from the earlier reviewed tranche.

## Scalar elimination and degenerate cases

For a finite family `a_i*t < b_i`, the proof derives the exact criterion:
zero coefficients require `b_i > 0`, and every negative/positive coefficient
pair requires `b_j*a_i < b_i*a_j`. The weak analogue uses weak inequalities
in the output. Both include an empty family and either or both missing signs.
All divisions used to choose a feasible t are justified by the corresponding
strict sign and are eliminated from the final criterion.

The mixed version marks each inequality with a Boolean: true means strict and
false means weak. A negative/positive pair has a strict cross-product condition
exactly when either source inequality is strict. The finite lower/upper-bound
proof explicitly handles touching weak bounds: at equal extremal bounds it
uses that common point and proves that every strict bound remains strict.
Unbounded fibers and zero coefficients are separate proved cases. Thus
replacing an equality by two weak inequalities preserves the equality fiber;
strict-only feasibility is never substituted for weak feasibility.

## Actual polynomial output and Boolean formulas

The scalar criteria are converted to quantifier-free polynomial sets using
only already proved Boolean closure and finite intersections. The output
conditions use signs of a_i, zero coefficients, b_i, and the cross-product
polynomials. No rational-function semialgebraicity premise or black-box
feasibility computation is used.

`AffineBooleanFormula` has actual affine atoms, conjunction and negation.
Atoms explicitly retain their polynomial slope/bound and strict/weak flag.
Negating an atom flips strictness and negates both coefficients. The actual
DNF construction pushes negations to atoms and distributes conjunction by
finite list products; its semantic equivalence is proved by structural
induction. A conjunction uses the mixed elimination theorem, and a finite DNF
uses actual finite unions. This proves projection for every formula in this
syntax, including arbitrary nesting of negations, not just one conjunction.

Each affine atom is encoded into the original `PolynomialFormula` by the
literal polynomial `rename(bound) - rename(slope)*X(eliminated)`, with a strict
positive sign or the negation of a negative sign. Its actual evaluation and
whole-formula semantics are proved. The final
`affine_boolean_coordinate_projection` applies the existing literal
`coordinateProjection` to this genuine polynomial set and returns an actual
`IsSemialgebraic` witness. Neither its hypothesis nor the definition of the
input syntax contains the desired projection conclusion.

## Scope and remaining Module A obligations

The three strict contracts check the mixed scalar consistency criterion,
polynomial-coefficient projection, and literal coordinate projection of an
arbitrary affine Boolean formula. These are infrastructure contracts. They do
not claim general nonlinear polynomial projection, semialgebraicity of the
actual full supporting graph, finite differentiable path decomposition, or
Module A's unconditional finite-critical-value theorem. The supporting-graph
reduction can have nonlinear dependence on the eliminated objective argument,
so this new special case does not by itself discharge that general obligation.
All original research sources remain unchanged.

Reproduce the delivered main sources with `bash audit/verify_linear_projection.sh`. The
script rebuilds all seven sources, prints every explicit declaration's actual
type and transitive axioms, checks three independent types with strict
`Meta.isDefEq`, and validates all frozen source hashes. The only accepted
foundation axioms are `propext`, `Classical.choice` and `Quot.sound`.

Main integration preserves the reviewed proof bodies and changes only import prefixes. Fresh main hashes/declarations are in `audit/a_linear_projection_declarations.json`; actual compiler, axiom, contract and validation logs share the `a_linear_projection` prefix. This delivered reproduction uses no scratch source or object file. Independent mathematical review is `audit/LINEAR_PROJECTION_PEER_REVIEW.md`.
