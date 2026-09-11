# Independent review: Module Q foundations and Q.13

Reviewed read-only: `ParabolicFamily.lean`, `ParabolicPairs.lean`,
`ParabolicDenominatorAlgebra.lean`, `ParabolicDenominator.lean`, and
`ParabolicUniformSecant.lean`, against the complete source `Q.tex`, especially
compactness, Q.9–Q.14, and the visibility/secant estimates. This is a statement
and proof review; the root's compiler and whole-project axiom audit provide the
formal integration record.

Finding: **no mathematical or statement defect found in the retained scope**.
The calibrated rescaling/envelope argument Q.7–Q.8 and Q.15–Q.17, the final Q
convergence application, and the explicit example remain separate obligations;
these five modules do not claim to complete them.

## Arbitrary finite family and degenerate branches

`Parabolic.Family m` has exactly real coefficients, positive a_i, one negative
normal slope and one positive normal slope. For a finite family this matches
`min b_i < 0 < max b_i`. The witnesses derive nonempty indices, so the actual
`Finset.sup'` objective is defined without an extra nonempty-family assumption.
There is no ordering, distinctness, genericity, unique activity, reduced-envelope
assumption, branch-adjacency condition, or nonzero intermediate b_i assumption.
Repeated branches, equal normal slopes, zero normal slopes, and tie-only branches
remain legal inputs.

The objective is the original finite maximum, not an abstract active-branch
selector. Convexity and each branch's actual Fréchet derivative are proved.
`active_eq_gradient` derives equality of every active branch gradient with the
actual derivative at a differentiable endpoint through its global supporting
inequality. Thus a differentiable tie is handled correctly without requiring a
unique active index. `gradient_from_active` supplies the witnesses subsequently
used for each actual eligible pair.

## Compactness and exact identities

`quadratic_lower_bound` chooses a positive or negative extreme-slope branch
according to the sign of v; it derives F≥a_min u². `unique_zero` then derives
u=0 and uses both extreme signs to derive v=0. Convexity, continuity, and this
proved unique minimum supply `sublevel_compact` via the already checked
finite-dimensional localization theorem. Compactness is a derived property,
not a family or run premise.

The pair definitions use the actual displacement z−x, actual decrease −g·s,
actual curvature (h−g)·s, and actual branch deficits. Q.9, Q.10, Q.11, Q.12,
Q.14, the old-radial identity, and the determinant identity have the correct
signs and endpoints. In particular D is `det(s,r(x))=2v*(u'−u)−u*(v'−v)`,
with the old radial direction. Nothing assumes u, u', h, the normal displacement,
or D is nonzero in these identities.

The secant estimate uses the proved two-weight inequality, including either
weight equal to zero. Its coefficient denominator a_i+a_j is derived strictly
positive from the family data. The quotient corollary requires t>0 only when
actually dividing by t; the uniform eligible-pair theorem instead uses the
square inequality and derives curvature nonnegativity from weak Wolfe and d>0.
There is no hidden h≠0 or deficit>0 premise.

## Q.13 uniformity and denominator safety

`exists_small_denominator_bounds` has quantifier order

```
for fixed P, compact K, η>0, c1≥0, c2<1:
  ∃ C>0, δ>0, ∀ x∈K, ∀ z∈K, ∀ actual gradients g,h,
    EligiblePair ... → η≤F(x) → d≤δ →
      d≤C|D| ∧ |horizontalStep|≤C|D| ∧ D≠0.
```

Both C and δ are selected before **all** eligible endpoint pairs and branch
choices. They depend only on the fixed family, compact set and line-search/level
parameters. A positive level is required only at the old endpoint; this is
stronger than the source's restriction of both endpoints to a positive band and
therefore specializes to it. The weaker c1≥0 and c2<1 hypotheses also include
all source parameters without removing a conclusion.

The proof derives compact coordinate and supporting-gradient bounds, then sets
κ=1−c2, E=2*a_max*R+2*G+2, τ=ηκ/(4E), and
δ=min(η/2,min(a_min*τ²,τ)). Each relevant denominator is proved positive.
The absorption lemma derives |h|≤τ and d≤τ, absorbs the error into ηκd/2,
and obtains the first inequality with Cd=8G²/(ηκ).
The scalar lemma does not assume D≠0; the final theorem derives D≠0 from d>0
and d≤Cd|D|.

The second inequality uses `b_i D = 2F(x)h + u d`, takes absolute values and
divides only by 2η>0. It never divides by b_i, so zero normal slopes are covered.
Neither normal-step smallness nor adjacent active branches enters the proof.
The final single constant max(Cd,Ch) covers both inequalities.

## Uniform secant and visibility scope

`exists_uniform_secant_bound` selects one positive constant before all eligible
pairs in an arbitrary compact K with d≤1. It derives the actual accepted branch
gradients, bounds the deficit by d, and bounds u'² from compactness; it has no
positive-band or branch-adjacency premise. `positive_visibility` derives
(g·r(x))²≥4η² from actual differentiability and F(x)≥η≥0.

These conclusions concern the unscaled direction r=(u,2v). They do not assert a
calibrated theta field, projected transport, or a certificate field W. The
module comments correctly reserve that work for a separate obligation. In the
future integration, theta bounds and calibrated transport must be proved before
applying the objective-pair convergence theorem.

All inspected namespace scopes are explicitly nested and closed consistently;
no discovery-parser mismatch was found. The files contain no custom axioms,
placeholders, or unchecked numeric computations. Root integration should retain
its ordinary complete transitive axiom audit.
