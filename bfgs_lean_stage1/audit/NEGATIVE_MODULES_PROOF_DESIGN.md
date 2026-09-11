# Exact proof design for negative Modules D and L

This is a source review and implementation design, not a verification result.
Both `report/chapters/D.tex` and `report/chapters/L.tex` were read in full.
The original files remain unchanged. No Lean file was created for this design.
All numerical and dynamical assertions listed below remain obligations until
their proofs compile and their transitive dependencies pass the project audit.

## Main findings

1. Module D has a finite exact algebraic seed followed by substantial, but
   elementary, analysis and an induction covering every deterministic query.
   Its infinite trajectory must not be replaced by a finite oracle regression.
2. Module L requires a new stable-orbit existence argument in addition to the
   seed. The pinned mathlib contains contraction and inverse-function theorems,
   but a search of all `Mathlib` sources found no stable-manifold theorem.
   An external citation or a rounded stable eigenvector cannot close this gap.
3. The source references `verify_certificate.py`,
   `verify_symbolic_closure.py`, an interval automatic-differentiation program,
   and `verification/fresh/SUMMARY.json`. These artifacts are absent from this
   checkout, including an unignored filename search. `VERIFICATION_REPORT.md`
   contains historical PASS descriptions, not the missing certificates.
   The displayed polynomials and formulas are enough to reconstruct new exact
   proof-producing calculations; those calculations still need to be done.
4. No contradiction or false numerical inequality was established by this
   read-only review. The primary gaps are missing formal arithmetic evidence,
   countable interpolation proofs, deterministic query semantics, and stable
   dynamics. The source already correctly distinguishes the different negative
   conclusions and regularity classes.

## Retained claims in Module D

| Claim | Exact retained content | Required proof object |
|---|---|---|
| D main theorem | One maximum of four globally convex C2 branches, branch Hessians between zero and 64I, compact sublevels, unique nonsmooth minimizer zero; identity-initialized starts approaching zero yield deterministic nonstationary limits approaching zero | A single globally defined objective, its branch regularity and Hessian bounds, and actual infinite deterministic runs |
| Deterministic implementation | Unit-first Armijo/weak-Wolfe bracketing; midpoint with finite upper bracket, doubling otherwise; strict comparisons and differentiable queries | A defined transition relation/function including rejection states, not just accepted steps |
| D root lemma | Exactly one real pair in the specified rational box of radius 10^-30 satisfies both polynomial equations; denominators nonzero; 0.060 < rho < 0.061 | A contracting self-map of the complete closed box, with exact rational enclosures and invertible rational preconditioner |
| Symbolic closure | Actual inverse-BFGS updates give M1 as displayed, then M3 = rho I; explicit displacements and z3 = rho z0 | Kernel-checked rational identities with all denominators proved nonzero |
| Symbolic beta/gamma derivation | For general admissible c,d, beta and gamma yield isotropic closure; the two root equations specialize them to 1/4 and 1/16 | Separate general rational identities plus specialization, if the explanatory derivation is to be retained as verified |
| SPD | Each finite seed matrix and every scaled future matrix is positive definite | Actual update positivity from initial I and verified positive curvature, or exact two-dimensional Sylvester inequalities |
| Nine-query certificate | Unique active branch at every listed query; rejected value strictly exceeds current value; accepted Armijo ratio > 1/3 and Wolfe ratio < 0 | Finitely many exact strict inequalities over the algebraic root box, tied to actual query definitions |
| Parameter extension | Identical decisions for every 0 < c1 <= 1/3 and c1 < c2 < 1 | Sign-safe conversion of the ratio inequalities to the chosen line-search convention |
| Trial bounds | Every base query and accepted point has all three absolute slope evaluations < 3, second coordinate < 2, and positive G value | Exact inequalities with accepted starting points included explicitly |
| Homogeneous seed orbit | x_(3m+j) = rho^m z_j and H_(3m+j) = rho^m M_j; all trials scale identically; x tends to zero and G values decrease to zero | Three-phase induction and geometric convergence, including the full query tree |
| Seed nonstationarity | Direction (-1,16) gives all slope products <= -1, hence G(t d) = -t for t >= 0 and zero is outside the slope convex hull | Exact inequalities and a separating linear functional |
| Coercive polyhedral global failure | The added fourth affine branch is inactive on every query; unique minimum (-1,16) with value -1; all sublevels bounded | Positive-weight lower bound, equality characterization, coordinate bounds, and query preservation |
| Scalar interpolation | For each of two specified b values, the globally defined phi_b is convex, C2, nonnegative, coercive, uniquely minimized at zero, and has the stated jets, curvature bounds, and exact affine plateaus | Definition with compatible countable pieces and proofs at every join and the accumulation point |
| Additional C2,1 regularity | Global Lipschitz continuity of the second derivative with the displayed finite derivative bound | A global estimate across arbitrarily many interpolation intervals, not only within a ramp |
| Four-branch objective | Hessian bounds 51, <52, <12, and zero imply common 64I; common Hessian Lipschitz bound such as 60000; compact sublevels and unique nonsmooth zero | Scalar composition calculus, Euclidean rank-one norm bounds, and finite-max geometry |
| Local cone copies | F(p_n+h) = a_n^3 + a_n^2 G(h) under the displayed three slab inequalities; p_n is positive-valued and nonstationary | Exact plateau use and strict inactivity of the fourth branch |
| All-trial embedding | Starting at p_n+a_n^2 z0 with H0=I gives the stated exact point and matrix sequences; every rejected and accepted query lies in the local cone model | Simultaneous run/query induction, not an assumption that the model is applicable |
| Arbitrarily small full trajectories | Supremum over all queries tends to zero as n grows; each individual run converges to p_n rather than the minimizer | Uniform finite-base-query norm bound, two geometric limits, and the actual query encoding |

The source does not claim a positive-measure failure basin, strong-Wolfe
interpolation-search failure, failure of every nearby start, or uniform positive
lower branch curvature in Module D. None should be added to the final target.

## Retained claims in Module L

| Claim | Exact retained content | Required proof object |
|---|---|---|
| L global theorem | For every mu > 0, a quadratic plus the three seed affine slopes has constant branch Hessians mu I and some deterministic runs tending to the nonstationary origin | A perturbed stable orbit for each mu, not reuse of the unperturbed seed |
| Actual minimizer | gbar=(1,-16)/257 is the least-norm point of the slope triangle; xStar=-gbar/mu and minimum -1/(514mu); exactly two active slopes make the minimizer nonsmooth | Convex-combination and supporting-plane inequalities or direct completion of the square, plus strict third-branch gap |
| Normalized return map | Five coordinates (z1,z2,b,e,tau); exact three updates, division by r=(M3)11, and tau' = tau*r | Rationally defined map on an open neighborhood with nonzero denominators, separate from physical storage |
| Agreement lemma | On a neighborhood of the normalized boundary seed, every tau>0 state follows precisely the nine strict query decisions and the return map | Continuity and finitely many strict inequalities, then query-state induction |
| Analytic extension | The return map is real analytic near the seed, permitting artificial negative tau; only tau>0 represents the actual run | Rational-operation regularity and denominator neighborhood lemmas |
| Shape Jacobian | The exact derivative of the actual shape return map has the displayed rigorous polynomial sign bounds | Symbolically differentiated rational map, with a derivative theorem and exact interval bounds |
| Shape roots | Two distinct real roots in (0.038,0.039) and (1.564,1.565), exhausting the degree-two characteristic polynomial | Intermediate value arguments and factorization/root count, not a floating-point eigensolver |
| Full derivative | Block upper-triangular derivative with diagonal blocks rho^-1 I2, J, rho; the listed five eigenvalues; invertibility and exactly two stable dimensions | Exact derivative blocks and linear algebra, with multiplicities and the real representation specified |
| Stable transversality | The rho eigenvector can have tau coordinate one because rho differs from every eigenvalue of the upper-left four-dimensional block | Solve an invertible linear system; this is needed to reach physical positive tau |
| Stable orbit existence | Arbitrarily small positive-tau states have forward return-map orbits staying in the agreement neighborhood and tending to the seed | A proved stable-manifold theorem or a sufficient stable-orbit graph contraction theorem |
| Physical convergence | Positive scale persists, every substep is SPD, all queries stay small and tend to zero, values decrease to zero while zero remains nonstationary | Exact normalization bridge, bounded normalized query maps, and stable-orbit estimates |
| C1,1 scalar interpolation | The second interpolation has prescribed node values/slopes and plateaus, bounded derivative slope, but no second derivative at zero | Countable gluing with global Lipschitz derivative and explicit incompatible second-derivative subsequences |
| Local four-branch embedding | One strongly convex max of four globally C1,1 branches, common gradient Lipschitz bound 512, compact sublevels, unique nonsmooth zero | Actual smoothness and convexity statements, not an almost-everywhere Hessian surrogate |
| Classical Hessian bounds | Wherever F is twice differentiable, mu I <= Hessian F <= 512I | An exact second-derivative predicate and the finite-max active-gradient/Taylor argument |
| Copying one perturbed orbit | The same small Q_mu orbit copies into every p_n+a_n y with the same fixed SPD initial matrix; all query decisions are preserved | Affine objective identity on a fixed query neighborhood and scale invariance |
| Identity initialization | A single fixed coordinate change A=H0^(1/2) produces identity initialization and fixed transformed curvature constants | SPD square root, gradient transformation, and full query/update affine invariance |
| Piecewise-affine alternative | Countable convex polyhedral nonsmooth part, same plateaus and runs, and one constant SPD Hessian at every twice-differentiable point after coordinate change | Local finiteness away from zero, inactivity at vanishing scalar arguments, and differentiable finite-max-affine implies locally affine |

The global theorem need not have H0=I in its displayed physical coordinates.
The local theorem attains identity initialization by one fixed transformation
for the entire objective and all starts. The latter theorem does not assert
four globally C2 branches with uniform positive lower curvature; the source
explicitly leaves that stronger combination unproved. The countable-polyhedral
variant does not acquire a finite smooth-branch representation by this proof.

## Shared exact arithmetic layer

Use `Vec 2` for the explicit algebra, while naming Euclidean norms and Hessian
quadratic forms explicitly. The default finite-Pi norm is the sup norm and is
appropriate for the root box; it is not a substitute for a Euclidean Hessian
bound with the same numerical constant.

Define all displayed decimals as exact rationals. Define c,d through the proved
existence-and-uniqueness result, not as their decimal center. The root theorem
must expose both polynomial equations and box membership. Prove every needed
denominator bound from the box before division simplification.

A manageable proof-producing interval layer can use rational lower/upper
endpoints and sound addition, multiplication, negation, integer power, and
reciprocal operations. Every reciprocal requires a sign-separated interval.
Evaluation soundness must be a Lean theorem for the actual expression. Rational
leaf comparisons can use `norm_num`; polynomial/rational identities can use
`ring`, `ring_nf`, and `field_simp` after denominator proofs. External Python may
generate a proposed expression and enclosure tree, but only the Lean proof
checks the certificate. Neither a JSON PASS bit nor `native_decide` is allowed
to discharge a mathematical theorem.

For the root box X, define P exactly and the rational matrix M from DP at the
rational center. Check M*DP(center)=I explicitly. Prove

```
norm (I - M * DP(z)) <= 10^-26  for z in X
norm (M * P(center)) < 10^-50
```

with the induced sup operator norm, or directly with coordinate row sums. A
convex mean-value bound makes z -> z-MP(z) a contraction on X. The residual
estimate plus box radius proves it maps X to X. Completeness and contraction
give one fixed point. Invertibility of M is indispensable for turning fixed
point equality into P(z)=0. Conversely every root is a fixed point, giving
uniqueness in the box. The strict bound in the source may be replaced internally
by the displayed non-strict bound 10^-26, since that still proves the source's
root conclusion; do not advertise the stronger strict derivative estimate as
verified unless it is actually proved.

For L's Jacobian, an exact derivative of the actual return map must precede
interval enclosure. An automatic differentiation implementation needs a
semantic derivative soundness theorem, or its output must be reconstructed
with ordinary `HasFDerivAt` proofs. A certificate for a separately defined
matrix J without that identification would leave the dynamical result open.

## Deterministic all-query semantics

The existing `AdmissibleBFGSRun` is an accepted-iterate model. It cannot by itself
express or prove the deterministic selection or rejected-query assertions.
Add a separate finite-query state model with current x,H,g, lower bracket,
optional finite upper bracket, trial alpha, and a query index. The test order
must be Armijo first, then weak Wolfe. Define the strict tests used by D; prove
that all certified margins also give the same decisions for non-strict tests.
An accepted outcome supplies alpha and the actual derivative at the accepted
query and then performs the existing full inverse-BFGS update.

Do not assert termination for arbitrary objective or input state. A finite trace
with the exact three lists [1], [1,1/2,1/4], and [1,1/2,1/4,1/8,1/16] proves
termination for the constructed states, with at most five queries. All branches
have a strictly unique active index at each query, proving differentiability
and identifying the actual gradient there. A general lemma that a finite max
agrees locally with a strictly active continuous branch will be useful.

The D induction should prove the normalized state formula and its entire
finite query trace together. The scaling lemma must preserve function
differences, directional products, bracket transitions, accepted updates,
and local-model membership at rejected trials. Export an accepted run into
`AdmissibleBFGSRun` only after the deterministic trace theorem is available.

For the final small-neighborhood assertion, quantify over every iteration and
every query in that iteration's trace. A bound only on accepted x_k is weaker
than the source theorem. The finite set of base queries gives the required
uniform constant.

## Countable scalar interpolation layer

Prove a reusable construction for intervals [b*r^(n+1), b*r^n], with positive
b and 0<r<1. Required primitives are interval coverage of (0,b], compatibility
at shared nodes, local finiteness away from zero, a well-defined piecewise
function, and identification with each local formula. A noncomputable choice
of containing interval is acceptable only with an independence-of-choice proof.

First prove the ramp and primitive formulas, including values and derivatives
at both transition endpoints. Then prove node matching and exact plateaus at
all n, with a separate outer-extension case n=0. Prove regularity away from zero
using local formulas. Treat the accumulation point explicitly:

- D needs function O(x^3), first derivative O(x^2), and second derivative O(x),
  followed by two actual differentiability proofs and continuity of the second
  derivative at zero.
- L needs function O(x^2), derivative O(x), and global Lipschitz derivative.
  It must also prove failure of the second derivative using both sequences
  b*a_n and (b+1/4)*a_n and their distinct derivative-quotient limits.
- A per-interval derivative bound does not immediately give a global bound
  across infinitely many knots. Prove finite telescoping estimates away from
  zero and pass to the zero endpoint by continuity, or establish monotonicity
  and Lipschitz inequalities directly from the piecewise derivative.

Convexity can follow from the monotone derivative. Coercivity must include both
outer extensions. The exact affine intervals, not approximate interpolation
samples, drive the local cone-copy identities. Module D's stronger C2,1 claim
requires the analogous global Lipschitz argument for the second derivative.

For the countable-polyhedral alternative, separately prove that all potentially
active scalar arguments are nonzero near each nonzero physical point. This
excludes accumulation of relevant knots locally. A finite max of affine
functions which is differentiable at a point is locally affine there, because
all active slopes agree and inactive branches have strict gaps. Without that
step, a claim about a constant classical Hessian would be premature.

## Stable dynamics: the main new analytic dependency

The supplied source argument invokes a local stable-manifold theorem. That is
a valid proposed analytic route but not a declaration presently found in this
mathlib. Merely proving derivative hyperbolicity, an inverse-function theorem,
or the existence of a stable eigenvector does not prove a nonlinear forward
orbit exists in the stable set.

A smaller sufficient theorem may be easier than formalizing all manifold
regularity. In coordinates splitting stable and unstable eigenspaces, write
T(w)=A*w+N(w), with DN(0)=0. Prove a small-neighborhood bound making N Lipschitz
with arbitrarily small constant. In an adapted finite-dimensional norm arrange
||A_s||<1 and ||A_u^-1||<1. Construct a forward orbit tending to zero by a
Lyapunov-Perron contraction on a complete space of bounded or weighted bounded
sequences. Its stable coordinate has prescribed initial value and its unstable
coordinate is determined by a convergent backwards-series formula.

This proposed substitute still needs proofs of completeness, convergence of
the series, the contraction bound, recurrence of the fixed sequence, and
uniform smallness of the full orbit. To obtain positive initial tau, prove the
initial-state graph is tangent to the stable linear space, or a sufficiently
strong small-error estimate along the rho eigenvector whose tau coordinate is
one. A generic nonzero bounded stable orbit without the tau sign is insufficient.
Then use tau' = tau*r and r>0 on the chosen neighborhood to keep tau positive.

The exact derivative in L has only two stable dimensions and three unstable
dimensions. Its repeated rho^-1 eigenvalue has a scalar two-dimensional
diagonal block. The remaining three eigenvalues are separated by the stated
intervals. Explicit finite-dimensional eigenvectors and a coordinate change
may avoid a general spectral-subspace theory, but their spanning and inverse
properties still need proofs. For each mu>0 the neighborhood may depend on mu;
the source requires no uniform neighborhood over all mu.

Whether using this smaller theorem or a full stable-manifold theorem, prove
the small-orbit property, not only asymptotic convergence. This is what permits
copying one entire perturbed orbit into every local interpolation neighborhood.
Forward numerical shooting is particularly unsuitable because unstable
directions amplify every truncation error.

## Exact second derivatives and affine invariance

For C2 branches, export genuine `ContDiff`/`HasFDerivAt` facts and identify the
second derivative with the displayed matrix. For L's pointwise Hessian claim,
choose and document a genuine twice-Fréchet-differentiable predicate. Requiring
`ContDiffAt 2 F x` would prove only a stronger-regularity special case and would
silently weaken the source's universal claim over twice-differentiable points.
Conversely, differentiating Lean's total `fderiv` without actual first-derivative
existence can accidentally involve its default value at nondifferentiable
points. That convention must not define the classical-Hessian hypothesis.

Prove active-gradient agreement for a finite max at a differentiable point.
Together with strict gaps to inactive pieces and the uniform branch Taylor
upper bounds, this gives the maximum's local upper quadratic remainder. Actual
strong convexity supplies the lower remainder. Taking directional second-order
limits yields the source Hessian inequalities without assuming that the max
has a globally Lipschitz gradient.

For the fixed transformation x=A*z, prove actual gradient transformation,
direction and step transformation, every line-search comparison, and the
inverse-BFGS congruence update. The transformed inverse matrix is
A^-1*H*A^-T. Thus A=H0^(1/2) gives initial I, while the scalar-positive Hessian
mu*I becomes mu*H0. Constants are fixed for the transformed objective and are
not reselected for each initial point.

## Pinned mathlib primitives actually located

The inspection used `leanprover/lean4:v4.19.0` and the project's existing locked
mathlib checkout. These are source-located APIs, not yet compiler-tested calls
in a proposed D/L implementation.

| Need | Local source / API |
|---|---|
| Complete-set contraction | `Mathlib/Topology/MetricSpace/Contracting.lean`: `ContractingWith.exists_fixedPoint'`, `efixedPoint'`, fixed-point and iteration bounds |
| Derivative bound to Lipschitz estimate | `Mathlib/Analysis/Calculus/MeanValue.lean`: `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`, derivative variants, and scalar variants |
| C1 local inverse | `Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`: `ContDiffAt.toPartialHomeomorph`, `localInverse`, `to_localInverse` |
| Rational expression smoothness | `Mathlib/Analysis/Calculus/ContDiff/Operations.lean` and ordinary derivative algebra |
| Characteristic polynomial sign roots | `Mathlib/Topology/Order/IntermediateValue.lean`: `intermediate_value_Icc` and its reversed version; polynomial root/factorization APIs in `Mathlib/Algebra/Polynomial/Roots.lean` |
| Scalar convexity from derivative | `Mathlib/Analysis/Convex/Deriv.lean`: `MonotoneOn.convexOn_of_deriv`, second-derivative variants |
| Strong convexity | `Mathlib/Analysis/Convex/Strong.lean` |
| C2 and Taylor statements | `Mathlib/Analysis/Calculus/ContDiff/Defs.lean`, `Basic.lean`, and `Mathlib/Analysis/Calculus/Taylor.lean` |
| SPD square root | `Mathlib/LinearAlgebra/Matrix/PosDef.lean`: `Matrix.PosSemidef.sqrt`, `posSemidef_sqrt`, `sq_sqrt`, `sqrt_mul_self` |
| Complete bounded sequence carrier | `Mathlib/Topology/ContinuousMap/Bounded/Basic.lean`: completeness of bounded continuous maps; natural numbers have discrete topology |
| Vanishing sequences / alternative carrier | `Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean`; `Mathlib/Analysis/Normed/Lp/lpSpace.lean` includes complete lp spaces |
| Proof-producing rational arithmetic | `Mathlib/Tactic/NormNum`, `Ring`, `Linarith`; `Tactic/Bound` can assist inequality propagation |

No stable-manifold declaration was found by searching `stable.?manifold` and
`StableManifold` across all pinned mathlib source files. `interval_cases` is an
integer case-splitting tactic, not a real interval arithmetic certificate
checker. No general real interval root-isolation tactic was established by this
inspection; the small sound interval layer above remains a development task.

## Recommended exact milestones

1. Define deterministic query traces and the proof-producing rational enclosure
   layer. Prove the root and symbolic full-BFGS seed closure.
2. Certify all nine query branches and inequalities; prove the exact infinite
   homogeneous seed and coercive global polyhedral counterexample. This is a
   meaningful negative milestone independent of interpolation or stable dynamics.
3. Prove the reusable countable interpolation machinery and Module D's complete
   identity-initialized local counterexample, including every query.
4. Formalize L's normalized map, actual-query agreement, exact derivative and
   eigenvalue separation. Retain these as finite/local results until stable
   orbit existence is proved.
5. Prove the required stable-orbit theorem and conclude L's global quadratic
   counterexample with complete small-query control.
6. Complete L's interpolation and fixed affine-invariance embedding, then the
   countable-polyhedral alternative and precise classical Hessian conclusions.

Every milestone needs separate declarations for what is proved, a statement
review, and transitive axiom logs. A theorem conditional on an assumed algebraic
root, assumed hyperbolic stable orbit, or assumed interpolation regularity is a
useful intermediate theorem but is not the corresponding existential negative
result in the report.
