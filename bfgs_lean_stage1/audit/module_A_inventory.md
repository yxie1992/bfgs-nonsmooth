# Module A retained-claim inventory and prerequisite review

Read in full: `BFGS_MASTER_REPORT_LaTeX/report/chapters/affine_geometry.tex`.
The source is preserved unchanged. This inventory records mathematical scope
and implementation prerequisites; it does not mark new declarations verified.
No Lean files were edited during the audit freeze.

## Complete retained-claim register

| Source claim | Exact scope | Current status / missing work |
|---|---|---|
| Subgradient affine geometry | For a finite convex real-valued objective, V(p) is the linear span of subgradient differences; U(p) is its orthogonal complement; a(p) is the nearest point to zero in the affine hull of the subdifferential | Pending. Define the actual convex subdifferential, prove nonemptiness, and connect its affine span/direction to the Euclidean projection |
| Affine decomposition | aff(partial F(p)) = a(p)+V(p), and a(p) is orthogonal to V(p) | Pending. Generic nonempty affine-subspace projection theorem, then specialize |
| Common tangential projection | Every subgradient g has P_U g = a and inner(g,a)=norm(a)^2 | Pending. No smoothness or finite-branch representation is needed |
| Equal-rate separation | At nonoptimal points, affine-critical correctness AC is equivalent to a vector v satisfying inner(g,v)=-1 for every subgradient; v=-a/norm(a)^2 works | Pending. Must prove the equivalence with zero outside the affine hull, not merely separation from the convex hull |
| Strict versus equal-rate descent | Equal negative inner products imply strict descent and impose a stronger geometric restriction | Pending as the elementary consequence of the preceding theorem; do not equate the two conditions |
| Cluster-point reduction | On a compact admissible run all cluster points have the finite limiting objective value; existence of at least one affine-critical cluster point, together with AC on the basin, forces optimal values | Objective finite limits and compact convergence machinery already verified; affine-critical reduction and subdifferential bridge pending |
| Nonunique/unique convergence conclusions | The preceding optimal-value conclusion gives distance to the full solution set tending to zero, and whole-sequence convergence under uniqueness | Generic results already verified in `CompactConvergence.lean` and `LocalizationCorollaries.lean`; final AC wrapper pending. Use actual Euclidean solution-set distance in report exports |
| Gradient warning | For absolute value, differentiable nonzero iterates have gradient magnitude one even when they approach its minimizer | Pending exact example. Affine-critical cluster points must not be replaced by a vanishing-gradient assumption |
| Quantitative visibility condition | A positive minimum of gamma(p)=dist(0,aff(partial F(p))) on every compact positive band is useful; pointwise nonzero gamma plus compactness alone does not supply it | Pending interpretation plus the rank-loss example below |
| Rank-loss objective | F(u,v)=u+u^2+v^2+abs(u*v) is the maximum of the two displayed convex quadratic branches | Pending exact identity and convexity proof |
| Rank-loss curvature and minimizer | Both branch Hessians have eigenvalues 1 and 3; F is strongly convex, with unique minimizer (-1/2,0), value -1/4 | Pending exact Hessian, strong-convexity, and minimizer proofs |
| Rank loss on the vertical axis | At (0,t), t nonzero, active gradients are (1+t,2t) and (1-t,2t), so gamma=2*abs(t); at zero the single common gradient is (1,0), so gamma=1 | Pending subdifferential formula and exact affine-distance calculations, including the separate t=0 case |
| Other switching axis | gamma(u,0)=abs(1+2u), which vanishes only at the minimizer | Pending exact calculation, with the origin consistent with the previous case |
| Global AC in rank-loss example | Smooth points are affine critical exactly when stationary; the axis calculations imply AC globally | Pending domain split into the two axes and smooth complement |
| Failure of uniform visibility | Along (0,t) tending to zero, gamma tends to zero while the objective gap tends to 1/4 | Pending exact limit; a compact positive band containing a short vertical segment demonstrates failure of any positive lower bound |
| Scope of rank-loss example | This is geometric rank loss, not a BFGS counterexample; a sufficiently small neighborhood of the true minimizer excludes the rank-loss point | Retained limitation; do not attach a failing trajectory claim |
| Local active-set exclusion | For a finite maximum of continuous branches, indices inactive at a reference minimizer remain inactive on a neighborhood | Pending finite strict-gap continuity lemma |
| Barycentric local AC | Convex C1 branches, affine independence of active gradients at the minimizer, and strictly positive optimal barycentric weights imply AC near that minimizer | Pending. No uniqueness or Hessian assumption is part of this particular proposition |
| Gram/pseudoinverse formula | The augmented-column matrix A(x) has full column rank locally; whenever A(p)*lambda=(0,...,0,1) is solvable, its unique solution is (A^T*A)^-1*A^T times that vector | Pending exact rectangular linear algebra and continuity of the actual matrix expression |
| Positive weights and missing indices | Continuity preserves strictly positive coefficients; a missing active index would have coefficient zero, so an affine-critical point locally has a positive convex representation of zero | Pending proof through the active-gradient convex-hull formula for the actual subdifferential |
| Local lower semicontinuity of gamma | Every nonempty subset of the reference active gradients has a locally continuous affine-hull distance; finitely many possible active sets imply gamma is lower semicontinuous locally | Pending. Rank persistence must be established for every relevant subset, and a limiting active set is only a subset of the active set at the limit |
| Uniform visibility under nondegeneracy | On a compact positive band contained in that local neighborhood, AC and lower semicontinuity give a strictly positive minimum of gamma | Pending. The neighborhood containment is essential; the proposition is not a global positive-band assertion |
| Visibility does not prove transport | The local gamma bound supplies visibility, not the full transported certificate or arbitrary-dimensional BFGS convergence | Retained limitation; no missing transport premise may be silently supplied |
| Semialgebraic subgradient graph | For finite convex semialgebraic F, its quantified global supporting-plane graph is semialgebraic | Pending general real semialgebraic quantifier-elimination/projection layer |
| Semialgebraic affine-critical set | At most n+1 subgradients suffice in an affine representation of zero, yielding a semialgebraic affine-critical set | Pending finite affine representation theorem plus semialgebraic closure under finite products, quantifiers, and polynomial relations |
| Finite semialgebraic path components | The affine-critical set has finitely many components, any two points in each joinable by a semialgebraic path with finitely many C1 pieces | Pending general semialgebraic decomposition theorem; ordinary topological path connectivity does not provide the required regularity or finiteness |
| Path derivative identity | Where p and F composed with p are differentiable, the scalar derivative equals inner(g,p') for every g in partial F(p) | Pending elementary supporting-plane calculus. F itself need not be differentiable at p(t), and no continuous subgradient selection is assumed |
| Constancy on affine-critical paths | A finite affine combination of subgradients equal to zero forces the derivative of F composed with p to vanish; finite piecewise C1 decomposition and continuity imply pathwise constancy | Pending. Constancy is not inferred from an arbitrary continuous path or an unchecked almost-everywhere assertion |
| Finitely many affine-critical values | Finite path-component decomposition plus pathwise constancy makes the image of the affine-critical set under F finite | Pending consequence after the preceding prerequisites |
| Low-level affine-critical gap | If finite convex semialgebraic F attains Fstar, some epsilon>0 satisfies F(p)<Fstar+epsilon and affine criticality imply zero in partial F(p) | Pending full semialgebraic theorem. Compactness, uniqueness, and a finite smooth-branch representation are not assumed |
| Positive-gap choice | Fstar belongs to the finite affine-critical value set; choose epsilon below the least strictly larger value, or any positive epsilon if there is none | Pending finite-set argument; handle an empty set of larger critical values explicitly |
| No blanket dynamic conclusion | Finite affine-critical values and the low-level AC gap do not force a BFGS cluster point to be affine critical | Retained limitation. Modules C and U establish restricted dynamical cases, not the full implication |
| Explicit general-dimensional conjecture | Finite convex C2,1 maxima, unique minimizer, compact low sublevels, affinely independent active gradients, strictly positive optimal weights, and positive weighted Hessian on Ustar are conjectured to give local full-BFGS convergence for arbitrary SPD initialization | **Explicitly unproved conjecture.** Record its exact proposition if useful, but do not report it as a proved retained theorem |
| Limits of related theorems | The planar strict-contour theorem and the fixed-normal arbitrary-dimensional theorem do not settle that conjecture | Retained limitation; their hypotheses/classes differ |
| Nonlinear coordinate warning | Straightening an active manifold by a nonlinear coordinate transformation does not preserve ordinary BFGS and cannot close the conjecture | Retained limitation. Only a proved applicable invariance theorem may transform an actual run |

## Semialgebraic theorem: exact missing prerequisites

The source proof is a plausible complete informal route; no contradiction was
established in this review. It relies on substantial external geometric results
which are not present as ready-to-use theorems in the pinned checkout. They must
be proved in Lean or obtained as dependencies with checked proofs. Adding a
custom axiom for any of them would violate the project requirements.

1. Define real semialgebraic subsets of finite-dimensional coordinate spaces,
   allowing real coefficients, and semialgebraic functions through their
   graphs. Prove the elementary finite Boolean and Cartesian-product closures.
2. Prove real projection closure / real-closed-field quantifier elimination.
   The supporting graph contains a universal quantifier over all ambient y:
   `F y >= F x + inner(g,y-x)`. Merely recognizing polynomial formulas with
   no quantifiers is insufficient.
3. Define the actual convex subdifferential as the global supporting-vector
   set. Stationarity `0 in partial F x` is then directly equivalent to global
   minimality. General subgradient existence is needed for the affine-projection
   section and should be proved from finite convexity; the attained-minimum
   case itself has the trivial supporting vector zero.
4. Prove affine Caratheodory: affine-span membership can be witnessed using
   at most n+1 points with real coefficients summing to one, without imposing
   nonnegative coefficients. Convex Caratheodory alone does not establish this
   statement. A basis of subgradient differences gives a direct finite-dimensional
   route. Pad shorter representations by repeated points or use a finite union
   over all lengths to obtain a fixed finite quantified formula.
5. Prove that semialgebraic sets have finitely many semialgebraically path-connected
   components. The source needs paths inside the affine-critical set, not just
   paths in its closure, and the finite-component conclusion is global, not
   restricted to a compact truncation.
6. Prove the needed finite regularity decomposition of a semialgebraic path
   and its scalar semialgebraic composition with F. A continuous path on [0,1]
   must admit a finite partition where both functions are C1 on each open
   piece, with continuity at partition endpoints. Endpoint derivatives need
   not exist. A common refinement of two finite partitions is sufficient.
7. Supply the ordinary calculus argument and finite-value/gap argument described
   below. These are independent of semialgebraic projection and can form useful
   intermediate checked results, but their geometric premises must remain
   explicit until items 1–6 are discharged.

A theorem assuming a finite partition into suitably regular path-connected
pieces would be a useful conditional analytic result. It would not establish
the full semialgebraic proposition. Similarly, a proof restricted to a finite
polyhedral or polynomial-branch representation would be a restricted theorem,
not a silent replacement for arbitrary finite convex semialgebraic objectives.

## Elementary pathwise proof to isolate first

Fix a parameter t in an open path interval and a supporting vector g at p(t).
The supporting inequality shows that

```
u |-> F (p u) - inner(g,p u)
```

has a local minimum at t. If p and F composed with p both have derivatives
there, `IsLocalMin.hasDerivAt_eq_zero` gives
`(F composed with p)'(t) = inner(g,p'(t))`. This proves the source's two-sided
subgradient chain identity without differentiability of F at p(t), bounded
subgradient paths, or a choice of continuously varying supporting vectors.

At an affine-critical p(t), take a finite affine representation
`sum lambda_j*g_j=0`, `sum lambda_j=1`. Summing the derivative identities gives
the scalar derivative zero. Apply the ordinary mean-value theorem on each
open partition interval; continuity then identifies endpoint values and joins
the finitely many constants. This avoids claiming that derivative zero merely
almost everywhere suffices for an arbitrary continuous function.

The finite set of path-component values has a global minimum equal to the
attained Fstar, because the minimizer is stationary and hence affine critical.
Removing Fstar leaves either no larger values or a finite set with a strictly
positive minimum gap. The strict low-level inequality in the source can use
that gap directly, or a smaller positive number.

## Pinned mathlib inspection

The inspection used the project's `leanprover/lean4:v4.19.0` toolchain and locked
mathlib checkout. The following are source-located primitives; no new API calls
were compiler-tested during this read-only inventory.

| Available primitive | Pinned source / relevant API |
|---|---|
| Actual affine orthogonal projection | `Mathlib/Geometry/Euclidean/Projection.lean`: `EuclideanGeometry.orthogonalProjection`, membership, orthogonal-direction, and continuous affine-map facts |
| Linear orthogonal projection | `Mathlib/Analysis/InnerProductSpace/Projection.lean`: `Submodule.orthogonalProjection` and its orthogonality characterization |
| Affine independence and extraction | `Mathlib/LinearAlgebra/AffineSpace/Independent.lean`: `exists_affineIndependent`; finite-dimensional cardinal/rank facts in `AffineSpace/FiniteDimensional.lean` |
| Convex Caratheodory | `Mathlib/Analysis/Convex/Caratheodory.lean`; useful finite-dimensional infrastructure but not a replacement for arbitrary signed affine coefficients |
| Matrix inverse continuity | `Mathlib/Topology/Instances/Matrix.lean`: `continuousAt_matrix_inv`; already used with proved nonzero determinant in `IncomingJumpObstruction.lean` |
| Ordinary path components | `Mathlib/Topology/Connected/PathConnected.lean`: `JoinedIn`, `Path`, `pathComponentIn`, and continuous-map lemmas |
| Derivative at a local minimum | `Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`: `IsLocalMin.hasDerivAt_eq_zero` |
| Constancy from zero derivative | `Mathlib/Analysis/Calculus/MeanValue.lean`: `IsOpen.is_const_of_deriv_eq_zero`, convex-domain and Fréchet variants |
| Existing objective support and limits | Project `ConvexAnalysis.lean`, `CompactConvergence.lean`, and `LocalizationCorollaries.lean`; actual derivative/supporting-vector limits are being developed separately |

Searches for `semialgebraic`, `semi-algebraic`, `semianalytic`, `o-minimal`,
`ominimal`, `Seidenberg`, and semialgebraic/cell-decomposition filenames found
no appropriate definitions or theorems anywhere in the pinned `Mathlib` source.
The model-theory directory has general formula semantics and ring definability,
and algebraically closed field theory, but no real-closed-field quantifier
elimination was located. The occurrences of “Tarski” concern fixed points and
the Tarski–Vaught test, not the needed real projection theorem. Neither ordinary
topological paths nor algebraically closed-field geometry supplies the missing
ordered-real semialgebraic result.

## Review cautions for subsequent formalization

- Quantitative affine distances and Hessian constants use the Euclidean metric.
  The coordinate model's default finite-Pi norm may be used for equivalent
  topology but must not silently replace a displayed Euclidean quantity.
- The rank-loss example deliberately violates lower semicontinuity of gamma
  at zero: gamma(0)=1 while nearby vertical values tend to zero. Global AC is
  compatible with this failure. A compactness proof of uniform visibility must
  not overlook this example.
- In the barycentric theorem, prove full column rank for the augmented matrix,
  not invertibility of a generally rectangular matrix. Its square Gram matrix
  is invertible; its least-squares expression is a genuine solution only where
  the displayed system is solvable.
- Missing active indices are extended by zero before using coefficient
  uniqueness. Positivity of the pseudoinverse coefficient formula then rules
  out those missing indices; assuming all original active indices remain
  active would add an unwarranted identification hypothesis.
- A proof of local lower semicontinuity must handle singleton active sets and
  the zero-dimensional difference matrix, not assume at least two active
  branches. The compact-band positivity consequence only applies inside the
  neighborhood where the rank/AC conclusions hold.
- The final conjecture is an explicit research obligation, not an omitted
  theorem proof. Verifying its formulation or the two restricted positive
  classes does not mark that conjecture solved.
