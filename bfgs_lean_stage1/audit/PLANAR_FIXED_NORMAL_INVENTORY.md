# Planar and fixed-normal theorem inventory (Modules C and U)

Read in full: `report/chapters/C.tex` (421 lines) and `U.tex` (419 lines).
This is source-to-proof-obligation mapping, not a claim that C or U has been
Lean-verified. No Lean files were changed. Original sources are preserved.

All dynamical claims concern unmodified full BFGS, arbitrary initial SPD H0,
positive accepted lengths, actual nonzero gradients at differentiable accepted
iterates, and fixed `0<c1<c2<1` Armijo–weak-Wolfe. They neither assert acceptable
length existence on every exceptional ray nor assume convergence of iterates,
matrices, eigenspaces, condition numbers, or path lengths.

## C: retained claims and dependencies

| ID / source claim | Exact retained assumptions and conclusion | Main remaining bridge |
|---|---|---|
| C1 / forced affine-critical cluster point (`C:thm:cluster`) | Finite convex F on R², attained minimum, compact sublevel K={F≤b}, b>F*. Every positive sublevel up to b has no nontrivial boundary segment. At every non-affine-critical p in K, F is locally convex C², or the max of two convex C² branches active at p with linearly independent gradients. Then every admissible run in K has an affine-critical cluster point. No structure is required at affine-critical points. | Construct the comparison field near the **whole hypothetical compact cluster set**, with uniform visibility, secant bound, and near-identity scalar transport; then apply M's moving-frame contradiction. |
| C2 / no false affine criticality (`C:cor:AC`) | Add `0∈aff ∂F(p) ⇒ 0∈∂F(p)` on K. Obtain value convergence to F*, distance to argmin→0, and whole-sequence convergence under uniqueness. The local version uses a low compact sublevel inside a structural neighborhood of a unique minimizer. | Affine-critical cluster point→optimal common cluster value; reuse compact-convergence/localization exports. |
| C3 / nondegenerate planar smooth maxima (`C:cor:max`) | Unique minimizer; near it, finite maximum of convex C² branches; strictly convex sufficiently low positive sublevels; active gradients affinely independent and positive optimal weights. A low objective basin works for every SPD initialization and fixed valid line-search pair. A common positive branch Hessian lower bound is sufficient for strict contours. | Active-set reduction and barycentric stability; affine-independent planar active sets have ≤3 members, and at a noncritical point have one or two relevant branches with independent gradients. |
| C4 / affine geometry (§2) | Stationary cluster point suffices for convergence in value. The minimum-norm point a of aff ∂F(p) has `g·a=||a||²` for every subgradient. At a non-affine-critical point, `-a/||a||²` is an equal-rate descent direction. | Actual affine projection/subdifferential geometry. This is not vanishing accepted gradients. |
| C5 / strict-contour steps (`C:lem:steps`) | Under positive finite limiting value, compactness and no boundary segment at the limiting sublevel imply s_k→0. Armijo gives summable d; finite convexity gives compact supporting-vector bounds. | Already available in `StrictContours.lean` and objective-budget modules in arbitrary dimension; package the source contour premise. |
| C6 / finite corners and joined field (§4) | A compact non-affine-critical subset C of a regular positive level has finitely many relevant C² corner curves p_j(t), with v_j=p_j' and both active gradient pairings equal to one. Strict contours make distinct corner normal arcs disjoint. Fixed disjoint angular cutoffs construct positive h and `w=h n+h_θ T`, equal to v_j(F(x)) near corners. | Implicit-function charts, finite buffering, supporting-normal arcs, circle cutoffs/periodicity, local Lipschitz gluing, uniform visibility and bounds. No convex-support-function property of h is needed. |
| C7 / endpoint estimates (`C:lem:trans`, `transport`, `secant`) | For all sufficiently close eligible differentiable pairs in one buffered neighborhood: uniform `|det(s,w)|≥κ||s||` along the segment; `w(z)=λw(x)+βs`, λ>0, `|log λ|≤Cd` and λ²≤1+C'd; `(y·w(z))²/t≤C0`. | Closed supporting-vector limits and Wolfe for transversality. AC segment calculus and total objective variation≤2d for transport. Local convex smooth estimates plus crossing-specific `t≥c||s||` for the secant bound. |
| C8 / BFGS energy (§6) | Actual Hessian energy satisfies `E_next=λ²(E-(g·w)²/q)+(y·w_next)²/t`. Visibility, secant bound, and summable scalar transport imply an O(N) reciprocal sum, contradicting M. | Exact identity and tail moving-frame machinery are checked; derive bounded cumulative scalar transports/inverses from the source `|log λ|≤Cd`. No new algorithm premise. |
| C9 / semialgebraic alternative (§7) | Finite convex semialgebraic objectives have finitely many affine-critical values. A low level then has no false affine-critical points. Combined with C1, this gives the stated **planar strict-contour regular-two-branch** local class without positive optimal weights. | Semialgebraic subgradient/affine-critical descriptions, finite piecewise-C¹ path components, two-sided supporting-chain-rule identity and constancy on each component. This external geometric infrastructure is not supplied by M and remains unverified. |
| C10 / explicit quadratic basin (§8) | For the three displayed quadratic branches, Hessians lie between I and 3I, F≥u²+v², and zero is the unique minimizer with weights 1/3. The displayed affine coefficients are positive on the 1/10 box: denominator≥267/100, numerators≥23/100,49/100,45/100. Thus F(x0)<1/100 implies x_k→0. | Exact polynomial identities/inequalities, actual finite maximum and active-set geometry, then C3/C2. Numeric checks do not discharge these claims. |
| C11 / same example outside RS (§8.1) | On the curved f0=f1 tie, `v=(-1+sqrt(1+4u+2u²))/2`, f2 is inactive for small u>0. The radial jump pairing is `u²/2-v²≠0`. The displayed vertical crossings have exact d,t,Δ and are eligible for c1=1/4,c2=1/2 as epsilon→0. Radial correction diverges on a positive band in every neighborhood of zero. | Prove tie/activity, exact crossing derivatives/values, nonzero limiting numerator, eligibility, and threshold quantifiers. This only excludes RS, not convergence or all transported fields. |
| C12 / any-dimensional partial construction and warning (§9) | Under finite convex C² maxima and constant rank of each local fixed gradient-difference family, a bounded equal-rate field with bounded secant correction can be joined by a partition of unity. **Transport does not follow.** For Q=diag(1,2,3), x=(1,1,1), and the displayed epsilon-step, d=epsilon², the displayed t and determinant are exact, the pair is eligible, and the canonical field fails rank-one projected transport for every multiplier. | Constant-rank inverse/affine-projection regularity and buffered partitions; local one-sided smooth Bregman estimate. Exact quadratic counterexample to that particular field's transport. The radial field still works. |

The relevant C6–C7 proof details must remain visible in formalization: an
infinite number of segment crossings with a C² tie curve is permitted; transport
uses absolute continuity rather than a finite-crossing assumption. In a crossing
chart, gradient independence plus Wolfe gives curvature linear in ||s||; it is
not replaced by an assumed positive Hessian lower bound. A global field must be
constructed around all cluster points, not merely one selected subsequence.

## U: retained claims and dependencies

| ID / source claim | Exact retained assumptions and conclusion | Main remaining bridge |
|---|---|---|
| U1 / one exceptional hyperplane (`U:one`) | Arbitrary finite dimension; unit a, P={a·x=b}; unique minimizer x* in P; compact initial sublevel. On an open convex neighborhood: positive strong convexity, all subgradients share tangential projection A(x) with A Lipschitz, and F is locally C¹,¹ off P. Then value/iterate convergence. P may contain differentiable points with non-Lipschitz gradient. | Construct cutoff frame from the hypothetical positive-level cluster set and apply M's residual-frame theorem. Local trapping gives a basin independent of H0 and fixed line-search constants. |
| U2 / composite family (§1.1) | F(u,v)=psi(u,v)+h(v), psi convex with locally Lipschitz gradient, h finite convex and locally C¹,¹ off zero, F strongly convex near the compact sublevel, optimizer v*=0. Coupled objective and coupled H0 are allowed. | Exact subgradient/derivative decomposition with tangential A=∇u psi. No uniform normal smoothness approaching zero. |
| U3 / tangential-curvature extension (§1.1, §6) | Same composite regularity, but only `psi-mu||u||²/2` convex with mu>0, strictly convex relevant positive sublevels, compact initial sublevel, unique optimizer v*=0. No positive normal curvature lower bound. | Derive `d-Δ≥mu||P_Ss||²/2`, projected secant bound `||P_Sy||²≤L t`, nonvanishing tangential gradient on nonoptimal exceptional points, and s→0 from strict contours. |
| U4 / parallel singular interfaces (`U:parallel`) | Finite convex F, attained minimum, compact sublevel, strong convexity on an open convex neighborhood; fixed unit a and closed E; every point of Σ={a·x∈E} genuinely nondifferentiable, F locally C¹,¹ off Σ, common Lipschitz tangential subgradient projection. Then an affine-critical cluster point exists. No finite number of interfaces or critical points is assumed. | Subdifferential on Σ is an actual nontrivial compact segment parallel to a; its affine hull is A(p)+R a, so affine criticality iff A(p)=0. |
| U5 / convergence from U4 (§2) | Add no false affine criticality on the compact basin, or on a sufficiently low trapped neighborhood. Then values tend to the minimum, and uniqueness gives whole-sequence convergence. | Same compact-cluster reduction as C2. U1 is not a literal special case of U4 because U1 permits smooth exceptional points. |
| U6 / common cutoff-frame proof (§5) | Strong convexity gives `d-Δ≥mu||s||²/2`, `t≥mu||s||²`, hence s→0; Lipschitz A gives the smooth-tangent secant bound. Z={p in Γ:A(p)=0} has scalar image separated from closed E. Choose a Lipschitz tau that vanishes on an exceptional strip and equals one on r(Z). Set V=[U,tau(r)a]. | Compact cluster-set/neighborhood facts; exceptional zero exclusion; explicit empty-E/empty-Z cases; orthonormal tangent coordinates; uniform visibility, bounded secant correction on smooth strips, and the exact residual identity below. |
| U7 / frame algebra (§5.5) | For beta=(tau(r(z))-tau(r(x)))/(a·s), with beta=0 at zero denominator: `V(z)=V(x)+s beta e_nᵀ-beta P_Ss e_nᵀ`, `|beta|≤Lip(tau)`. Residual lies in S and has Frobenius square≤`2 Lip(tau)² d/mu`. Transport matrix is exactly I. | Direct rectangular matrix algebra, including the zero-denominator case. Feed all derived bounds to checked `residual_frames_on_tail_incompatible_source`; no Hessian subblock growth is assumed. |
| U8 / infinite normal-curvature spikes (§7) | The displayed disjoint C¹ bump series k and integrated r are finite, convex, globally C¹, C³ away from zero, locally C¹,¹ off zero; `r'≤6v²`, `r≤6v³` near zero; r''(0)=0 but `r''(a_j)=a_j⁻³→∞`. F=half||u||²+half v²+|v|+r(v) is 1-strongly convex/coercive with sole kink hyperplane v=0 and Lipschitz tangential gradient u. U1 gives global convergence in every n≥2. | Locally finite series, disjoint supports, total mass, integral derivatives, exact bounds and regularity, then objective wrapper. No truncated oracle can certify these infinite-series claims. |
| U9 / failure of RS and exact oracle (§7, §7.1) | At x_j=(u0,a_j), u0≠0 fixed, radial Hessian energy=`||u0||²+a_j²+a_j⁻¹→∞` on a positive band. Thus inward Taylor bounds and RS fail in every optimizer neighborhood. Polynomial antiderivatives give exact partial mass/moment, geometric tails, and peak identities `r(a)=64a³/315+a⁷/6`, `r'(a)=8a²/9`, `r''(a)=a⁻³`. | Actual inward-Taylor second derivative necessary bound and radial equivalence; formal series/integration algebra for the oracle. Recorded numerical BFGS runs are provenance only, not mathematical verification. |
| U10 / variable jump magnitude (§7.2) | For ||c||<1, F=half(||u||²+v²)+|(1+c·u)v|+r(v) is strongly convex with unique minimizer zero. In a neighborhood |c·u|<1/2, sole exceptional hyperplane v=0 and A=u+c|v| is Lipschitz. U1 gives local convergence; the same spikes exclude local RS. | Actual two-quadratic Hessian bound `(1-||c||)I`, local derivative/subgradient formulas, and radial spike limit. To demonstrate a family outside additive smooth-plus-univariate splitting, choose c≠0. |

The U cutoff is a proof object derived from F and the hypothetical whole cluster
set; it is not an algorithmic input. For tau(r(z))>0, the endpoint has a fixed
positive distance from E, so sufficiently short segments stay in a buffered
smooth strip; compactness supplies a common local C¹,¹ constant there. No
uniform smoothness constant as the strip shrinks toward E is required.

## Existing foundations and unverified bridges

- Checked M infrastructure: initial-SPD propagation, actual Hessian update,
  Armijo budgets, compact supporting-vector bounds, qualitative and
  superquadratic reciprocal growth, `StrictContours.lean`, `MovingFrame.lean`,
  and `ResidualFrames.lean` / `ResidualSourceForm.lean`. `CompactConvergence.lean`
  supplies the final value/argmin-distance/unique-limit implications.
- `HomogeneousAffineGeometry.lean` supplies general affine separation into a
  common component, but not full subdifferential affine projections, normal
  arcs, or barycentric stability of varying smooth gradients. Module A's
  actual subdifferential and finite-max geometry must be proved/reused.
- The current integration's `ConvexGradientLimits.lean` and radial/inward
  equivalence modules support later endpoint and negative-RS arguments; their
  presence is not C/U completion. Local convex cocoercivity, strong-convex
  subgradient monotonicity, chart buffering, and the whole-cluster-set field
  constructions remain substantial new obligations.
- Suggested order after the shared affine lifting tranche: U fixed-normal
  frame algebra plus analytic objective hypotheses→U1/U4; C barycentric local
  geometry; C planar angular field and endpoint estimates; then exact examples
  and semialgebraic infrastructure. Each final theorem must derive its frame
  conditions, not assume the desired comparison field.

## Source precision findings and limits

No gap invalidating the main C/U theorem statements was found on this reading.
The following minor points need explicit treatment during proof development:

1. C uses n=(cos theta,sin theta), T=(-sin theta,cos theta) and the ordered basis
   (T,n). This basis has determinant -1. With the standard ambient determinant,
   the displayed identity `det(s,Dw s)=s_n[(e-a)s_T-b s_n]` has the opposite
   sign. Its absolute-value inequality and all subsequent transport estimates
   are unchanged. State the norm bound directly or document the orientation.
2. C's arbitrary-dimensional field has C¹ regularity from C² branch data.
   “Smooth” there must not be strengthened to C-infinity without stronger
   branch assumptions. C¹ regularity is sufficient for the retained secant
   construction, which deliberately does not claim transport.
3. U's variable-jump example allows c=0 in its displayed hypothesis. That case
   is still a valid convergent example, but its jump does not vary with u and
   it is additive. The claim demonstrating non-additive behavior needs c≠0.
4. The source's general-dimensional smooth-max conjecture with weighted
   tangential curvature remains a conjecture. Neither C nor U proves it;
   nonlinear straightening of a switching manifold cannot be used as an
   invariance of ordinary BFGS. Exact numerical examples and source citations
   cannot replace the missing geometric or dynamical proofs.
