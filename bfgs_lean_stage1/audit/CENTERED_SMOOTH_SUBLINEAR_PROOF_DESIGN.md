# Centered smooth-plus-sublinear proof design

Status: design only. No theorem in this note is counted as Lean verified.
Owned future modules: `CenteredSmoothSublinear.lean` and uniquely named local
smoothness/calculus helpers. Existing reverse/central files are frozen for the
third integration audit.

## Exact source scope

Source: `report/chapters/families.tex`, first section, Theorem F:centered and its
proof and recentering paragraph. The smooth summand need only be convex and
locally C1,1 on an open convex neighborhood U of the compact initial sublevel K.
The nonsmooth summand gamma is globally finite, convex, and degree-one positively
homogeneous. The given center minimizes the sum; neither summand is assumed to
be minimized there. Differentiability of gamma at accepted endpoints must be
derived from differentiability of F and psi. The conclusion allows a nonunique
minimizer and is value convergence; uniqueness then gives iterate convergence.
A local representation near a unique minimizer must give a low-starting basin.

The actual correction to prove is

    (dot (g' - g) (x' - star))^2 / dot (g' - g) (x' - x)
      <= L * R^2 + 2 * G_gamma * R,

with constants derived from the objective and compact set, not from the run's
matrix sequence. The curvature denominator is positive for the actual run, but
the separate smooth and homogeneous curvature contributions may be zero.

## Simplified existence-of-constant route

The theorem does not prescribe L before its hypotheses: one may choose any
sufficient uniform smoothness constant. Consequently the centered theorem does
not require a sharp, externally prescribed-L version of Baillon--Haddad on all
of U. Compactness permits the following direct proof, with exact final formula
for the chosen L and without increasing the field assumptions.

1. Formalize local C1,1 using `DifferentiableOn` (or pointwise `HasFDerivAt` on
   open U) and `LocallyLipschitzOn U (fderiv ℝ psi)`. The latter is standard local
   Lipschitz continuity of the derivative in the existing finite-Pi norm. No
   Euclidean convention is silently imposed on that norm.
2. A finite cover of compact K supplies M >= 0 and rho > 0 such that for each
   x in K, the derivative is M-Lipschitz on the full ball B(x, rho), and this
   ball lies in U. For each local neighborhood choose a radius e_x with the
   ball of radius 3e_x inside it; cover K with the e_x balls, take a finite
   subcover, a positive lower bound on these radii, and a common upper bound
   on the finitely many local Lipschitz constants. Any B(x, rho) lies in one
   selected 3e_x ball. Empty compact sets can be handled separately, although
   the actual initial sublevel contains the center.
3. The same local derivative hypothesis gives continuity of the coordinate
   gradient p(x)_i = fderiv psi x (Pi.single i 1) on U. Compactness bounds its
   actual Euclidean square sum by G_psi^2 on K, with G_psi > 0.
4. On each local ball, apply the first-order mean-value estimate to
   psi(z) - dot p(x) z on the segment from x to z. Its derivative is bounded by
   M * ||z-x||_infinity on that segment. This yields

       |psi(z)-psi(x)-dot p(x)(z-x)| <= M * ||z-x||_infinity^2
                                                <= M * sqNorm(z-x).

   This deliberately elementary remainder estimate has coefficient M instead
   of M/2. Choose L >= 2M; then its coefficient is at most L/2. Because L is
   selected existentially, this is the source's L-smooth upper estimate for
   the selected L, with no loss in the final displayed correction formula.
5. Also choose L > 0 and 2G_psi/L < rho. For x,x' in K let u=p(x')-p(x).
   Both test points x' - u/L and x + u/L lie in the local balls. Local Taylor
   upper estimates there, together with the convex supporting plane at x or
   x', give the two inequalities

       sqNorm u <= 2L * (psi(x')-psi(x)-dot p(x)(x'-x)),
       sqNorm u <= 2L * (psi(x)-psi(x')-dot p(x')(x-x')).

   Adding gives `sqNorm u <= L * dot u (x'-x)` exactly. There is no assumed
   cocoercivity and no need for gradient convergence, a Hessian, integration,
   or an extension of psi beyond U.
6. Cauchy--Schwarz and sqNorm(x'-star)<=R^2 give xi^2 <= LR^2 a. Convexity
   supplies a>=0. Gamma's supporting inequality and Euler identity at the
   actual differentiable endpoints give 0<=zeta<=b, b>=0, and
   zeta<=2G_gamma R. Thus zeta^2<=(2G_gamma R)b.
7. Prove the denominator-free scalar lemma: for a,b,A,B>=0,
   xi^2<=A*a and zeta^2<=B*b imply
   (xi+zeta)^2 <= (A+B)*(a+b). This follows from weighted Cauchy--Schwarz or
   the identity (A*b-B*a)^2>=0 after the two numerator bounds. Handle a=0
   and b=0 by deriving the corresponding numerator equals zero. Apply the
   actual curvature positivity only at the last division.
8. Feed the derived constant correction to existing actual-run energy/value
   convergence exports. Compactness/uniqueness and localization are separate
   wrappers, using the existing compact convergence and basin modules.

This verifies the centered theorem and its stated correction estimate for one
uniformly chosen L. It does not, by itself, verify the independent sharp claim
that every prescribed Lipschitz derivative constant on arbitrary open convex U
is also the exact cocoercivity constant. That broader auxiliary theorem must not
be advertised as covered by this route. If required separately, short-pair
local descent proofs plus segment subdivision provide a simpler route than the
quadratically adjusted four-point proof (see below).

## Optional prescribed-L extension

If the derivative is already L-Lipschitz in the Euclidean norm throughout U,
use the true L/2 Taylor estimate on sufficiently short subsegments. For adjacent
points the two descent test points remain inside a uniform tube around the
compact segment [x,x']. This gives local L-cocoercivity. Subdivide into m equal
steps s/m; Cauchy--Schwarz and telescoping give

    ||sum_i u_i||^2 <= m sum_i ||u_i||^2
      <= m L sum_i dot u_i (s/m) = L dot (sum_i u_i) s.

This uses only the original convex function and avoids proving nonexpansion for
a quadratically adjusted nonconvex function. A true L/2 Taylor estimate can be
obtained by differentiating the scalar remainder minus (L/2)t^2||s||^2 and
applying `antitoneOn_of_hasDerivWithinAt_nonpos` on [0,1].

## Recentring

Derive the supporting inequality `dot (-p(star)) z <= gamma z` by testing the
minimum condition at star+t*z for small positive t and passing t down to zero.
Positive homogeneity makes the gamma term exactly t*gamma(z); differentiability
of psi at star gives the smooth directional limit. Set

    psi_bar(x) = psi(x) - psi(star) - dot p(star) (x-star),
    gamma_bar(z) = gamma(z) + dot p(star) z.

Convex supporting planes make psi_bar>=0 on U; the derived inequality makes
gamma_bar>=0 globally. Both vanish at the center/zero, gamma_bar remains finite
convex positively homogeneous, and their sum is exactly F-F(star) wherever the
original representation holds. No objective-transform invariance of BFGS is
claimed or used.

## Located pinned-mathlib APIs

- `LocallyLipschitzOn` / `.continuousOn`:
  `Mathlib/Topology/EMetricSpace/Lipschitz.lean`.
- `IsCompact.elim_finite_subcover`: `Topology/Compactness/Compact.lean:173`.
- `Metric.mem_nhds_iff` extracts ordinary positive-radius balls. Open U converts
  nhdsWithin to nhds; intersect local neighborhoods with U before shrinking.
- `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`:
  `Analysis/Calculus/MeanValue.lean:420`. Its proof already handles the segment
  parameterization, so the elementary coefficient-M remainder needs no new
  one-dimensional calculus machinery.
- `antitoneOn_of_hasDerivWithinAt_nonpos`:
  `Analysis/Calculus/Deriv/MeanValue.lean:490`, for the optional sharp remainder.
- Existing `gradientFunctional_coordinates` and `coordinateGradient` connect
  the actual derivative to finite coordinate gradients.
- A local version of `convex_supporting_inequality` is needed: compose psi with
  the line map, restrict its preimage to U, and apply
  `ConvexOn.le_slope_of_hasDerivAt` to 0 and 1. The endpoint derivative is an
  ordinary derivative because U is open. This must not strengthen convexity to
  all of the space.
- Existing `convex_supporting_bound_on_compact` bounds gamma subgradients on
  compact sets. Euler plus global domination makes a single bound at zero a
  global bound for all gamma supporting vectors; alternatively a compact
  translated initial sublevel is sufficient for accepted endpoints.

## Further proof reductions located during the integration freeze

The recentering directional inequality need not formalize a new limit argument:
apply `IsLocalMinOn.hasFDerivWithinAt_nonneg` to the scalar function
`q(t)=psi(star+t*z)+t*gamma(z)` on `Ici 0` at zero. It agrees with the minimized
objective for nonnegative t in a neighborhood of zero. The vector 1 is in the
positive tangent cone by `mem_posTangentConeAt_of_segment_subset`. Its derivative
is exactly `dot p(star) z+gamma(z)`. This discharges the center support inequality
without assuming differentiability of F or gamma at the minimizer.

`norm_sub_le_of_mem_segment` in `Analysis/Normed/Module/Convex.lean:123` is the
specific segment radius estimate for the elementary Taylor bound. The existing
`Homogeneous.global_supporting_bound`, `supporting_euler`, and
`supporting_linear_le` already prove gamma's global boundedness and support
identities without positivity/coercivity of gamma. They should be reused.

The anticipated generic compact theorem is:

    exists_cocoercivity_constant_on_compact
      (hU : IsOpen U) (hconvex : ConvexOn ℝ U psi)
      (hsmooth : LocallyC11On U psi)
      (hK : IsCompact K) (hKU : K ⊆ U) :
      ∃ L > 0, ∀ x ∈ K, ∀ x' ∈ K,
        sqNorm (coordinateGradient psi x' - coordinateGradient psi x)
          ≤ L * dot (coordinateGradient psi x' - coordinateGradient psi x) (x'-x).

The source main wrapper will use local equality on U, so the same theorem covers
both global and locally represented objectives. No global convexity assumption
on psi outside U is introduced. The actual run itself supplies global convexity
of F as part of its existing exact specification.
