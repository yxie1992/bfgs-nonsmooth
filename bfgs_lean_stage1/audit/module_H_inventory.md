# Module H formalization inventory

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/H.tex` (read in full).
Original sources are preserved. This inventory separates the checked H.A and H.B tranches
from later obligations; complete project verification is recorded by the root audit. All statements concern unmodified full BFGS with fixed Armijo–weak
Wolfe and nonzero gradients at differentiable accepted iterates.

## H.A core tranche — compiled and individually axiom-audited

Files: `Homogeneous.lean`, `HomogeneousDichotomy.lean`,
`HomogeneousConsequences.lean`. Pinned builds and individual axiom reports are
recorded in `audit/homogeneous_build.log`, `audit/homogeneous_dichotomy_build.log`,
`audit/homogeneous_consequences_build.log`, and `audit/homogeneous_axioms.log`.
Only standard Lean axioms occur in these reports. Full root integration remains
subject to the comprehensive project audit.

The finite-limit proof uses the verified superquadratic reciprocal theorem,
rather than the source's qualitative liminf argument. Summability is derived
from the same finite-value/Armijo premises. A fixed positive absolute-value lower
bound on a shifted tail contradicts the normalized actual reference-energy
budget. This changes the proof route without changing any H.A hypothesis or
conclusion.

### Checked claims

1. Finite convex positive degree-one homogeneity is real-valued on the whole
   finite-dimensional space. No finite-piece or finite-gradient assumption.
2. Every supporting vector satisfies Euler `g·x=F(x)` and `g·z≤F(z)` for every
   `z`; equivalently it supports at zero. All supporting vectors have one global
   finite Euclidean bound, independently of where accepted points lie.
3. Actual-run identities: `h=y·x_next=d−Δ≥0`, `ell=−y·x≥0`, `t=h+ell`;
   `h²/t≤h≤((1−c1)/c1)Δ`. The exact reference-zero energy and homogeneous
   potential `Phi=E+((1−c1)/c1)F` have the source recurrence/inequality.
4. H.A: every infinite admissible run has values tending either to zero or to
   minus infinity. No bounded iterates, displacements, lengths, matrices, or
   finite gradient alphabet. A finite-value branch derives summability from
   Armijo and invokes verified Module M reciprocal growth.
5. Consequences: bounded-below homogeneous objectives are nonnegative with
   minimum zero at the origin; bounded-below runs converge in value to zero;
   finite-value branches have strictly positive values at every iteration;
   attaining a nonpositive value forces escape to minus infinity. Coercivity
   (or bounded sublevels) gives point convergence to zero, without a rate or
   finite-path-length claim.

Dependencies: `AdmissibleBFGSRun`, supporting-vector compact bounds on `{0}`,
Armijo monotonicity/summability, initial-SPD propagation and Hessian identity,
reference energies, and actual-matrix reciprocal-growth exports from Module M.

## H.B finite recurrent alphabet — compiled and individually axiom-audited

Files: `HomogeneousMaxLinear.lean`, `HomogeneousAffineGeometry.lean`,
`HomogeneousAffineObstruction.lean`, `HomogeneousCommonTilt.lean`, and
`HomogeneousCardinality.lean`. Reproduce the module build with the exact command
in `audit/homogeneous_affine_build.log`; `audit/H_B_AxiomChecks.lean` prints the
transitive dependencies of all 37 explicit theorem declarations. Results are in
`audit/homogeneous_affine_axioms.log`; each declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`. Full root integration is a separate audit.

### Checked claims


6. For any full-BFGS finite-gradient run with a lower value bound, the affine hull
   of recurrent gradients contains zero. This algebraic necessity does not use
   homogeneity; finite alphabet gives a tail containing only recurrent gradients.
   Missing affine zero produces a fixed vector pairing to one with every tail
   gradient; Hessian energy then telescopes by exactly `−1/q`.
7. For finite maxima of linear slopes: accepted gradients belong to the slope
   set; absence of affine zero in the full slope set forces value escape.
   The many-piece common-tilt family has a gradient component equal to one.
   No finite-termination claim for this many-piece family.
8. If recurrent gradients span dimension `r`, their number is at least `r+1`.
   The dimension is the actual `Module.finrank` of the linear span; cardinality
   is the actual finite set cardinality of values occurring infinitely often.

The finite maximum is implemented using `Finset.sup'`, not an assumed active
slope selector. Convexity and degree-one homogeneity are proved from the finite
maximum. Every active slope supports the objective; actual differentiability
forces that supporting vector to equal the unique gradient. Thus the final
max-linear results derive their gradient alphabet instead of assuming it.

The algebraic affine obstruction uses the genuine inverse-update identity for
`FullBFGSRun`: unit pairing with consecutive gradients yields exactly
`vᵀ B_(k+1) v = vᵀ B_k v - 1/q_k`. Actual SPD gives nonnegative residual energy,
and the tail reciprocal sum is bounded by its initial energy. Module M's proved
qualitative reciprocal-mean divergence supplies the contradiction. Objective
wrappers derive vanishing predicted decreases by Armijo from the source lower
bound. The core matrix theorem does not assume homogeneity or convexity; its
objective wrapper uses the existing convex admissible-run model.

The coordinate common-tilt corollary writes `x=(t,u)` (tilt first rather than the
source's last coordinate) and proves equality with the actual finite maximum of
lifted slopes `(1,b)`. This is a coordinate permutation only. No matrix/iterate
convergence, bounded steps, finite lengths, field regularity, or finite
termination assumptions enter. Original research sources remain unchanged.

## Later H.C / Sections 7–8 obligations: projected and low-dimensional iterates

9. Exact projected full-BFGS update on a gradient subspace; q,d,t and line-search
   inequalities are preserved. All later steps lie in the fixed image `H_K S`.
   Derive the actual lift `H_K U (Uᵀ H_K U)⁻¹`, and the source limit formula.
   The projected Hessian is `(Uᵀ H_k U)⁻¹`, not `Uᵀ B_k U`.
10. Homogeneous endpoint pairings tend to zero. Finitely many independent slope
    pairs in dimension two give uniform inverse bounds at transition endpoints.
11. Exclude unchanged/positively proportional active transitions on the positive
    branch; dependent transitions must have opposite slopes. Unbounded-below
    max-linear objectives cannot contain an opposite slope pair.
12. H.C: planar unbounded-below finite maxima have exactly the two source branches
    (iterate→zero, value↓zero) or (value→−infinity, norm→infinity). The zero limit
    is nonstationary. No directional convergence in the escaping branch.
13. General planar finite-value branch: independent-transition anchors→zero;
    opposite-gradient blocks are collinear, with the explicit uniformly bounded
    interpolation coefficient. Finitely many anchors instead give a fixed-line
    limit. Projection/lifting extends convergence to recurrent span dimension≤2.
14. Relative-interior slope condition gives coercivity on the effective span and
    the explicit metric projection limit in any dimension, independent of
    accepted lengths. Include recurrent-tail version; exclude stationary F=0
    from infinite nonzero-gradient runs.

## Explicitly unresolved in the research source

Zero-value iterate convergence for noncompact objectives with recurrent span
at least three, without the relative-interior/coercive-on-span condition, is
unresolved. Formalization must not promote that question into a theorem. Source
references to previous examples and the external two-piece finite-termination
paper are provenance/comparison claims, not proofs supplied by Module H.

Third tranche: AffineProjection/AffineCompression/AffineLifting and their run/fiber wrappers prove exact projected updates and arbitrary-tail fixed lifting (H.7.1). H.C endpoint and planar finite-value convergence remain open. ObjectiveRates.lean also proves the homogeneous finite weighted-sum and o(1/N) rates used in F, including derived Euclidean coercive norm bounds.
