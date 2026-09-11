# Actual linear-image projection and affine lifting

The bounded shared F/H lifting tranche compiles on pinned Lean 4.19.0 and pinned
mathlib. All 49 explicit public theorems, plus the actual `projectRun`
construction, were individually audited for transitive axiom dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Comprehensive root
integration is a separate audit.

Reproduce the exact build command from `audit/affine_lifting_full_build.log`.
`audit/AffineLiftingAxiomChecks.lean` is the reproducible axiom-check source;
`audit/affine_lifting_axioms.log` records its actual compiler output and exit code.
The modules contain no proof placeholders, custom axioms, unsafe declarations,
native decision procedures, or externally supplied mathematical computations.

## Checked modules and statements

- `AffineProjection.lean`: rectangular A from R^n to R^r; full row rank means
  injectivity of its actual transpose action. Arbitrary SPD H compresses to
  actual SPD A H Aᵀ. The explicit right inverse J=Aᵀ(AAᵀ)⁻¹ and fixed lift
  L=H Aᵀ(A H Aᵀ)⁻¹ satisfy A J=A L=I. Actual derivative descent through
  F=barF∘A is proved using the affine section through the point; the forward
  chain rule and derivative uniqueness prove g=Aᵀ gbar.
- `AffineCompression.lean`: the exact rectangular inverse-BFGS compression
  identity, projected executed step and energy, and preservation of a fixed
  annihilator of H range(Aᵀ). The compression identity itself has no denominator
  or positivity premises; genuine run positivity is proved separately.
- `AffineImageRun.lean`: `projectRun A hA barF R` constructs an actual
  `AdmissibleBFGSRun r barF`. It derives reduced convexity, actual accepted
  derivatives, nonzero gradients, initial SPD, the full unmodified update,
  Armijo, and weak Wolfe. The step lengths, q, d, curvature t, and objective
  values are exactly those of the original run. No projected gradient oracle
  or projected recurrence is assumed.
- `AffineLifting.lean`: for actual gradients g_k=Aᵀ gbar_k, proves
  H_k Aᵀ=L0(A H_k Aᵀ), every executed step s_k=L0 A s_k, and
  x_k=x_0+L0(A x_k-A x_0). A projected iterate limit gives the original
  iterate limit through this fixed matrix. These identities require no
  global objective factorization and do not infer one.
- `AffineFiberProjection.lean`: the explicit point
  p=x0+H Aᵀ(A H Aᵀ)⁻¹(z-Ax0) lies in the actual fiber Ax=z. Proves the exact
  Pythagorean identity in H⁻¹ for every point in that fiber. SPD derives both
  minimum initial-metric squared distance and uniqueness of its minimizer.
- `AffineImageLifting.lean`: end-to-end `F:lifting` uses convergence of the
  genuine `projectRun` and returns the original limit, fiber membership, and
  unique metric minimizer. Projected optimality lifts to original optimality;
  unique projected optimality identifies the full original solution fiber.
  Arbitrary finite-tail iterate/limit formulas prove the algebraic H.7.1–H.7.2
  implication with the actual current H_K and x_K.

## Statement review and limits

The projected gradient in arbitrary row coordinates is Jᵀg, and its transpose
lift AᵀJᵀg=g is proved at accepted points. It is not incorrectly identified with
Ag for a non-orthonormal A. The compressed matrix is A H_k Aᵀ; its inverse is
never replaced by A H_k⁻¹ Aᵀ. Initial SPD may be arbitrary and fully coupled.
No matrix convergence, step bound, path-length bound, or compact-iterate
assumption is present in these results.

The only limit premise in `projectRun_limit_lift` is the reduced-iterate limit
specified by the source lifting theorem. The construction of the reduced run,
the matrix invariant, and the exact lift have no convergence premises. A
reduced optimizer need not be unique to get a lifted optimizer; uniqueness is
used only for identification of all original minimizers with that one fiber.

For H.C/H.8, recurrent-tail gradient membership is enough for the exact lift,
but a homogeneous finite-max projected objective still needs the discarded
nonrecurrent-slope/local-derivative bridge. Relative-interior coercivity, planar
transition/anchor arguments, and the general low-effective-rank conclusions
remain separate obligations. No H.C classification or H.8 coercivity theorem
is claimed by this algebraic/actual-run tranche. Research sources are unchanged.
