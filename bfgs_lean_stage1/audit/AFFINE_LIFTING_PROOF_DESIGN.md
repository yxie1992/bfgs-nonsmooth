# Shared exact projection and affine-fiber lifting: proof design

Status: design only, prepared during the frozen milestone integration. No new
Lean source was created for this design. Source references are `F:lifting` in
`report/chapters/families.tex`, H.7.1–H.7.2 and H.8.1 in `H.tex`. The currently
checked rectangular determinant-compression theorem is not an exact projected
objective-run theorem; the latter remains to be implemented as described here.

## Scope and exact dimensions

Use `A : Matrix (Fin r) (Fin n) ℝ`, acting from `Vec n` to `Vec r`.
Define `FullRowRank A := Function.Injective Aᵀ.mulVec`. This is exact linear
independence of the rows, not a spectral or uniform lower-bound assumption.
Its equivalence with surjectivity of `A.mulVec` can be exported, but is not
needed as an additional premise. For an arbitrary SPD `H : Mat n`, define

```
compress A H := A * H * Aᵀ
lift A H := H * Aᵀ * (compress A H)⁻¹
rightInverse A := Aᵀ * (A * Aᵀ)⁻¹
```

`metricGram_posDef hH hA`, with compression columns `Aᵀ`, proves actual
compressed SPD. The nonzero determinant and actual inverse follow. In
particular `A * lift A H = 1` and `A * rightInverse A = 1`. No orthonormality of
A or special initialization is imposed. The formulas remain total in dimension
zero; an actual infinite nonzero-gradient run on the zero-dimensional reduced
objective is excluded by its run fields, not by a hidden rank assumption.

For general A, the reduced gradient is the unique vector `gbar` such that
`g = Aᵀ.mulVec gbar`. It is *not* `A.mulVec g` unless the rows are orthonormal.
One concrete definition is `gbar = (rightInverse A)ᵀ.mulVec g`; equivalently
`(A*Aᵀ)⁻¹.mulVec (A.mulVec g)` once gradient membership is proved.
For H's orthonormal U, use `A=Uᵀ`; then `gbar=Uᵀ g` exactly as in the source.

## Bounded implementation tranche 1: rectangular algebra

Suggested file: `AffineLiftingAlgebra.lean`, independent of objective convexity.
Use actual matrix multiplication and the project's `inverseBFGS`, `bfgsStep`,
`metricEnergy` definitions. Export the following exact identities.

1. `dot (Aᵀ.mulVec u) v = dot u (A.mulVec v)` and compatible rectangular
   outer-product identities. Existing `BFGSCompression.congruence_outer` helps;
   its square-only left/right outer helpers need rectangular counterparts.
2. If `g=Aᵀ*gbar`, then the projected step is
   `A*(-α H g) = -α*(A H Aᵀ)*gbar` and both q values are equal.
3. For arbitrary H, s, ybar, with `y=Aᵀ*ybar`,

   ```
   A * inverseBFGS H s (Aᵀ.mulVec ybar) * Aᵀ =
     inverseBFGS (A*H*Aᵀ) (A.mulVec s) ybar.
   ```

   This equality itself needs no positivity or denominator premise: both sides
   use the same total scalar inverse after the actual curvature identity.
   Write `P=I-rho*s*yᵀ` and `Phat=I-rho*(A*s)*ybarᵀ`. Then `A*P=Phat*A`,
   `Pᵀ*Aᵀ=Aᵀ*Phatᵀ`, and compress the rank-one increment. The objective wrapper
   separately derives positive curvature and SPD from its existing run theorem.
4. Strengthen the source's range invariant to the exact matrix relation

   ```
   H_k * Aᵀ = L0 * (A * H_k * Aᵀ),
   L0 = H_0 * Aᵀ * (A * H_0 * Aᵀ)⁻¹.
   ```

   The initial case is inverse cancellation. For the inductive step, current
   gradient and secant change in `range Aᵀ` imply `s=L0*(A*s)`.
   `P*L0=L0*Phat`, followed by the exact compressed update, proves the next
   matrix relation. This avoids a dimension-counting proof of equality of
   `H_k range(Aᵀ)` and `H_0 range(Aᵀ)` while proving at least the needed fact.
5. Every actual step satisfies `s_k=L0*(A*s_k)`. Induction in the accepted-step
   recurrence proves

   ```
   x_k = x_0 + L0.mulVec (A.mulVec x_k - A.mulVec x_0).
   ```

   Thus all displacements lie in `range(H_0*Aᵀ)`, a fixed subspace determined
   by arbitrary initial SPD H0. There is no iterate/matrix convergence premise.

A generic trajectory version should take genuine update/step recurrences and
an explicit gradient-in-range condition. The actual objective wrappers below
discharge these conditions. A finite-prefix version follows from the already
checked `AdmissibleBFGSRun.shift`, replacing 0/H0/x0 by K/HK/xK.

## Bounded implementation tranche 2: actual objective and derivative bridge

Suggested file: `AffineImageRun.lean`. Final API:

```
projectRun (A) (hA : FullRowRank A) (barF : Vec r → ℝ)
  (R : AdmissibleBFGSRun n (fun x => barF (A.mulVec x))) :
  AdmissibleBFGSRun r barF
```

No reduced derivative, gradient alphabet, or matrix recurrence is assumed.
Derive convexity of barF from `R.convex` by composition with the linear right
inverse J, since `F(J z)=barF z` globally.

At an accepted x, define the affine section
`σ_x(z)=x+J*(z-A*x)`. It sends A*x to x and has `A*σ_x(z)=z` everywhere.
The known actual derivative of F at x, composed with σ_x, therefore proves
that barF has derivative represented by `Jᵀ*g` at A*x. Apply the forward chain
rule to `barF∘A`; uniqueness of the derivative identifies `g=Aᵀ*gbar` as actual
coordinate vectors. This is the essential surjective derivative bridge; merely
postulating `g=Aᵀ*gbar` would not verify `F:lifting`.

Use `A.mulVecLin` and `LinearMap.toContinuousLinearMap` for the exact Pi-norm
matrix action. Their finite-dimensional continuity gives the chain rule and
later limiting continuity. Existing `gradientFunctional_apply` identifies each
functional by the dot identity; coordinate evaluation identifies gradient
vectors. No differentiability away from accepted iterates is required.

The projected run fields are

```
xbar k = A.mulVec (R.x k)
Hbar k = A * R.H k * Aᵀ
gbar k = Jᵀ.mulVec (R.g k)
alphaBar = R.α; c1Bar = R.c₁; c2Bar = R.c₂.
```

Compressed initial SPD is derived; `gbar≠0` follows from `g=Aᵀ*gbar` and the
original nonzero-gradient field. The exact rectangular algebra supplies the
step and inverse-update fields. Value identity and dot-product identity supply
Armijo and weak Wolfe with the same accepted lengths/constants. Export q, d,
beta, curvature t, value, and projected displacement equality lemmas explicitly.
The reduced Hessian is `(A H_k Aᵀ)⁻¹`; it is never asserted to be `A H_k⁻¹ Aᵀ`.

## Bounded implementation tranche 3: limits and metric fibers

Suggested file: `AffineLifting.lean`, importing the actual-run bridge.
The strongest useful limit theorem only needs `A*x_k → zstar`. Continuity of
the fixed affine lift and the exact iterate formula give

```
x_k → x_0 + L0.mulVec (zstar - A.mulVec x_0).
```

The source's unique-optimizer case is a specialization: any retained theorem
proving convergence of the actual projected run supplies that premise. Do not
build unique optimality or convergence into the projected run or its algebra.

Prove the metric projection independently of convergence. Put
`p=x0+L0*(zstar-A*x0)` and `B0=H0⁻¹`. Then A*p=zstar. For every x in the same
fiber, A*(x-p)=0 while `B0*(p-x0)=Aᵀ*(A H0 Aᵀ)⁻¹*(zstar-A*x0)`. The cross
term therefore vanishes and the actual quadratic forms satisfy

```
metricEnergy B0 (x-x0) =
  metricEnergy B0 (p-x0) + metricEnergy B0 (x-p).
```

SPD of B0 proves p minimizes this metric distance on the fiber and equality
holds only at x=p. This verifies the precise metric-fiber claim without
assuming a preexisting projection operation or an unchecked optimization result.
If zstar is the unique optimizer of barF, the full minimizer set is exactly this
fiber; otherwise only this particular fiber is covered. Runs with the same x0,
H0 and projected limit have the same original limit regardless of their
accepted lengths. No general convergence theorem for arbitrary nonunique
minimizer sets follows from this statement.

## H.7.1 and the recurrent-tail subtlety

The algebraic tail lift needs only that the actual tail gradients lie in a
fixed S. Given orthonormal U spanning S, set A=Uᵀ, use the shifted run and
apply the strong invariant. This proves H.7.1–H.7.2 directly, with arbitrary HK.

For a general convex objective whose *visited* gradients lie in S, one cannot
silently claim that its whole objective factors through Uᵀ. Two valid bridges:

- The exact lift gives an affine restriction
  `Fhat(z)=F(xK+LK*(z-Uᵀ*xK))`. Along the lifted actual tail it preserves values;
  the chain rule and gradient-in-S give the genuine projected gradient.
  Convexity is inherited by this affine composition. This suffices for a
  general projected actual-run statement, but does not imply homogeneity of
  that restricted objective.
- For homogeneous finite max-linear H.C/H.8, replace the original slope set by
  its actual recurrent subset G after the last nonrecurrent gradient visit.
  Every visited gradient is in G and is active; every other G slope is still
  an original supporting slope. Thus the two maxima have exactly the same
  accepted values. At a differentiable original accepted point every active
  slope equals the gradient (already proved in `HomogeneousMaxLinear`).
  Finiteness supplies a strict local margin against each distinct inactive
  slope, so both maxima locally equal the same linear form and have the same
  actual derivative. Package a genuine tail run on the reduced maximum,
  retaining its exact accepted matrices, steps, values, and line search.
  This objective globally factors through Uᵀ, with slopes `Uᵀ*g` for g in G.
  The shared linear-image bridge now yields a homogeneous finite max-linear
  projected run of dimension `finrank(span G)`.

The second bridge is needed before applying planar max-linear classification
to the recurrent tail. Merely assuming a projected active-gradient alphabet or
projected objective homogeneity would leave the crucial reduction unproved.

## H.8 coercivity and original metric projection

When zero is in the relative interior of the convex hull of the original
slopes, relative to their actual span S, derive a positive ball in S contained
in that hull. Its support-function inequality gives
`f(x)≥mu*||Uᵀ*x||` for some mu>0. H.A then gives projected iterates tending to
zero. The preceding exact lift and Pythagorean fiber result prove H.8.1 and its
H0⁻¹ metric projection characterization. The recurrent-tail case uses the
reduced maximum bridge first, then the same argument with HK and xK. No step
length, path length, matrix bound, or matrix limit is introduced.

The planar endpoint/anchor arguments remain a later bounded H.C tranche.
Dimension zero has no infinite nonzero-gradient run. The source's open
noncoercive recurrent-span-at-least-three iterate question remains open.
