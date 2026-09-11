# Module Q inventory and proof design

Source `BFGS_MASTER_REPORT_LaTeX/report/chapters/Q.tex` was read in full. This is a design/review inventory, **not a formal-verification claim**. No Lean source is introduced in this tranche and the research source is unchanged.

## Exact objective class and primary conclusion

`F(u,v)=max_i (a_i*u²+b_i*v)` for an arbitrary finite nonempty index family, with every `a_i>0`, at least one `b_i<0`, and at least one `b_i>0`. Equal slopes, redundant pieces, tie-only pieces, and essential pieces with zero normal slope are allowed in the original input. The two slope witnesses ensure at least two branches; this must not be replaced by an assumed regular upper envelope.

For every infinite admissible ordinary full-BFGS run, every initial SPD matrix, and every fixed `0<c1<c2<1`, the primary theorem concludes both `x_k→(0,0)` and `F(x_k)→0`. It is a positive theorem for this planar family. It makes no line-search-existence or finite-oracle-complexity assertion.

The second section supplies one explicit three-branch objective that meets the new certificate condition but fails the radial secant condition on positive levels in every neighborhood of the minimizer. The constructed pairs use varying SPD matrices; they are one-step BFGS realizations, **not an asserted single infinite bad run**. The class's actual runs converge by the primary theorem.

## Obligations for the arbitrary finite family

| Item | Exact claim and dependencies | Boundary / degeneracies |
|---|---|---|
| Q.C1 finite convex objective | Every branch is differentiable and convex; finite maximum is real-valued and convex. An active branch gradient equals the gradient of F wherever F is differentiable. | Must handle differentiable ties, duplicated slopes, and `u=0`; unique branch activity must not be assumed. |
| Q.C2 compact sublevels/minimizer | A convex combination of positive/negative slope branches gives `F≥a_min*u²`. Extreme slopes bound v above and below. Minimum is zero uniquely at origin. | Negative sublevels may be empty. No division by an intermediate `b_i`. |
| Q.E1 finite-envelope reduction | Merge equal slopes by largest a, remove globally redundant/tie-only pieces, obtain increasing distinct slopes with strictly increasing adjacent breakpoints. | Must derive reduction for every original family and prove it preserves the objective and gradients at differentiable points. It cannot remain an extra final-theorem hypothesis. |
| Q.E2 positive interface values | `A_i=a_i+b_i*ξ_i=a_(i+1)+b_(i+1)*ξ_i>0`. | Follows from the same `a_min` bound at u=1. |
| Q.E3 calibration | `k_(i+1)-k_i=-(a_(i+1)-a_i)/(2*A_i)` gives matching exponents at each retained switching interface. | Finite recursion, with zero-length cells already removed. |
| Q.W1 finite positive scaling | `θ=exp(a_i*u²/(2F)+k_i)` on active cells; it agrees on ties and extends over `u=0,F>0`. Uniform `0<θ_min≤θ≤θ_max<∞` follows from `0≤u²/F≤1/a_min`. | No extension/continuity at origin is claimed or needed. |
| Q.P1 pair identities | For active old i and new j: `d−Δ=a_i*h²+e`; `t=(a_i+a_j)*h²+e+ebar`; `g·r(x)=2F(x)`; `y·r(z)=2*a_i*h*u'+2e`. | i,j need not be adjacent. e,ebar nonnegative by actual maxima. |
| Q.P2 secant bound | `N²/t ≤ 4*a_i²/(a_i+a_j)*u'²+4e`; eligible pairs have `h²≤d/a_min`, `e≤d`. | Prove by cross multiplication / weighted Cauchy–Schwarz, avoiding division by h or e when either is zero. t>0 is derived from eligibility. |
| Q.V visibility | `gᵀWg=θ²*(g·r)²≥4*θ_min²*η²>0`. | Actual visibility is `g·r=2F`; no nonzero coordinate, nonzero normal slope, or positive definiteness of W is required. W has rank one, possibly with a direction varying by position. |
| Q.D1 quotient denominator | `D=det(s,r(x))`; on a positive band and for sufficiently small eligible d, derive `d≤C*abs D` and `abs h≤C*abs D`. Hence D≠0. | Do not assume D≠0, nonparallel gradients, small normal displacement, adjacent branches, u≠0, or b_i≠0. |
| Q.D2 determinant mechanism | `det(g,y)*D=−d*(y·r(x))−2F(x)t`, with `y·r(x)=−2t+ε`, `abs ε≤C*(abs h+d)`. Absorb `d*(sqrt(d/a_min)+d)` using t≥(1−c2)d. | Never divide by det(g,y); a zero determinant is ruled out where necessary by eligibility and small d. |
| Q.D3 zero-slope-safe identity | `b_i*D=2F(x)*h+u*d` yields h bound after D bound. | Divide only by positive band value F(x), **never by b_i**. If b_i=0, this identity still works. |
| Q.T1 exact quotient transport | `λ=1+h*ell/D`; `r(z)−λ*r(x)` is parallel to s; `λ−1+(a_i*u/F(x))*h=−v*h*d/(F(x)*D)`. | h and/or normal displacement may vanish. D is derived nonzero. |
| Q.T2 logarithmic cancellation | Derive λ=1+O(sqrt d)>0, `log λ=−a_i*u/F(x)*h+O(d)`, and old-index exponent increment has opposite first order. | Constants and sufficiently small δ must be uniform over every eligible pair in the fixed positive band. |
| Q.T3 arbitrary-switch exponent bound | `abs(L_j(z)−L_i(z))≤C*e/F(z)` on normalized compact arc `{t≥0,max_i(a_i*t+b_i*v)=1}`. | Need exact finite-cell geometry; allow extreme cells ending at t=0 and zero-slope cells. Do not assume adjacent i,j. |
| Q.T4 compensated transport | `abs(log(θ(z)*λ/θ(x)))≤Cη*d`; projected rank-one Loewner expansion ≤`exp(2Cη*d)`, then ≤`1+Lη*d` for small d. | Supplies exactly T's objective-pair certificate, not a trajectory condition. |
| Q.END actual run conclusion | Build `HasBandCertificates` for every nonempty positive sublevel band; invoke the verified Module T convergence theorem and unique origin. | Must discharge all coefficient/envelope assumptions from the original arbitrary finite family. |

## Simplifications available without changing the proof's conclusions

The source's Taylor estimate in `(u,F)` admits this exact identity, useful to avoid a separate multivariable remainder theorem:

```
[a_i*u'²/(2*F(z)) − a_i*u²/(2*F(x))] − (a_i*u/F(x))*h
  = a_i*h²/(2*F(x)) + a_i*u'²*Δ/(2*F(x)*F(z)).
```

It follows from `u'=u+h` and `Δ=F(x)−F(z)`. On `η≤F≤B`, the right side is nonnegative and bounded by a constant times `h²+Δ≤C*d`.

A convenient explicit scaling bound is `θ_min=exp(min k_i)` and `θ_max=exp(max k_i+a_max/(2*a_min))`; neither requires a nonzero b_i.

For the finite-cell estimate Q.16, formulate and prove a reusable compact-segment lemma: if a nonnegative affine function D and an affine function E have `D=0 → E=0` on a segment, then `abs E≤C*D` there. The general finite polygonal arc follows by finitely many cells. This avoids an informal distinction between proportional adjacent-cell functions and strictly positive nonadjacent deficits, while retaining its content.

## Explicit three-branch separation

Objective:

```
max(u²+v, 3u², 2u²−v).
```

Interfaces are `v=−u²` and `v=2u²`. Scaling is the displayed piecewise exponential, continuous on `F>0`, with `exp(−1/3)≤θ≤1` and θ=1 in the zero-normal-slope middle region.

For the printed pair with old `v=2u²+ε` and new `v=2u²−ε/2`:

* `u≠0`, `A>0`, `0<ε<6u²` ensure both endpoints lie in their stated differentiable cells.
* The displayed H is SPD with determinant `A*(3ε/2)` and satisfies the exact unit-length step equation.
* `d=t=3ε/2`, `Δ=ε`, so the pair is eligible only when **c1≤2/3** (strict Armijo if c1<2/3). Weak Wolfe is strict for every c2>0.
* Radial correction diverges to infinity at positive limiting value `3u²`, while d→0; transported correction is `2ε/3→0` and the compensated logarithm is the displayed `ε/[6(3u²+ε)]`.

### Scope limitation and a proposed explicit generalization

The printed construction does not cover c1>2/3. It is valid as stated with its printed strict-Armijo restriction. If the separation theorem is intended for **every** allowed fixed c1, use the following generalized pair and document the extension:

```
zε=(u,2u²−ρ*ε),
H22=4u²*A+(1+ρ)*ε,
ρ>0, c1*(1+ρ)<1, ρ*ε<3u².
```

Then `d=t=(1+ρ)ε`, `Δ=ε`, the old/new gradients remain `(2u,1)` and `(6u,0)`, and the exact unit-step identity and SPD determinant `A*(1+ρ)ε` persist. The radial numerator is `(2u²+ρ ε)²`, while the transported numerator is `(2ρ ε)²`. The compensated logarithm is unchanged because θ(z)=1. Every c1<1 permits such ρ. This is an explicit proof extension; it must not be silently attributed to the printed ε/2 pair.

## Gap assessment

No contradiction was found in the general finite-branch proof. The following are compressed source arguments requiring substantial formal proofs, not justified assumptions:

1. Arbitrary finite-envelope pruning and ordered-cell construction, preserving gradients at differentiable ties.
2. The uniform finite-cell estimate Q.16 including t=0 extreme endpoints, zero-slope cells, and arbitrary nonadjacent branch pairs.
3. Uniform δ and constants through denominator absorption, positivity of λ, logarithmic remainder, and final exponential bound.
4. Explicit positive-band/neighborhood quantifiers for radial failure; one-step varying H must not be promoted to a single infinite run.

There is **no zero-visibility defect** on a positive band: `g·r=2F≥2η`. If b_i=0, positive F forces u≠0; if u=0 and F>0, an extreme nonzero slope supplies visibility. No proof may globally divide by either coordinate or an arbitrary normal slope. The only identified parameter-coverage limitation is the explicit pair's c1≤2/3 range described above.

## Proposed Lean APIs and implementation order

1. `ParabolicFamily`: finite coefficient data with `a_pos`, positive-slope and negative-slope witnesses; actual `objective : Vec 2 → ℝ`, branch values/gradients, active predicate.
2. `parabolic_convex`, `parabolic_unique_minimum`, `parabolic_sublevel_compact`, `gradient_eq_active_branch` (including differentiable ties).
3. `pair_identities` and `pair_secant_bound`, quantified over actual active endpoints and exact `TransportedCertificate.EligiblePair`.
4. `small_eligible_denominator_bounds`: ∃C>0,δ>0, ∀ eligible band pair d≤δ, d≤C|D| ∧ |h|≤C|D|. D≠0 follows, not assumed.
5. `EnvelopeCalibration` as an intermediate **derived witness**, `envelope_calibration_exists` for every original family; include active coverage, matching exponents, and Q.16. No final theorem may assume this witness independently.
6. `calibrated_band_certificate`: constructs the existing `BandCertificate` with actual W=θ²rrᵀ.
7. `parabolic_run_convergence`: invokes the already verified T primary theorem.
8. Explicit three-branch branch regions, theta bounds, generalized one-step eligible pairs, radial divergence, and transported correction/log identities; then exact RS failure on every neighborhood for the intended fixed-parameter scope.

## Fourth milestone progress

ParabolicFamily, ParabolicPairs, ParabolicDenominatorAlgebra, ParabolicDenominator
and ParabolicUniformSecant now have 43 compiled theorems and 12 audited
definitions. Compactness/unique minimum, actual active gradients, Q.9--Q.14,
uniform Q.13 with derived D!=0, and unscaled visibility/secant estimates are
verified. See PARABOLIC_FOUNDATION_REVIEW.md and parabolic_foundation_axioms.log.
The finite-envelope calibration, Q.15--Q.17, main convergence theorem and
explicit separation remain open in this released milestone.
