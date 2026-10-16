# M42 hypothesis examples — implementation report

**Status: complete; ready for independent review.**

16 October 2026. Implemented only
`bfgs_lean_article/BfgsArticle/HypothesisExamples.lean` in the repository.
All production names are under `BfgsVerification.HypothesisExamples`.

- Starting revision supplied by coordinator: `6145363`; initial worktree was clean.
- Final source: 792 lines, SHA-256
  `39134726105a010df070f544fcba0bb8d186cce212546dafdf9017a3b7ad778a`.
- Production module: compiled successfully, **zero errors and zero warnings**.
- Import-based scratch check: **33 principal axiom checks**, all exactly
  `[propext, Classical.choice, Quot.sound]`; zero errors and zero warnings.
- No mathematical assumptions remain undischarged beyond the explicit
  quantifiers below. No `sorry`, `admit`, custom axiom, `native_decide`, `unsafe`,
  opaque proof device, or linter suppression is present.
- Imports are direct mathematical `BfgsVerification.*` modules. The archived
  higher-rank proof's `Coverage.Article.Energy` dependency was removed; geometric
  convergence is proved directly. No root or coverage-module import is used.
- Existing Lean, registers, manuscript, TODOs, package configuration and frozen
  stage1 sources were not edited. No git mutations or Lake builds/updates/cleans
  were run. Other worktree changes visible at completion belong to concurrent work.

## 1. Actual structure types and conventions

| Mathematical object | Actual Lean representation |
|---|---|
| Euclidean coordinates | `BfgsVerification.Vec n = Fin n → ℝ` |
| Real square matrix | `BfgsVerification.Mat n` |
| Squared Euclidean norm | `sqNorm x = ∑ i, x i ^ 2` |
| Euclidean norm bridge | `Quadratic.objective_euclidean` uses `euclideanVector x` |
| Actual full-space gradient | `HasFDerivAt F (gradientFunctional g) x` |
| Infinite full-BFGS history | `AdmissibleBFGSRun n F`, including convexity, nonzero actual gradients, positive step lengths, initially SPD matrix, full update, Armijo and weak Wolfe |
| One positive-band certificate | `TransportedCertificate.BandCertificate F K 0 c₁ c₂ η` |
| Positive band | `TransportedCertificate.positiveBand F K 0 η = {x | x ∈ K ∧ 0 + η ≤ F x}` |
| Minimum value | `IsLeast (Set.range F) 0`, plus `∀ x, F x = 0 ↔ x = 0` for uniqueness |
| Gauge representation | `MaxAffine.Family 2 3` with the three literal slopes and zero offsets |
| Nonnegative degree-one homogeneity | `Homogeneous.PositiveDegreeOne F`, quantifying over every `t ≥ 0` |

`BandCertificate` stores `C : ℝ`, without a nonnegativity field. Both
`certificate_parameters` and both `joint_witness` theorems explicitly include
`0 ≤ B.C`. Thus their contracts meet the article's extra nonnegative-`C`
convention, not just the frozen library structure.

The coordinate-space topology is the finite-Pi topology, equivalent to the
Euclidean topology. The quadratic is explicitly the Euclidean `sqNorm / 2`,
not half the square of the Pi/sup norm.

## 2. Principal names and locations

All line numbers refer to `bfgs_lean_article/BfgsArticle/HypothesisExamples.lean`.
Prefix every short name with `BfgsVerification.HypothesisExamples.`.

### Quadratic

| Name | Line | Contract |
|---|---:|---|
| `Quadratic.objective` | 31 | `sqNorm x / 2` in arbitrary dimension |
| `Quadratic.objective_euclidean` | 39 | Literal Euclidean norm identity |
| `Quadratic.objective_hasGradient` | 48 | Actual gradient `x` at every point |
| `Quadratic.sublevel_compact` | 73 | Every real sublevel is compact |
| `Quadratic.certificate` | 79 | Identity certificate, arbitrary `K`, arbitrary real `c₁,c₂`, every `η>0` |
| `Quadratic.certificate_parameters` | 102 | Exact constants, `0≤C`, SPD field, rank exactly `n` everywhere |
| `Quadratic.exact_field_equalities` | 111 | Secant and projected-transport equalities for all pairs |
| `Quadratic.inverseBFGS_identity` | 125 | The full inverse update fixes `I` when `y=s` |
| `Quadratic.run` | 170 | Actual infinite run for every nonzero prescribed `x₀` |
| `Quadratic.run_values` | 193 | Exact geometric objective formula |
| `Quadratic.run_scalars` | 197 | Exact `q,d,Δ,t` formulas |
| `Quadratic.run_weak_wolfe_eq` | 214 | Weak Wolfe holds with equality |
| `Quadratic.run_limits` | 223 | Direct geometric convergence of values and iterates |
| **`Quadratic.joint_witness`** | **236** | Full joint convexity/minimum/sublevel/certificate/rank/initialization/run/convergence statement |
| `Quadratic.planar_projection` | 262 | Projected identity at `s=(1,0)` equals `diag(0,1)` |
| `Quadratic.planar_run_nonempty` | 270 | Explicit nonzero start `(1,1)` in dimension two |

### Mixed ridge

| Name | Line | Contract |
|---|---:|---|
| `Mixed.objective` / `objective_formula` | 281 / 283 | Literal `u²+|v|`, definitionally the frozen `UnexcitedMetric.objective` |
| `Mixed.sublevel_compact` | 301 | Every real sublevel is compact |
| `Mixed.gradient_eq_of_nonneg` / `gradient_eq_of_nonpos` | 307 / 318 | Actual full-space gradients forced by the supporting slopes |
| `Mixed.differentiable_coordinate_ne_zero` | 328 | Every differentiable endpoint has `v≠0` |
| `Mixed.radial_pairing` | 337 | `gᵀx=2u²+|v|` |
| `Mixed.opposite_sign_bound` | 347 | Division-free weighted Cauchy--Schwarz bound |
| `Mixed.secant_bound` | 359 | Sharp `(yᵀz)²≤2b t` for all differentiable endpoint pairs with `F(z)≤b` |
| `Mixed.projected_transport` | 400 | Exact equality of projected radial fields for every pair |
| `Mixed.certificate` | 416 | The actual radial `BandCertificate` with all displayed constants |
| `Mixed.certificate_parameters` | 434 | Exact field/constants and `0≤C` for `b>0` |
| `Mixed.run` | 441 | Frozen run specialized to `A=1,v₀=2/3,ρ=1/2,c₁=1/4,c₂=1/2` |
| `Mixed.run_points` / `run_gradients` / `run_matrices` | 446 / 454 / 456 | Literal formulas for the displayed history |
| `Mixed.run_initial` / `run_constants` | 463 / 470 | Start `(0,2/3)`, `H₀=I`, fixed constants, `α=1` |
| `Mixed.run_values` / `run_scalars` | 474 / 483 | Objective value and exact `d,Δ,t` |
| `Mixed.run_limits` / `run_matrix_limit` | 506 / 514 | Value/iterate convergence and `H_k→diag(1,0)` |
| **`Mixed.joint_witness`** | **526** | Full conjunction for every `b≥2/3`, including all positive-band certificates and the actual run |
| `Mixed.run_nonempty` | 554 | Explicit non-vacuity |

### Gauge

| Name | Line | Contract |
|---|---:|---|
| `Gauge.family` / `objective` | 560 / 566 | Three literal slopes, zero offsets, finite max |
| `Gauge.objective_formula` | 573 | `max u (max (-u+v) (-u-v))` |
| `Gauge.objective_homogeneous` | 602 | Positive degree-one homogeneity |
| `Gauge.coordinate_bounds` | 609 | `|u|≤G` and `|v|/2≤G` |
| `Gauge.sublevel_compact` / `objective_coercive` | 639 / 644 | Every sublevel compact; cocompact-to-atTop coercivity |
| `Gauge.admissible_runs_converge` | 653 | The actual homogeneous convergence theorem applies to every infinite admissible run |
| `Gauge.initialPoint` / `initialGradient` / `ray` | 660 / 662 / 664 | `(ε,0)`, `(1,0)`, `(ε−α,0)` |
| `Gauge.ray_step` / `ray_gradient_before` | 666 / 672 | Actual identity-metric search ray; constant gradient before the origin |
| `Gauge.ray_value_after` / `ray_not_differentiable_after` | 680 / 688 | Value `α−ε`; full-space nondifferentiability for all `α≥ε` |
| `Gauge.initial_state` | 703 | Positive-value differentiable start, nonzero actual gradient, SPD identity |
| `Gauge.no_differentiable_weak_wolfe` | 718 | No positive differentiable weak-Wolfe step for any `c₂<1` |
| `Gauge.no_admissible_run` | 734 | No infinite admissible run from those prescribed data, for any valid constants |
| **`Gauge.joint_obstruction`** | **754** | All objective hypotheses, initial state, both ray regimes and obstruction together, for every `ε>0` |
| `Gauge.obstructed_state_exists` | 782 | Concrete state `ε=1` establishes non-vacuity of the obstruction |

## 3. Exact TeX-ready statements

### 3.1 Full-rank Euclidean quadratic

For every finite dimension \(n\) and every \(b>0\), let
\[
F(x)=\tfrac12\|x\|_2^2,\qquad K_b=\{x\in\mathbb R^n:F(x)\le b\}.
\]
Then \(F\) is finite, convex and differentiable everywhere, with
\(\nabla F(x)=x\), minimum value zero, unique minimizer zero, and compact
sublevels. For every \(\eta>0\) and every pair of real constants \(c_1,c_2\),
\[
W_\eta(x)=I_n,\quad m_\eta=2\eta,\quad C_\eta=1,\quad
L_\eta=0,\quad\delta_\eta=1
\]
is a band certificate on \(K_b\). Its field is positive definite and has rank
exactly \(n\) everywhere. For every pair \(x,z\), writing \(s=z-x\),
\(y=\nabla F(z)-\nabla F(x)=s\), the secant estimate is equality and
projected transport is equality. The constructor actually works on every set
\(K\), without compactness or an upper-level hypothesis.

For every \(x_0\ne0\), set \(b=F(x_0)>0\). With
\[
c_1=\tfrac14,\qquad c_2=\tfrac12,\qquad
x_k=2^{-k}x_0,\quad g_k=x_k,\quad H_k=I_n,\quad\alpha_k=\tfrac12
\qquad(k\in\mathbb N),
\]
these data form an infinite admissible full-BFGS run, all of whose iterates
lie in \(K_b\). In particular \(H_0=I_n\), all accepted gradients are nonzero,
the full inverse update fixes \(I_n\), and weak Wolfe holds with equality.
Moreover
\[
q_k=\|x_k\|_2^2,\quad d_k=\tfrac12q_k,\quad
\Delta_k=\tfrac38q_k,\quad t_k=\tfrac14q_k,\quad
F(x_k)=4^{-k}F(x_0)\longrightarrow0,\quad x_k\longrightarrow0.
\]
All objective/certificate/initialization/run/convergence facts hold jointly
in `Quadratic.joint_witness`. The Lean theorem quantifies over arbitrary
\(n\), with the nonzero-start premise automatically excluding \(n=0\).
For a genuinely higher-rank example choose \(n=2,x_0=(1,1)\); the field has
rank two, and for \(s=(1,0)\), \(\Pi_s I\Pi_s=\operatorname{diag}(0,1)\).

### 3.2 Mixed ridge and sharp radial certificate

Let
\[
F(u,v)=u^2+|v|,\qquad K_b=\{F\le b\},\qquad b>0.
\]
The objective is finite convex, its minimum is zero attained uniquely at
zero, and every sublevel is compact. For every \(\eta>0\) and every pair of
real constants \(c_1,c_2\),
\[
W_\eta(x)=xx^T,\quad m_\eta=\eta^2,\quad C_\eta=2b,\quad
L_\eta=0,\quad\delta_\eta=1
\]
is a band certificate on \(K_b\), with \(C_\eta\ge0\).

The sharp secant estimate is proved under the stronger quantification:
for every real \(b\), every \(x,z,g,h\in\mathbb R^2\) with
\(F(z)\le b\), \(g=\nabla F(x)\) and \(h=\nabla F(z)\) in the full-space
derivative sense,
\[
\bigl((h-g)^Tz\bigr)^2\le2b\,(h-g)^T(z-x).
\]
There is no eligibility, positive-curvature, small-step, or first-endpoint
sublevel premise in this stronger result. Projected radial transport is an
equality for every endpoint pair, including a zero step in the library's
total projector convention.

For every \(b\ge2/3\), the objective facts and all positive-band certificates
hold jointly with the actual infinite full-BFGS history
\[
c_1=\tfrac14,\quad c_2=\tfrac12,\qquad
x_k=\left(0,\tfrac23(-\tfrac12)^k\right),\quad
g_k=(0,(-1)^k),\quad
H_k=\operatorname{diag}(1,2^{-k}),\quad\alpha_k=1
\quad(k\in\mathbb N).
\]
Its start is \(x_0=(0,2/3)\), \(H_0=I\), and every iterate belongs to \(K_b\).
All accepted points are differentiable, all gradients are nonzero, and both
line-search inequalities and the full update hold. The exact scalars are
\[
F(x_k)=\tfrac23\,2^{-k},\qquad d_k=2^{-k},\qquad
\Delta_k=\tfrac13\,2^{-k}=d_k/3,\qquad
t_k=2\,2^{-k}=2d_k.
\]
Values and iterates tend to zero; separately `Mixed.run_matrix_limit` proves
\(H_k\to\operatorname{diag}(1,0)\).

**Proof detail for review:** the four sign combinations are reduced to the
same-sign estimate and the division-free identity
\[
(a^2+w)(A^2+v+w)-(Aa+w)^2
=w(A-a)^2+va^2+vw\ge0\qquad(v,w\ge0).
\]
For a crossing pair take \(A=z_1-x_1\), \(a=z_1\),
\(v=|x_2|\), \(w=|z_2|\); multiply by four and use
\(a^2+w\le b\). This is the stated weighted Cauchy--Schwarz argument with
its division eliminated. Visibility uses the exact radial pairing
\(g^Tx=2u^2+|v|\), and transport uses \(z=x+(z-x)\).

### 3.3 Covered gauge with an obstructed first search ray

Define
\[
G(u,v)=\max\{u,-u+v,-u-v\}=\max\{u,-u+|v|\}.
\]
It is finite convex and continuous, satisfies
\(G(tx)=tG(x)\) for every \(t\ge0\), has minimum zero uniquely at zero,
and every real sublevel is compact. In particular it is coercive. The
explicit bounds are \(G(u,v)\ge|u|\) and \(G(u,v)\ge|v|/2\).
Every infinite admissible full-BFGS run on \(G\) converges in values and
iterates to zero (`Gauge.admissible_runs_converge`).

For every \(\varepsilon>0\), let
\[
x_0=(\varepsilon,0),\qquad H_0=I_2,\qquad g_0=(1,0).
\]
This is a differentiable positive-value state:
\(G(x_0)=\varepsilon>0\), \(\nabla G(x_0)=g_0\ne0\), and \(H_0\succ0\).
For every real \(\alpha\), its BFGS search ray is
\[
x_0-\alpha H_0g_0=(\varepsilon-\alpha,0).
\]
For \(\alpha<\varepsilon\) the full-space gradient is still \(g_0\).
For \(\alpha\ge\varepsilon\), the objective is not differentiable in
\(\mathbb R^2\); both distinct slopes \((-1,1)\) and \((-1,-1)\) are active.
Consequently, for every \(c_2<1\), every \(\alpha>0\), and every full-space
gradient \(h\) at the proposed next point, weak Wolfe is impossible:
\[
\neg\left[c_2\,g_0^T(-\alpha H_0g_0)
\le h^T(-\alpha H_0g_0)\right].
\]
This statement is independent of Armijo and of \(c_1\); it implies that for
every valid pair \(0<c_1<c_2<1\) there is no infinite admissible run from
these prescribed initial data. All these facts hold jointly in
`Gauge.joint_obstruction` for every \(\varepsilon>0\).

The obstruction is already to the first differentiable accepted step from
a strictly positive objective value. At and beyond the origin, the whole
remaining ray is nondifferentiable in the ambient plane. It therefore
illustrates the distinction between conditional convergence and prescribed
initialization existence, rather than failure of optimization after an
accepted iterate has reached a nonsmooth minimum.

## 4. Non-vacuity and check artifacts

Scratch root:
`/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/calibrations/`.

`Audit.lean` imports a freshly compiled standalone `.olean` of the production
module. It checks signatures, all three concrete full-conjunction specializations,
actual run nonemptiness, a concrete obstructed state, and nonempty positive bands:

- Quadratic: \(n=2,x_0=(1,1),b=1,\eta=1/2\), with `(1,1)` in the band.
- Mixed: \(b=2/3,\eta=1/3\), with `(0,2/3)` in the band.
- Gauge: \(\varepsilon=1\), genuinely differentiable start of positive value.

Files: `PROGRESS.md`, `FINAL_REPORT.md`, `Audit.lean`, `Audit.log`, `Compile.log`,
and the generated `BfgsArticle/HypothesisExamples.olean`. The production file
contains no `#check` or `#print` commands.

Commands run from `bfgs_lean_article/`, sequentially with `LEAN_NUM_THREADS=4`:

```sh
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  BfgsArticle/HypothesisExamples.lean

# S denotes the scratch root above.
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  -o "$S/BfgsArticle/HypothesisExamples.olean" \
  BfgsArticle/HypothesisExamples.lean > "$S/Compile.log" 2>&1

# Prepend S after Lake installs its own LEAN_PATH, so the new standalone module
# is found before the package directory that has no built copy of this module.
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env sh -c \
  'LEAN_PATH="/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/calibrations:$LEAN_PATH" lean /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/calibrations/Audit.lean' \
  > "$S/Audit.log" 2>&1
```

All final commands exited **0**. `Compile.log` is empty, as expected for a clean
compile. `Audit.log` has the resolved signatures and all 33 standard-only axiom
dependency lists, with no diagnostics. The new source is ready for the coordinator's
independent review, coverage wrappers, root import, and normal package-wide checks.

## Fix pass

16 October 2026, original implementation agent. Read and accepted the independent
review in `../review_calibrations/REVIEW.md`: **PASS**, including all 90 public
production declarations, complete joint contracts, and seven independent
consumer/non-vacuity checks. No required core correction or overlooked defect
was identified.

- **S1:** accept the literal smallest-eigenvalue bridge. The separate coverage
  agent owns its integration in `Coverage/Article/HypothesisExamples.lean`, using
  the independently verified `../review_calibrations/SpectralChecks.lean`.
  No duplicate core implementation is needed.
- **O1:** retain the simple printed `b=2/3` numerical example. The broader
  `b≥2/3` contract is already proved by `Mixed.joint_witness`.
- **O2:** the coordinator owns the TeX clarification restricting the printed
  quotient-projector transport statements to eligible, hence nonzero-step,
  pairs. The total Lean projector and existing certificate proofs are valid.
- **Terminology:** “sharp” above describes the requested `C=2b` estimate; the
  implementation does not assert least-possible `C` for a fixed eligible-pair
  class or fixed line-search/band constants, as the review correctly notes.

Disposition complete: no production edit, and the successful compilation and
axiom audits were accepted without rerunning them. Only this report was appended.
