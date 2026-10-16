# Existing Lean evidence: joint satisfiability and actual-run non-vacuity

**Independent formal-evidence review, 16 October 2026.** Repository revision:
`a6f46d13bb31e27e92b27890470c8c0754fb9c80` (clean at the start).
Scope: the article's main energy, global, local/planar, and negative results;
companion evidence is included where it strengthens the article's examples.

## Verdict

**No new vacuous MAIN-result theorem was found.** Every listed article main
result has a satisfiable algebraic/objective core. For every main convergence
class there is existing evidence of an actual infinite admissible full-BFGS
run on a qualifying objective, including runs inside arbitrarily small local
basins. Several of these witnesses are substantially stronger than the
one-dimensional examples at the ends of the article coverage modules.

The strongest positive witness is the article's three-quadratic nonradial
example: Lean proves existence **from every differentiable starting point,
for every SPD initial matrix and every `0 < c₁ < c₂ < 1`**, and gives a concrete
start in the printed `1/100` basin. A companion example also handles an
arbitrarily small positive basin with the same arbitrary-matrix/constants
quantifiers. The negative theorems themselves existentially produce the
infinite runs and their complete deterministic search traces.

There are important distinctions for the author's answer:

1. A theorem about **every infinite admissible run** is not an existence
   theorem for every differentiable start/initial matrix. The latter assertion
   is actually false for the whole coercive homogeneous/polyhedral class:
   the existing five-piece example has a differentiable starting state with
   no acceptable differentiable step.
2. The article-only end-of-module examples are often scalar or objective-only.
   Looking at them alone misses the later companion witnesses and the
   `AdmissibleRunExistence` supplement.
3. I found no instantiated **rank greater than one certificate in dimension
   at least two**. The scalar `W = I` examples are simultaneously full-rank
   and rank-one; all concrete multidimensional certificates located here are
   rank-one. This is an illustration/general-purpose evidence gap, not a
   vacuity or correctness defect in the arbitrary-PSD-field theorem.
4. The PDFs present the important objective examples, but do not present the
   strongest nonradial run-existence theorem or its concrete start. The
   already-recorded Chapter 7 common-tilt existence issue remains separate
   from the article's coercive homogeneous theorem.

## Method and interpretation

Read `HANDOFF.md`, `AGENTS.md`, `editorial/lean_coverage/README.md`, and the
non-vacuity/reviewer instructions in `AGENT_BRIEFS.md`. Read theorem signatures,
definitions, witness constructions, and the relevant TeX. Extracted text from
the actual released PDFs (49 article pages, 108 companion PDF pages), rather
than inferring their contents from register statuses. PDF page references below
are physical PDF pages; companion printed page numbers are six smaller.

`BfgsVerification.AdmissibleBFGSRun`,
`bfgs_lean_stage1/BfgsVerification/ObjectiveDefinitions.lean:30-53`, requires
infinite sequences, actual nonzero gradients at all accepted points, the full
update, and Armijo/weak Wolfe, with SPD assumed only initially. It does **not**
contain convergence, boundedness, a certificate, or a prescribed later matrix
behavior. Thus the `AdmissibleBFGSRun` witnesses below really establish the
requested dynamical non-vacuity.

Evidence levels used below:
- **Objective:** a qualifying objective/geometry is proved, without a run in
  that particular declaration.
- **Run:** an actual infinite `AdmissibleBFGSRun` is exhibited.
- **Uniform existence:** the existence statement quantifies over the specified
  initial matrices/constants, not just the convergence statement.
- **Assembly:** facts already proved in separate declarations fit together;
  distinguish this from a single named theorem asserting the conjunction.

One scratch Lean invocation succeeded with `LEAN_NUM_THREADS=4`: 29 `#check`s
and 14 `#print axioms` commands. All 14 inspected dependencies use only
`propext`, `Classical.choice`, `Quot.sound`. Sources and output are
`Checks.lean` and `Checks.log` beside this report. This subagent made no
repository edits or git writes. A final read-only status showed concurrent
work in `TODO_LEAN_REVIEW.md`, `TODO_MANUSCRIPT_REVIEW.md` and
`editorial/main_results_scope_20261016/`, outside this subagent's work.
Anonymous `example`s have file:line references, rather than invented public
Lean names.

## 1. Energy results

### Principal-minor hierarchy — Theorem 1, article p. 8

**Exact main name:** `BfgsCoverage.Article.Energy.minor_hierarchy`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean:646-677`.
The dimension is arbitrary; hypotheses are SPD `H`, `s = -α • (H *ᵥ g)`,
`α > 0`, the defining equations for `q, β`, and `q, β > 0`. All degrees
`1 ≤ j ≤ n` and the determinant equality are concluded. There is no
objective-level or infinite-run assumption hidden in this algebraic theorem.

The explicit joint algebraic witness is the anonymous example at
`Energy.lean:1701-1709`: `n = j = 1`, `H = Z = U = I`, `g = 1`, `y = -1`,
`α = q = β = 1`, `s = -1`. It does not illustrate intermediate minor degrees.
That narrow example is not a restriction of the theorem. Moreover, the
existing two- and three-dimensional runs below supply actual step instances:
`BfgsVerification.AdmissibleBFGSRun.positive_invariants` and
`.beta_lower_bound`, `bfgs_lean_stage1/BfgsVerification/ObjectiveRun.lean:18-22,55-56`,
prove the required positivity on every step of any such run.

**PDF:** states/proves the general inequality; does not print the scalar
non-vacuity instance. No gap in the main result.

### Reciprocal growth — Theorem 2, article p. 9

**Exact main name:** `BfgsCoverage.Article.Energy.reciprocal_growth`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean:773-781`.
The extra assumptions are precisely bounded Euclidean gradient norms and
`Tendsto R.d atTop (𝓝 0)`.

**Run:** `BfgsCoverage.Article.Energy.Example.run`, same file `1759-1789`,
on `Example.quad` (`1714`), `F(x)=x²/2`, with
`x_k=g_k=2⁻ᵏ`, `H_k=1`, `α_k=1/2`, `(c₁,c₂)=(1/4,3/4)`.
`Example.run_d` (`1839-1841`), `Example.run_summable` (`1843-1844`), and
`Example.run_bounded` (`1846-1856`) discharge both hypotheses. The joint
existential example, including the proof's constants, is `1860-1876`.
This is one initial matrix/constant pair; existence for arbitrary choices is
not asserted by this witness. Multidimensional bounded-gradient compact runs
also fit via the general invariants and summability theorems.

**PDF:** theorem and proof, rather than this explicit geometric-decay run.
No persistent-positive-gap run is needed: those assumptions occur only in
the contradiction argument, not in this theorem.

### Band-certificate convergence — Theorem 3, article pp. 10–11

**Exact main name:** `BfgsCoverage.Article.Energy.certificate`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean:1351-1370`.
Its quantified certificate hypothesis is for every nonempty positive band,
for the run's constants, with `0 ≤ Cert.C`; compactness, attained minimum,
positive upper level and initial membership are explicit.

**Direct joint run/certificate witness:** `Energy.lean:1880-1888` combines
the quadratic run with `K={F≤1}`, `F_*=0` and
`BfgsCoverage.Article.Energy.Example.quadCert` (`1793-1822`):
`W=I`, `m=2η`, `C=1`, `L=0`, `δ=1`. This is dimension one.
`BfgsCoverage.Article.Energy.absCert` (`1252-1300`) and
`.nonsmooth_optimizer_certificates` (`1310-1336`) give the scalar nonsmooth
objective `|x|` for all valid constants; the actual run is
`BfgsCoverage.Article.Global.absRun`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean:1693-1727`.

**Nontrivial multidimensional witnesses are present:**
- The mixed benchmark gives `W(x)=xxᵀ` in dimension two through
  `BfgsCoverage.Article.Global.radial_band_certificate`,
  `Global.lean:649-676`, with the actual `UnexcitedMetric.run` described below.
- More strongly, `BfgsVerification.Parabolic.Family.exists_bandCertificate`
  and `.hasBandCertificates`,
  `bfgs_lean_stage1/BfgsVerification/ParabolicCertificate.lean:16-64`,
  construct the moving field on every compact set for the parabolic family.
  For `F(u,v)=max{u²+v,3u²,2u²-v}`, the explicit field is
  `W=θ²(u,2v)(u,2v)ᵀ`, so the projector/transport requirement is genuinely
  two-dimensional. `BfgsCoverage.Companion.Ch10Q.example_run_exists`,
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch10Q.lean:2593-2602`,
  proves existence from every differentiable start for arbitrary SPD `H₀`
  and every valid pair. `.exampleRun_nonempty` (`2606-2610`) uses `(1,3)`,
  `H₀=I`, `(1/4,1/2)`. This is actual-run non-vacuity of the moving
  certificate, even with flat contours. The library certificate permits real
  `C`; `Energy.hasBandCertificates_iff` (`1198-1217`) upgrades to `C≥0`.

**Rank distinction:** both multidimensional fields just listed are rank-one.
`W=I` on `Vec 1` does not supply a higher-rank example, and its projected
transport is automatic because `Π_s=0`. The certificate-addition theorem
`BfgsCoverage.Companion.Ch03T.certificate_sum`,
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch03T.lean:1136`, is general
closure evidence, not an exhibited rank-two instance. No rank>1 concrete
`BandCertificate` in dimension≥2 was located in either Lean package.

**PDF:** article `energy.tex:234-238,266-270` explicitly motivates one or
several directions but illustrates rank-one radial/contour fields. Companion
`10_Q.tex:230-247` prints the parabolic objective and field. This is a genuine
illustration opportunity for the arbitrary-PSD generality, not a failed proof.

**The conditions are sufficient, not necessary, with a real run:**
`BfgsCoverage.Article.Energy.certificate_not_necessary` (`Energy.lean:1667-1695`)
uses the accumulating-kink objective; its convergence part is non-vacuous by
`BfgsCoverage.Companion.Ch05G.kinkRun`,
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch05G.lean:2985-3037`:
`x_k=-2⁻ᵏ`, `H_k=1`, `α_k=1/2`, `(c₁,c₂)=(1/4,1/2)`, with no certificates on
any positive sublevel for that same pair. The article points to this boundary
at `energy.tex:318-321`.

## 2. Global results

### Inward/radial conditions — Theorem 4 and Corollary 1, article pp. 11–13

**Exact main names:** `BfgsCoverage.Article.Global.radial_equivalence`
(`Global.lean:608-619`) and `.radial_convergence` (`690-710`), in
`bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean`.
The first is the objective-only inward⇒radial implication; the second takes
an actual run. `.radial_implies_inward` (`627-635`) covers the companion converse.

**Objective witness:** `.mixed_inward_condition` (`360`) and
`.mixed_hypotheses` (`1234-1269`) verify `F(u,v)=u²+|v|`, center zero, all
compact sublevels. The anonymous joint example `2238-2286` additionally
exhibits both signs of the radial numerator on a positive band:
`x=(0,1), z=(0,-1)` and `x=(1,1), z=(1/2,1)`.

**Run witness:** `BfgsVerification.UnexcitedMetric.run`,
`bfgs_lean_stage1/BfgsVerification/UnexcitedMetric.lean:139-183`, has

```
x_k = (0, (-ρ)^k v₀),   g_k = (0, (-1)^k),   α_k = 2ρ,
H_k = diag(A, ((1+ρ)/(2ρ)) ρ^k v₀),
A>0, v₀>0, 0<ρ<(1-c₁)/(1+c₁), 0<c₁<c₂<1.
```

Its accepted inequalities and full update are proved in the structure, and
`.run_limits` (`242-256`) proves its limits. This is a two-dimensional
objective and full-matrix run, but the orbit is an invariant axis and the
initial matrix is a special diagonal matrix tied to `v₀,ρ`. The constructor
supports **every valid pair** after choosing `ρ` appropriately; it does not
by itself assert existence for an arbitrary prescribed SPD `H₀` and start.
The joint centered/radial example is `Global.lean:2294-2313`.

**PDF:** article prints the benchmark as Corollary 2 (p. 14), and its inward
mechanism. The explicit orbit/matrix formulas are in companion
`06_F.tex:175-187`, PDF p. 43, printed p. 37. They are not printed as a run
example in the article.

### Centered smooth-plus-sublinear — Theorem 5, article pp. 13–14

**Exact main names:** `BfgsCoverage.Article.Global.centered`
(`Global.lean:1135-1148`), `.centered_global` (`1215-1225`), and
`.mixed_benchmark` (`1281-1288`). The joint witness and run above qualify.

**The centering condition is real:** `hmin` says the same `xstar` minimizes
the full sum whose sublinear term is `γ(x-xstar)`. Smooth loss plus a penalty
centered somewhere else is not automatically a global instance. The paper
states this at `global.tex:129-146`. The local lasso/residual decomposition
addresses many nonzero minimizers, but only locally.

`BfgsCoverage.Article.Global.centered_summands_not_minimized`
(`Global.lean:1156-1197`) witnesses the weaker requirement on the individual
summands with `ψ(x)=x²`, `γ(r)=r`, `xstar=-1/2`, `F=x²+x+1/2`. This is an
**objective-only, scalar smooth** witness for that particular remark; it does
not exhibit a nonsmooth tilted-summand run. It is sufficient for the remark
and does not undermine the nonsmooth benchmark witness for the main theorem.

A substantive limitation already proved in the companion is
`BfgsCoverage.Companion.Ch04R.spectral_RS_fails`,
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch04R.lean:4456-4464`:
smooth plus nuclear norm at a nonzero rank-deficient minimizer can fail the
local radial criterion. `.centered_nuclear_covered` (`4470-4478`) and
`.centered_nuclear_smooth_covered` (`4489`) distinguish the centered case.
The PDF states this distinction at `04_R.tex:413-429`, PDF p. 31.

### Coercive homogeneous objectives — Theorem 6/Corollary 3, article pp. 15–16

**Exact main names:** `BfgsCoverage.Article.Global.homogeneous`
(`Global.lean:1457-1482`), `.homogeneous_examples_norm` (`1537-1548`),
`.homogeneous_examples_gauge` (`1552-1562`), and
`.homogeneous_examples_maxLinear` (`1594-1603`). Their convergence quantifier
is `∀ R : AdmissibleBFGSRun ...`, not `∀ x₀ H₀ c₁ c₂, ∃ R`.

**Scalar witnesses:** the joint anonymous example `Global.lean:2324-2379`
identifies `|x|` simultaneously with the one-dimensional ℓ₁, ℓ∞ and Euclidean
norms, a gauge, and `max{x,-x}`. Its `.absRun` (`1693`) has
`x_k=(-1/2)^k`, `H_k=(3/2)2⁻ᵏ`, `α_k=1`, constants `(1/4,1/2)`.
`.asymRun` (`1756-1797`) witnesses the asymmetric gauge `max{x,-2x}` with
`x_k=(-1/4)^k`, `H_k=(5/3)4⁻ᵏ`, the same constants. These demonstrate
nonemptiness, not the distinctive higher-dimensional nonsmooth geometry.

**Stronger existing witnesses prevent a scalar-only conclusion:**
- `BfgsCoverage.Article.Verification.fourMaxRun`,
  `bfgs_lean_article/BfgsArticle/Coverage/Article/Verification.lean:682-720`,
  on `max{v,-v,3u+v/2,-3u+v/2}`. `.fourMax_zero_sublevel` (`657-671`) proves
  coercivity's bounded-zero-sublevel hypothesis; `.branch_change_without_failure`
  (`729`) combines convergence and existence. The objective is genuinely 2D,
  although the displayed run stays on `u=0`, with `H₀=diag(1,3/2)` and
  `(c₁,c₂)=(1/4,1/2)`.
- `BfgsCoverage.Companion.Ch07H.bw_run_exists`,
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch07H.lean:3029-3123`,
  constructs an infinite run on `|u|+|v|` whose first points are
  `(1,3),(1,-1),(-1/20,11/10),(1/400,199/200)`. These are not one invariant
  axis. Its proof starts with `H₀=[[1,-1],[-1,2]]`, constants `(1/4,1/2)`,
  and continues three exact steps using general existence. `.absSum_line`
  (`2900-2918`) and `.absSum_no_stationary` (`2921-2930`) verify the
  existence hypotheses, rather than assuming them for finite maxima.
- `BfgsCoverage.Companion.Ch04R.nuclear_run_exists`,
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch04R.lean:5196-5208`,
  gives a run on the nuclear norm of symmetric 2×2 matrices (three real
  coordinates). Its proof uses start `(1,0,1)`, `H₀=I`, constants `(1/4,1/2)`.
  `.nuclear_line_countable` (`5155-5173`) and `.nuclear_gradient_ne_zero`
  (`5177-5188`) are general lemmas that, together with the general existence
  theorem, also permit arbitrary SPD/valid-constant specializations. The
  named `.nuclear_run_exists` statement itself is only `Nonempty`.

**PDF:** article explicitly presents ℓ₁ and ℓ∞ in dimension≥2, gauges, and
linear maxima at `global.tex:231-261`; it does not print these higher-dimensional
run constructions. The companion prints the centered spectral applications.

## 3. Local results and the basin quantifiers

### Finite polyhedral cells / PLQ — Theorem 7/Corollary 4, article pp. 17–18

**Exact main names:**
- `BfgsCoverage.Article.PositivePartition.polyhedral`,
  `bfgs_lean_article/BfgsArticle/Coverage/Article/PositivePartition.lean:59-78`.
- `BfgsCoverage.Article.Local.plq` and `.plq_loss_regularizer`,
  `bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean:482-528`.

The basin is genuinely chosen before the run: `∃ ε>0, ∀ R, F(R.x 0)≤F*+ε → ...`.
Because constants and initial matrix are fields of `R`, this is uniform in
them. A run somewhere on the objective alone would not establish an application
inside this existential basin.

The article's anonymous objective witness is `|x|` on two full-dimensional
half-lines (`PositivePartition.lean:84-149`; `Local.lean:3053-3126`).
`BfgsCoverage.Article.Local.plq_different_hessians` (`Local.lean:2788-2858`)
uses scalar `x²+max{x,0}²`, with Hessians 2 and 4; it too is objective-only.

**The low-basin issue is already closed in the companion:**
- `BfgsCoverage.Companion.Ch04R.exists_low_run`,
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch04R.lean:4568-4572`,
  takes tails of a convergent-value run. `.absRun_values` (`4575-4584`)
  gives the explicit value limit. The anonymous example `4761-4853` proves
  all half-line geometry together with a run below `F*+ε` for **every** `ε>0`.
  Tails retain the fixed constants but change the initial matrix; this is not
  arbitrary-prescribed-`H₀` existence. The tail operation itself is
  `BfgsVerification.AdmissibleBFGSRun.shift`,
  `bfgs_lean_stage1/BfgsVerification/RunShift.lean:14-32`.
- **Genuinely 2D PLQ witness:**
  `BfgsCoverage.Companion.Ch04R.plq2d_covered` (`Ch04R.lean:3090-3099`, proof
  following) verifies `F(u,v)=u²+v²+(2+|u|)|v|`, unique minimizer zero, four
  full-dimensional quadrant cells and different quadratic Hessians.
  `.plq2d_low_runs` (`5433-5483`) gives an actual run below `F(0)+ε` for every
  `ε>0`, using `x₀=(δ,δ)`, `δ=min{1,ε/5}`, `H₀=I`, `(c₁,c₂)=(1/4,1/2)`.
  The proof verifies countable bad-line sets and no smooth stationary point.
  Thus the article's polyhedral/PLQ hypotheses and actual low-starting runs
  coexist in dimension two. `.plq_broader_2d` (`3271-3281`) additionally
  proves that no global common locally-C¹,¹ summand plus finite max-affine
  penalty represents this objective. Its statement is global nonrepresentation;
  do not silently strengthen it to every local neighborhood.
- `.plq_example_run` (`5218-5300`) handles the scalar PLQ
  `x²+max{x,0}²+|x-1|`, with minimizer `1/4`, initial `x₀=1/2`, `H₀=1/4`,
  `α=1/2`, constants `(1/4,1/2)`; `5305-5308` obtains all low basins by tails.

**PDF:** article gives the PLQ class, absolute-value/hinge penalties and the
warning that arbitrary quadratic maxima need not be polyhedrally partitioned
(`local.tex:79-100`). The stronger 2D varying-Hessian example is actually
printed at `companion/chapters/04_R.tex:309`, PDF p. 30 (printed p. 24),
although its low-starting-run construction is not printed there.

### Local centered basin, lasso and residuals — Corollary 5, article p. 18

**Exact main name:** `BfgsCoverage.Article.Local.local_centered`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean:827-836`.
**Actual basin witness:** `BfgsCoverage.Companion.Ch06F.basinRun` and
`.basinRun_start`,
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch06F.lean:3079-3090`,
give the mixed benchmark with initial value exactly `F(0)+δ` for any `δ>0`.
The example `3113-3118` instantiates the actual basin supplied by the local
theorem. Constants are `(1/4,1/2)`, `ρ=1/4`, `H₀=diag(1,5δ/2)`.

**Important limits of individual illustrative examples:**
`Local.lean:3130-3152` witnesses the lasso assumptions only with
`m=n=1`, `A=1`, `b=0`, `λ=1`, minimizer zero; every optimal coordinate is zero.
`Local.lean:3156-3171` witnesses Euclidean residual assumptions by the scalar
norm with zero loss. Neither anonymous declaration contains a run. The
symbolic lasso theorem is general (`BfgsCoverage.Article.Local.lasso_local_basin`,
`Local.lean:1041`) and the residual theorem is general
(`.euclidean_residuals_basin`, `1194`); these scalar end examples do not test
a nontrivial mixture of zero/nonzero optimal residuals or a high-dimensional
lasso instance. This is an application-illustration limitation, not a missing
non-vacuity witness for the main local-centered theorem.

The companion has 2D benchmark-based low-starting examples for affine residual,
hinge and Euclidean residual forms (`Ch04R.lean:4876-4925`) and fused ℓ₁
(`4927-4969`). Its joint PLQ-plus-loss example is `5315-5362`.
The PDF itself prints the general lasso decomposition with `I₀` and signs
(`paper/sections/local.tex:116-136`) and Euclidean residual reduction (`138-144`).

## 4. Planar geometry and the explicit nonradial example

### Affine-critical cluster / convergence — Theorem 8/Corollary 6

**Exact main names:** `BfgsCoverage.Article.Local.planar_cluster`
(`Local.lean:1558-1576`) and `.planar_convergence` (`1761-1799`), in
`bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean`.
The regular two-branch hypothesis is imposed only **outside** the affine-critical
set; convergence additionally requires affine-critical points in the sublevel
to be minimizers. These are genuine assumptions, not properties built into runs.

**Joint objective + run:** anonymous example `Local.lean:3315-3384` uses
`u²+|v|`, `F*=0`, `b=1`, the run with `A=1`, `v₀=ρ=1/2`, `(c₁,c₂)=(1/4,1/2)`.
The named proofs `.unexcited_affineCritical_eq_zero` (`3236-3269`) and
`.unexcited_strict_contours` (`3272-3304`) verify the difficult objective
conditions. Branches are `u²±v`. At a switching point `(u,0)` off the
affine-critical origin, the gradients `(2u,1),(2u,-1)` are linearly independent.
This is a two-active-branch example with strict contours despite no common
positive lower Hessian bound for the branches. It is not merely a smooth
one-branch specialization, although its exhibited run stays on the vertical axis.

The three-quadratic objective also has all these hypotheses on `{F≤1/100}`:
the anonymous example `Local.lean:3176-3196` and the named facts in
`bfgs_lean_stage1/BfgsVerification/PlanarQuadraticConvergence.lean:22-59`.
Its actual runs are described next. Article PDF pp. 20–21 present the
theorem/corollary, pp. 22–23 the three-quadratic application.

### Nondegenerate planar maxima — Corollary 7, article pp. 21–22

**Exact main name:** `BfgsCoverage.Article.Local.planar_max`,
`Local.lean:1845-1865`; the lower-Hessian sufficient contour condition is
`.planar_max_hessian_contours` (`1876-1911`). `∃ ε` precedes `∀ R` and hence
is independent of `H₀,c₁,c₂`.

**Three-active-branch objective witness:** anonymous example
`Local.lean:3389-3435` proves all hypotheses for the explicit three quadratics,
including the active set at zero, affine independence, weights `1/3` and
branch Hessian lower bound `I`. Crucially, the stronger companion example at
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch09C.lean:4722-4751`
gives **for every `ε>0`, every SPD `H₀`, and every valid pair** a run with
`F(x₀)<F(0)+ε` and `F(x₀)<1/100`. Thus the unspecified basin of the main
max theorem has actual runs; the witness is not just one start potentially
outside that basin.

**Two versus three active branches:** at a planar minimizer the affine
independence/positive-balance hypothesis permits one, two or three active
gradients. For the existing `u²±v` example, the two gradients at zero are
`(0,±1)`, affinely independent with positive weights `1/2`; the geometry and
arbitrarily low runs are already proved above. This is an assembly of the
existing facts, not a separate named two-active `planar_max` non-vacuity theorem.
The fully packaged explicit max witness has three active branches at zero.
At a **non-affine-critical** point, three affinely independent active planar
gradients cannot occur (their affine hull is all of the plane), explaining
why the theorem requires at most two there. No inconsistency between its
two-branch local charts and the three-branch minimizer example was found.

### Curved nonradial switching — Theorem 9, article pp. 22–23

**Exact main names:** `BfgsCoverage.Article.Local.nonradial_example`,
`Local.lean:2405-2431`, and
`BfgsVerification.PlanarQuadraticExample.fullBFGS_explicit_basin`,
`bfgs_lean_stage1/BfgsVerification/PlanarQuadraticConvergence.lean:63-72`.

**Strong existing uniform existence:**
`BfgsVerification.PlanarQuadraticExample.objective_exists_admissible_run`,
`bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean:431-438`, says:

```
∀ differentiable x₀, ∀ H₀ ≻ 0, ∀ 0<c₁<c₂<1,
  ∃ R : AdmissibleBFGSRun 2 objective,
    R.x 0=x₀ ∧ R.H 0=H₀ ∧ R.c₁=c₁ ∧ R.c₂=c₂.
```

`.start_point_facts` (`443-453`) uses `x₀=(1/1000,0)`, where only `f₀` is
active and `F(x₀)=1001/10⁶<1/100`.
`.exists_admissible_run` (`479-489`) states basin existence in the article's
branch-variable notation; `.nonradial_example_nonvacuous` (`496-505`)
combines it with value and iterate convergence, for arbitrary `H₀,c₁,c₂`.
The companion's arbitrarily-low-start version was cited immediately above.

This is an objective with a nonsmooth optimizer, different positive-definite
branch Hessians, three active branches at the optimizer, and genuinely curved
switches. It proves substantially more than scalar consistency of the conditions.

**Eligible obstruction pairs versus an infinite orbit:**
`BfgsVerification.PlanarQuadraticExample.eligible_radial_unbounded_on_neighborhood`,
`bfgs_lean_stage1/BfgsVerification/PlanarQuadraticSeparation.lean:52-85`,
chooses a positive band before every `δ>0,C` and produces actual endpoint
gradients, an eligible pair for `(1/4,1/2)`, and an SPD matrix realizing that
pair as a unit BFGS step. It does not assert one common infinite run containing
all these pairs, or one fixed matrix across the family. The main radial-bound
failure is objective-level, so that stronger orbit assertion is unnecessary.

**Presentation gap:** the PDF prints the objective, `1/100` basin, coefficient
bounds and radial obstruction (`paper/sections/local.tex:369-434`), but not
the existence theorem, the finite tie-line argument, or `(1/1000,0)` start.
The existence supplement is therefore valuable evidence that the current
reader does not see directly. The old comment in `Global.lean:120-123`
correctly says existence is not established *in that module*; it is not an
unresolved project-wide gap.

## 5. The general run-existence theorem has essential extra hypotheses

**Exact name:** `BfgsVerification.AdmissibleRunExistence.exists_admissible_run`,
`bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean:199-244`.
Its assumptions are convexity, boundedness below, and

```
∀ x p, DifferentiableAt ℝ F x → p ≠ 0 →
  {t : ℝ | ¬ DifferentiableAt ℝ F (x+t•p)}.Countable,
∀ y g, HasFDerivAt F (gradientFunctional g) y → g ≠ 0.
```

The second condition ensures recursion never terminates successfully at a
smooth minimizer. It is sufficient, not necessary: the explicit smooth
quadratic run exists even though the objective has a smooth stationary point.
The first condition is about **full-space differentiability**, not just the
one-dimensional line restriction. Convexity gives much less than this on
arbitrary lines. A finite maximum can have a whole line segment of full-space
nondifferentiability after a differentiable start.

The nonradial example verifies a stronger finite-line condition, rather than
silently assuming it: `.tie_line_finite` (`335-379`),
`.nondifferentiable_line_finite` (`383-391`), and
`.objective_run_hypotheses` (`422-427`) in the same file. Its pairwise tie
curves are two nondegenerate hyperbolas and a circle; none contains a line.

**Rigorous counterexample to an overgeneral existence reading:**
`BfgsVerification.FivePieceObstruction.no_differentiable_armijo_wolfe`,
`bfgs_lean_stage1/BfgsVerification/FivePieceObstruction.lean:176-189`, and
`BfgsCoverage.Companion.Ch06F.five_piece_obstruction`,
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch06F.lean:2627-2667`, use

```
h(x,y,z)=max{-x,y+z,-y+z,x/4,-z},
x₀=(-2,0,1), H₀=I, (c₁,c₂)=(1/4,1/2).
```

This is finite, convex, coercive, degree-one homogeneous and uniquely minimized
at zero. The initial gradient is `(-1,0,0)` and the ray is `(α-2,0,1)`.
For `0<α<1`, weak Wolfe fails; for `1≤α≤6`, the full objective is not
differentiable (although the restriction is constant in the interior);
for `α>6`, Armijo fails. Thus **no infinite admissible run can have this
initial state and pair**, even though the objective satisfies the global
homogeneous/centered geometry. `.obstruction_in_every_neighborhood`
(`FivePieceObstruction.lean:193-216`) scales the point and matrix near zero.

This is a scope limitation, not a counterexample to the stated convergence
theorems. Article p. 6, `energy.tex:32-34`, explicitly disclaims all-ray
existence; companion `06_F.tex:189-203`, PDF pp. 43–44, explains the distinction
and prints the finite obstruction. A response to “arbitrary H₀” should retain
the qualification “for every infinite admissible run.”

## 6. Negative constructions: actual existence is in the main statements

### Globally C²,¹ branches, local failure — Theorem 10, article pp. 24–25

`BfgsCoverage.Article.NegativeUpper.local_failure`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/NegativeUpper.lean:207-297`,
existentially gives four branches, all objective regularity/minimum facts,
and sequences of starts/iterates/matrices/query lists chosen **before**
the line-search constants. For every `0<c₁≤1/3`, `c₁<c₂<1` and copy index≥1,
there is a matching `AdmissibleBFGSRun`, and the specified non-strict search
returns its lengths/trace for every trial budget≥5.

The proof uses `BfgsVerification.DEmbedding.run`
(`bfgs_lean_stage1/BfgsVerification/DEmbeddingRun.lean:10`) and proves
`H₀=I`, nonoptimal nonstationary limits, strict value decrease, differentiability
of all accepted/rejected queries, and shrinking query norms. **No extra run
existence premise.** This is identity initialization and exceptional starts,
not failure for every SPD matrix or every nearby start. All constants in the
stated range are supported by the same objective, starts and decision tree.

### Homogeneous seed / coercive polyhedral cap — Corollary 8, article p. 28

`BfgsCoverage.Article.Failure.cone_orbit`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/Failure.lean:1230-1254`,
produces the seed run with `H₀=I`, actual search outputs and exact three-step
scaling. `.cone_limit_nonstationary` (`1270-1276`) supplies its wrong limit.
`.failure_polyhedral` (`1295-1310`, proof following) proves the coercive
four-piece objective's unique minimizer `(-1,16)` and gives the **same actual
deterministic run**, for every pair in the stated range, converging instead
to zero. This is stronger than a formal algebraic cycle or prescribed
accepted-length sequence. The seed is unbounded below; its cap has an affine
intercept. Neither contradicts coercive homogeneous convergence.

### Positive lower curvature, local failure — Theorem 11, article p. 32

`BfgsCoverage.Article.NegativeLower.local_failure_lower`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/NegativeLower.lean:168-216`
(proof following), existentially constructs one strongly convex objective,
four globally C¹,¹ uniformly strongly convex branches, fixed bad starts→0,
and actual runs with `H₀=I`, uniformly for every pair in the stated range.
It also explicitly proves that the first three branches are not twice
differentiable at zero. The source theorem is
`BfgsVerification.LUniform.uniformSmoothLocalFailure`,
`bfgs_lean_article/BfgsArticle/LUniformLocal.lean:572`.
No missing main non-vacuity premise; no finite strongly convex C² local
counterexample is being supplied by this result.

### Strongly convex quadratic perturbation — Proposition 1, article p. 44

`BfgsCoverage.Article.LowerCurvature.quadratic_failure_initial_point`,
`bfgs_lean_article/BfgsArticle/Coverage/Article/LowerCurvature.lean:402-419`
(proof following), and `BfgsVerification.LUniform.uniform_global_failure`,
`bfgs_lean_article/BfgsArticle/LUniformGlobal.lean:227-262`, prove that for
every `μ>0` and every neighborhood of the wrong corner, **some** initial SPD
state produces the actual bad run. That state is chosen before the valid pair
in `0<c₁≤1/3`, and every actual query stays in the neighborhood. The initial
matrix here is existentially selected; it is not an arbitrary-matrix theorem.
The local embedding later whitens one common matrix to identity. The PDF
correctly distinguishes existence on a stable manifold from a rounded
numerical initial state (`failure.tex:498-506`, appendix D).

## 7. Chapter 7 common-tilt issue — existing open item, not a new article gap

`TODO_LEAN_REVIEW.md:494-512` already records this issue. Exact formal evidence:

- `BfgsCoverage.Companion.Ch07H.maxLinear_line_no_run`,
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch07H.lean:1436-1439`
  (proof following): `IsEmpty (AdmissibleBFGSRun n F)` for slopes on an
  affine line missing zero, in arbitrary ambient dimension.
- `.maxLinear_affine_free_no_run` (`1600-1664`): with ambient dimension≤2,
  `0∉aff{a_i}` implies there is no infinite admissible run.
- `.tilt_collinear_no_run` (`1496`), `.tilt_two_values_no_run` (`1544`), and
  `.tilt_plane_no_run` (`1559`) specialize this to `t+max_i b_iᵀu`.
- `.TiltNoInfiniteRunQuestion` (`1675-1679`) is an unproved `Prop`, correctly
  left open for noncollinear slope families (at least three pieces and
  ambient dimension≥3).

The PDF calls it a “useful arbitrary-many-piece family”
(`companion/chapters/07_H.tex:91-100`, PDF p. 46, printed p. 40) and later
conditions the result on infinite continuation (`448-464`, PDF p. 49,
printed p. 43). The formal no-run results for the low-dimensional/collinear
subfamilies are not spelled out there. The general bounded-below existence
theorem cannot resolve this: these common-tilt objectives are unbounded below.
No attempt to settle the open case was made.

## 8. Findings/TODO candidates for the coordinating reviewer

These are evidence/presentation findings, except for the already-recorded
Chapter 7 open item. No correction to a main convergence theorem was found.

- [ ] **NV-F1 — Surface the strong nonradial existence evidence.** Add a short
  existence remark after the printed example: at `(1/1000,0)` the first branch
  is uniquely active, the objective value is `1001/10⁶<1/100`, and an infinite
  admissible run exists for every SPD initialization and valid pair. State the
  verified finite-line/nonsmooth-minimizer reason, or point explicitly to the
  existence supplement. Existing proof: `AdmissibleRunExistence.lean:422-505`.
- [ ] **NV-F2 — Illustrate genuinely higher-rank certificate generality.** A
  concrete dimension≥2 rank>1 certificate is absent from the examples located
  in this audit. The scalar identity certificate does not exercise it. This
  concerns the explanatory reach of the general PSD theorem; its existential
  non-vacuity is already established by rank-one applications. A smooth
  quadratic with `W=I` is a natural additional illustration, but no new Lean
  construction was added in this audit.
- [ ] **NV-F3 — Make the existence/convergence quantifier distinction visible
  near broad “arbitrary initialization” summaries.** Keep the present theorem
  scope. Use the existing five-piece obstruction to explain why a theorem
  covering every admissible run cannot assert that every differentiable start
  and SPD matrix extends to such a run. Do not claim the general existence
  theorem applies automatically to all finite maxima.
- [ ] **NV-F4 — Consider stronger application examples in the article.** The
  printed general lasso decomposition is sound, but the corresponding
  end-of-module witness is scalar with all optimal coordinates zero. The
  companion's 2D varying-Hessian PLQ example and actual low-basin runs provide
  stronger existing evidence to cite; a mixed zero/nonzero-coordinate lasso
  example would clarify the local nature of the reduction.
- [ ] **Existing H item — disclose possible vacuity of the common-tilt
  corollary if retaining its “useful family” presentation.** This is the
  existing `TODO_LEAN_REVIEW.md` item, not a newly discovered main-result gap.

**Do not record as gaps:** the persistent-positive-gap contradiction assumptions
in the certificate proof (`Energy.lean:1374-1379`); the no-affine-critical-cluster
contradiction assumptions (`Local.lean:2980-2984`); failure to prove that all
eligible pairs form a common BFGS orbit; absence of a uniform neighborhood for
arbitrary initial points in a theorem that explicitly gives only a local
sublevel basin; or special initialization of an existential counterexample.

## Evidence artifacts

- This report: `REVIEW.md`.
- `Checks.lean`, `Checks.log`: successful cached-import signature/axiom check.
- `BFGS_Journal_Article.pdf.txt`, `BFGS_Complete_Companion.pdf.txt`: released-PDF
  text with physical page markers, extracted for this review.

Bottom line for the author: the complicated conditions do have rigorous,
nontrivial, dynamically inhabited examples. The main improvement is to make
those examples and their exact quantifiers easier to find, while preserving
the distinction between conditional infinite-run convergence and line-search
existence from a prescribed initial state.
