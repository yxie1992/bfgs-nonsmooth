# Main results: satisfiability, examples, and scope

16 October 2026. Review requested by Yuchen Xie after the 15 October release:
“For the main results, the conditions are stated quite complicated. Have we made
sure that they are actually possible to satisfy and present examples? It would
be good to review how general they are.”

Reviewed sources: `a6f46d1`, the completed 15 October edition. This report reviews
the principal article results and uses the companion to identify extensions and
limitations. The mathematical review is by GPT-6 Astra in OpenCode; an independent
agent checked the existing formal witnesses, and another independently checked
the new analytic examples. This is not the author's expert check. The detailed
records are [FORMAL_EVIDENCE.md](FORMAL_EVIDENCE.md) and
[MATHEMATICAL_REVIEW.md](MATHEMATICAL_REVIEW.md).

**Subsequent implementation (16 October 2026):** M42 is complete. The article
now includes the hypothesis-check guide and Appendix E, with joint Lean
witnesses and independently reviewed literal coverage; the companion states
the Chapter 7 caveat. Fresh package evidence passes for 5506 audited names and
786 replayed modules. See [verification/EVIDENCE.md](verification/EVIDENCE.md).
The review below preserves the findings that motivated those additions.

## 1. Answer in brief

**The main convergence mechanisms have concrete jointly satisfying examples,
including genuine infinite full-BFGS runs. The examples and existence evidence
are not collected clearly enough in the article.** The useful distinction is
between broad, readily recognizable objective classes and a more general
certificate whose construction is itself a substantial proof obligation.

Three questions must be kept separate:

1. **Objective hypotheses:** does an actual function satisfy all of them at once?
2. **Run existence:** is there an infinite admissible BFGS run on that function,
   rather than just a sequence of eligible endpoint pairs?
3. **Initialization/implementation guarantee:** for which starting points,
   matrices and constants is existence known, and does a specified search find
   the steps?

The main positive theorems quantify over infinite admissible runs. Their freedom
in the initial SPD matrix and line-search constants is conditional on such a run.
This is stated in `paper/sections/energy.tex:13-34` and
`paper/sections/introduction.tex:56-61`. The distinction is material, not just a
logical technicality: Section 6 below gives a covered coercive max-linear
objective with a differentiable start for which the first ray contains no
differentiable weak-Wolfe point.

Conversely, run existence is considerably stronger than a bare conditional
statement for the article's explicit curved-switching example: the existing
Lean theorem supplies infinite admissible runs for **every** initial SPD matrix
and **every** valid pair of line-search constants.

### Main-result map

Labels below are the stable LaTeX labels; the file paths refer to the article.

| Result | What has to be checked | Illustrative witness / class (sources below) | Actual scope |
|---|---|---|---|
| `art:minor-hierarchy`, `art:reciprocal-growth` (`sections/energy.tex`) | Positive curvature of an actual update; bounded gradients and vanishing predicted decrease for the latter | Ordinary admissible runs, including the scalar quadratic and the mixed ridge | Algebra in any finite dimension. On a compact sublevel, the latter two assumptions follow from finite convexity and Armijo; no matrix limit or conditioning bound is added. |
| `art:certificate` (`sections/energy.tex:251-280`) | Construct a PSD field satisfying visibility, secant control, and projected transport on each positive band | Radial field for the mixed ridge; an explicit nonradial parabolic field in companion Chapter 10 | A broad sufficient mechanism, not a simple test for every convex function and not necessary for convergence. |
| `art:centered`, `art:mixed-benchmark` (`sections/global.tex:135-198`) | Smooth-plus-degree-one structure centered at an actual minimizer; compact initial sublevel inside its region | `u²+|v|`; a convex locally C¹,¹ term plus a centered sublinear term | Arbitrary dimension, arbitrary smooth/sublinear coupling. Global if the representation is global and sublevels are compact. Centering is a real restriction. |
| `art:homogeneous`, `art:homogeneous-examples` (`sections/global.tex:207-265`) | Finite convex degree-one homogeneity and coercivity | Every norm; finite gauges with bounded unit sublevel; positively spanning finite linear maxima | Global, arbitrary dimension, without finite-piece or symmetry assumptions. Does not cover general affine maxima. |
| `art:polyhedral`, `art:plq`, `art:local-centered` (`statements/positive_partition.tex`, `sections/local.tex:79-144`) | Finite local polyhedral cells with C¹,¹ extensions, or local centered structure; unique minimizer | Squared loss plus ℓ₁ regularization; smooth losses plus finite polyhedral/PLQ penalties; sums of Euclidean residual norms via the centered route | Arbitrary-dimensional **local** basin independent of the initial SPD matrix and valid constants. A finite smooth maximum need not have a finite polyhedral partition. |
| `art:planar-cluster`, `art:planar-convergence` (`sections/local.tex:214-292`) | Strict positive contours; regular two-branch switching off the affine-critical set; for optimality, all affine-critical points in the sublevel are optimal | The mixed ridge and the explicit three-quadratic example | Two-dimensional. The cluster theorem alone asserts an affine-critical cluster point, not an optimal one. |
| `art:planar-max` (`sections/local.tex:303-360`) | Active gradients affinely independent, with a strictly positive balancing vector at the minimizer; strict low contours | Three quadratics in `art:nonradial-example`; two branches `u²+v²±v` are an elementary special case | A checkable local sufficient criterion. A common positive branch-Hessian lower bound supplies the contour condition. No genericity or necessity theorem is proved. |
| `art:nonradial-example` (`sections/local.tex:369-434`) | All of the preceding geometric conditions, verified explicitly | The printed maximum of three distinct quadratics, with basin `F<1/100` | A genuine nonsmooth curved-switching example where radial control fails arbitrarily near the optimizer. Existing Lean evidence also establishes run existence. |
| `art:local-failure`, `art:local-failure-lower`, `art:failure_polyhedral`, `art:quadratic_failure` | All the advertised regularity, initialization, and search properties of the constructed examples | Explicit seed, cap, strongly convex quadratic perturbation, and local embeddings; exact accepted and rejected queries | Existential deterministic failures, realized by the specified search. Global failure already occurs for strongly convex quadratic maxima; the two local constructions have different regularity. No generic or positive-measure failure is claimed. |

The article already has a useful scope table in `sections/geometry.tex:59-109`.
What it lacks is the adjoining **joint-hypothesis and run-existence check**.
For the general certificate and centered results, the conclusion is convergence
of objective values and distance to the minimizer set; convergence of the whole
iterate sequence follows when the minimizer is unique. The homogeneous, local
unique-minimizer and explicit planar examples have that stronger conclusion.

## 2. Many of the long hypotheses are consequences, not extra restrictions

For an admissible run, weak Wolfe and the BFGS update give

\[
H_k\succ0,\quad q_k=g_k^TH_kg_k>0,\quad
d_k=\alpha_kq_k>0,\quad
\beta_k=t_k/d_k\ge1-c_2>0.
\]

Thus the principal-minor theorem does not ask the user to independently verify a
sequence of positive-curvature inequalities. They follow from the run convention.

If the accepted iterates stay in a compact sublevel of a finite convex function,
subgradients are bounded there. Armijo and a lower bound on the objective give
`sum d_k < infinity`, hence `d_k -> 0`. These discharge the two assumptions of
the reciprocal-growth theorem. The proofs are in
`sections/energy.tex:44-73,170-219,281-287`.

For a finite convex objective on all of a finite-dimensional space, a **unique
attained minimizer already implies compact sublevels** and that sufficiently low
sublevels lie in any prescribed neighborhood of the minimizer. The article proves
this in `art:localization`. Consequently the local results do not need a separate
matrix-dependent trapping assumption.

The substantive work is then the objective geometry: centered homogeneity,
finite local cells, or controlled planar switching. These should be prominent
in a reader-facing statement, with the consequences listed once.

The planar proof uses the same three field estimates on a neighborhood of a
hypothetical positive-level cluster set, and applies the energy argument to the
run's tail (`sections/local.tex:230-273`). This is not a claim that a single field
on every entire initial band has already been exhibited for that objective.
Assumptions introduced for a contradiction, such as a persistent positive gap,
are not additional hypotheses for which a successful-run witness is required.

## 3. An explicit certificate and an actual nonsmooth run

The comparison field `W_eta` is an analysis device, not a matrix the algorithm
must compute. It may be rank deficient and may depend on the positive band;
the definition does not demand continuity, a uniform upper bound, or constants
uniform as `eta` tends to zero. Its inequalities do, however, quantify over all
eligible sufficiently small-`d` pairs in the band, not just the pairs selected
by one particular run.

For the printed benchmark

\[
F(u,v)=u^2+|v|,\qquad K=\{F\le b\},\quad b>0,
\]

one can give **every constant** in the band-certificate definition:

\[
W_\eta(x)=xx^T,\qquad m_\eta=\eta^2,\qquad
C_\eta=2b,\quad L_\eta=0,\quad\delta_\eta=1.
\]

Only differentiable points, hence `v != 0`, are used.

* **Visibility:** `g^T x = 2u²+|v| >= F(x) >= eta`, so
  `g^T W(x) g >= eta²`.
* **Transport:** `z=x+s` implies `Pi_s z=Pi_s x`, hence the projected matrices
  are equal. No transport error is needed.
* **Secant control:** write `x=(u,v)`, `z=(a,w)`. If `v,w` have the same sign,
  `t=2(a-u)²`, `y^T z=2(a-u)a`, and `(y^T z)² <= 2a² t <= 2b t`.
  If the signs differ, set `S=|v|+|w|>0`. Then

  \[
  t=2(a-u)^2+2S,\qquad y^Tz=2(a-u)a+2|w|.
  \]

  Cauchy--Schwarz bounds its square by
  `t [2a² + 2|w|²/S] <= 2 F(z) t <= 2b t`.

This holds for all such endpoint pairs, so in particular for all eligible pairs
in the band. A field of rank one really does suffice in dimension two.

There is also a particularly short **actual full-BFGS history**, with
`c1=1/4`, `c2=1/2`:

\[
x_k=\left(0,\frac23(-\tfrac12)^k\right),\quad
g_k=(0,(-1)^k),\quad
H_k=\operatorname{diag}(1,2^{-k}),\quad\alpha_k=1.
\]

The step is `-H_k g_k`, the inverse-BFGS update changes the second diagonal entry
from `2^{-k}` to `2^{-k-1}`, and

\[
d_k=2^{-k},\quad \Delta_k=\tfrac13 2^{-k},\quad t_k=2\,2^{-k}.
\]

Both line-search inequalities hold, all accepted points are differentiable with
nonzero gradients, and `H_0=I`. The matrices become singular in the limit; that
does not invalidate the theorem. This history crosses the kink on every step.
It is a specialization of the existing formal construction
`BfgsVerification.UnexcitedMetric.run` (`A=1`, `v0=2/3`, `rho=1/2`).

The certificate estimate `C=2b` above is a worked calculation in this review;
it is not being attributed to a new registered Lean declaration. The printed
article instead derives a certificate through its inward-model theorem.

For the matrix/reciprocal results an even simpler witness is the scalar quadratic
`F(x)=x²/2`, `x_k=2^{-k}`, `H_k=1`, `alpha_k=1/2`, with the same constants.
Here `q_k=4^{-k}` and `d_k=4^{-k}/2`. The assumptions occur along an actual run,
not an arbitrary SPD matrix sequence unrelated to BFGS.

**Higher-rank calibration.** The same calculation extends to
`F(x)=||x||_2²/2` in any dimension `n>=2`. On `K={F<=b}` take
`W_eta=I`, `m_eta=2 eta`, `C_eta=1`, `L_eta=0`, `delta_eta=1`.
Here `g=x`, `y=s`, `t=||s||²`: visibility is `||x||²>=2 eta`, secant control
is equality, and projected transport is equality since the field is constant.
For a nonzero start in `K`, `x_k=2^{-k}x0`, `H_k=I`, `alpha_k=1/2` is an
actual run with `(c1,c2)=(1/4,1/2)`. The update keeps `I`, since its projected
part is `Pi_s` and its rank-one part is the complementary projector.
Unlike the scalar identity example, this exercises a field of rank greater
than one and a nonzero orthogonal projection. It illustrates satisfiability of
the higher-rank option, not a need for higher rank in the nonsmooth applications.
This follow-up is now also compiled in scratch Lean, in arbitrary finite
dimension: `HigherRankCalibration.joint_witness` proves the run, compact
sublevel, all certificate hypotheses, rank exactly `n`, and convergence
together. The proof and its six standard-axiom checks are archived as
`HigherRank.lean.txt` and `HigherRank.log`; details are in
[HIGHER_RANK.md](HIGHER_RANK.md). This is additional review evidence, distinct
from the registered examples in the released package.

## 4. How broad are the easy-to-recognize objective classes?

### 4.1 Centered objectives: a whole parameterized family

For a prescribed decomposition `F(x)=psi(x)+gamma(x-x*)`, checking that `x*`
really minimizes the sum is equivalent to

\[
-\nabla\psi(x_*)\in\partial\gamma(0).
\]

This is the convex subgradient optimality condition. It makes the centering
hypothesis checkable; the two summands need not be separately minimized there.

For example, take any nonempty compact convex set `C` in `R^n`, its support
function `sigma_C`, any `a in C`, and `Q` positive definite. Then

\[
F(x_*+r)=c+\tfrac12r^TQr-a^Tr+\sigma_C(r)
\]

is a globally centered objective of the theorem, with unique minimizer `x*`
and compact sublevels. Indeed `sigma_C(r)>=a^T r`, so
`F(x*+r)>=c+lambda_min(Q)||r||²/2`. This allows arbitrary dimension,
nonpolyhedral and asymmetric support sets, and many choices of the smooth term.
The positive definiteness here is a convenient sufficient condition for the
example, not an extra requirement of `art:centered`.

By contrast, an arbitrary translated penalty is not globally homogeneous about
the optimizer. For a Lasso-type objective the decomposition is generally **local**.
That distinction explains why the theorem does not give global convergence for
every smooth-loss-plus-polyhedral-penalty problem.

### 4.2 Homogeneous objectives: a finite-dimensional geometric test

For `F(x)=max_i a_i^T x`, coercivity is equivalent to

\[
0\in\operatorname{int}\operatorname{conv}\{a_i\},
\]

where the interior is in the full ambient space. Equivalently, some `mu>0`
satisfies `F(x)>=mu||x||` for every `x`. This is positive spanning, not merely
membership of zero in the convex hull. It is stable under sufficiently small
perturbations of the slopes when there is a positive margin.

Every norm and finite gauge with bounded unit sublevel qualifies. The objective
class is genuinely broad and arbitrary-dimensional. General affine offsets need
not preserve homogeneity, so this theorem gives no guarantee for arbitrary
finite affine maxima. The cap in the article's coercive polyhedral failure
example is genuinely nonhomogeneous. This is a property of the objective, not
the chosen list of formulas: a redundant offset piece, as in
`max{x,-x,-1}=|x|`, is harmless, and a common additive objective constant can be
removed without changing BFGS or its line-search inequalities.

Nor are all existing homogeneous run examples confined to an invariant axis:
`BfgsCoverage.Companion.Ch07H.bw_run_exists` constructs a run on `|u|+|v|`
starting with `(1,3), (1,-1), (-1/20,11/10), (1/400,199/200)` and the
non-diagonal SPD matrix `[[1,-1],[-1,2]]`, before continuing it by the existence
theorem.

### 4.3 Local cells and regularized optimization

The finite-polyhedral theorem applies to convex locally C¹,¹ losses plus finite
polyhedral penalties (absolute values, generalized/fused absolute values, hinge
terms), and to finite PLQ pieces. Strong convexity of a smooth loss, for example
full column rank in squared loss or a positive quadratic regularizer, is an easy
way to ensure the required unique minimizer. It is sufficient, not necessary.

The article already gives the general local ℓ₁ decomposition and the Euclidean
residual-norm extension in `sections/local.tex:116-144`. A fully numerical instance
that exposes the locality is

\[
F(x_1,x_2)=\tfrac12[(x_1-2)^2+x_2^2]+|x_1|+|x_2|,
\qquad x_*=(1,0),\quad F_*=3/2.
\]

On `U={x1>0}`, set `psi=1/2[(x1-2)²+x2²]+x1` and `gamma(r)=|r2|`.
The boundary `x1=0` has minimum value `2`; in fact the entire half-space `x1<=0`
has `F>=2`. Thus any initial value `<2` lies in a compact sublevel contained in
`U`, and the centered theorem proves convergence for every admissible run there.
This is a nonempty, explicitly verifiable basin with a nonsmooth optimizer.

There is stronger existing formal PLQ evidence than a scalar absolute-value
example. The companion prints

\[
P(u,v)=u^2+v^2+(2+|u|)|v|
\]

in Chapter 4. `BfgsCoverage.Companion.Ch04R.plq2d_covered` verifies its four
full-dimensional quadrant cells and varying Hessians;
`Ch04R.plq2d_low_runs` proves an actual admissible run with
`P(x0)<=P(0)+epsilon` for every `epsilon>0`. Its proof chooses
`x0=(delta,delta)`, `delta=min(1,epsilon/5)`, `H0=I` and `(c1,c2)=(1/4,1/2)`.
Thus a run can start inside the unspecified local basin, not just somewhere on
a function that has the right geometry.

The Euclidean residual argument should not be read as an arbitrary-norm
regularization theorem. For example, the companion distinguishes centered
nuclear-norm models from nonzero rank-deficient minimizers where the local
radial condition can fail (`Ch04R.spectral_RS_fails`, Chapter 4's spectral
example). Failure of that sufficient condition is not itself a proof of
failure of BFGS convergence.

What is **not** asserted: a uniform basin size for all such problems, global
convergence from arbitrary starts, active-set identification, confinement of
rejected trials, or automatic differentiable line-search acceptance. A finite
maximum of quadratics typically has curved switching sets, so “finitely many
quadratic formulas” is not the same hypothesis as “finite PLQ cells”.

### 4.4 Planar maxima: substantive, but not an empty or isolated condition

At the minimizer the condition is a simplex balance:

\[
\sum_{i\in I_*}\lambda_i\nabla f_i(x_*)=0,\quad
\sum_i\lambda_i=1,\quad\lambda_i>0,
\]

with affinely independent active gradients. There are at most three active
branches in the chosen planar representation, although arbitrarily many other
branches may be inactive nearby. A redundant representation can fail this test
even when a simpler representation of the same objective passes it.
Geometrically, with three active gradients zero lies strictly inside their
triangle; with two, it lies strictly between them; with one, that gradient is
zero. These are nondegeneracy/strict-complementarity-type conditions on the
objective, not assumptions about an unknown BFGS trajectory.

These conditions are easier to read in the following **sufficient special case**:
finite convex `F` on `R²`, locally a maximum of strongly convex C² branches, with
affine independence and strictly positive balancing weights at its minimizer.
Local branch strong convexity supplies strict contours and uniqueness, and the
localization lemma supplies a compact basin. The real extra test is the active
gradient geometry. The algorithm does not need to find these weights or the
comparison field.

The printed three-quadratic example is especially strong evidence:

* Hessians lie between `I` and `3I`;
* the average of the three branches is `u²+v²`, so the optimizer is uniquely zero;
* gradients at zero are `(1,0)`, `(0,1)`, `(-1,-1)`, balanced by `(1/3,1/3,1/3)`;
* the paper verifies affine correctness throughout the box `|u|,|v|<=1/10` and
  gives the explicit basin `F<1/100`;
* its curved switching violates radial secant control on every sufficiently
  small neighborhood. It is a genuine extension beyond the radial argument.

The formal run-existence result is in
`bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean`:
`BfgsVerification.PlanarQuadraticExample.nonradial_example_nonvacuous`.
It uses `x0=(1/1000,0)`, with `F(x0)=1001/10^6<1/100`, and works for arbitrary
`H0` positive definite and every `0<c1<c2<1`. Its proof checks, rather than
assumes, that every line meets the nondifferentiable set only finitely often.
The manuscript presents the objective and convergence proof, but not this
run-existence argument.

For the existential basin in `art:planar-max`, the companion coverage also
supplies runs starting below **every** `epsilon>0`, with arbitrary prescribed
SPD matrix and valid constants (`Coverage/Companion/Ch09C.lean:4714-4751`).
It uses `x0=(min(epsilon/4,1/1000),0)`. This discharges the possible concern
that one displayed start might lie outside the local theorem's unspecified
basin.

No claim of genericity among all convex nonsmooth functions follows from these
examples. In particular, higher-dimensional curved switching is not covered by
the planar construction. Stationarity implies affine criticality, not conversely;
requiring every affine-critical point in the relevant sublevel to be optimal is
a genuine extra condition.
The theorem does not assert that affine independence or positive multipliers
are necessary for convergence.

The companion does add higher-dimensional positive results, notably the single
exceptional-hyperplane theorem in Chapter 11 under strong convexity and
tangential regularity. These have additional fixed-normal geometry; they do not
constitute a theorem for arbitrary higher-dimensional curved switching.

## 5. A simpler curved-switching family to consider presenting

This is an additional analytic example worked out for this review, not a claim
that the current manuscript or its Lean register already contains this family.
For any `a,b,c>0`, let

\[
F_{a,b,c}(u,v)=\max\{a u^2+b v^2+v,\;c u^2+b v^2-v\}.
\]

This supplies a three-parameter family satisfying the hypotheses of the
article's **global** planar-convergence corollary, on every positive sublevel
`K_B={F<=B}`, `B>0`. Switching is curved when `a!=c`; `a=c` is the valid
straight-switching special case:

1. Both branches have Hessian bounded below by
   `2 min(a,b,c) I`, so their maximum is strongly convex. Also
   `F >= (a+c)u²/2+bv²` and `F(0)=0`; zero is the unique minimizer and
   all sublevels are compact with strict positive contours.
2. The only switching curve is `v=(c-a)u²/2`. On it the determinant of the two
   active gradients is

   \[
   -2u\,[a+c+b(c-a)^2u^2],
   \]

   which vanishes only at `u=0`, hence only at the minimizer. Away from the
   switching curve there is a smooth branch. At a smooth point affine
   criticality is stationarity; convexity and uniqueness exclude such a point
   from the affine-critical set. Thus `C_aff={0}`, and all hypotheses of
   `art:planar-convergence` hold on every positive compact sublevel.
3. The active gradients at zero are `(0,1)` and `(0,-1)`, affinely independent
   with weights `(1/2,1/2)`. This also directly instantiates `art:planar-max`.
4. These objectives have actual infinite admissible runs from every
   differentiable start, every SPD initialization and every valid pair of
   constants: apply the existing general existence theorem. They are bounded
   below, have no differentiable minimizer, and each line through a
   differentiability point meets the switching curve finitely often. For
   `a!=c` the curve is a parabola containing no line; for `a=c` a line through a
   differentiability point cannot be contained in the switching line.

For instance, `a=b=1`, `c=2` gives `max{u²+v²+v,2u²+v²-v}`. It also separates
moving from radial geometry. Fix `r>0` small, put `v0=r²/2`, and take
`x=(r,v0+e)`, `z=(r,v0-e/2)`, `e>0`. Direct calculation gives

\[
\begin{aligned}
d&=\tfrac32 e(1+r^2+2e),&
t&=3e+\tfrac92e^2,\\
\Delta&=(\tfrac12+\tfrac32r^2)e+\tfrac34e^2,&
y^Tz&=r^2+(1-\tfrac32r^2)e+\tfrac32e^2.
\end{aligned}
\]

For `0<r²<3` these pairs are eligible for `(c1,c2)=(1/4,1/2)`:
`Delta-d/4=e(1+9r²)/8>0`, `d-Delta=e+9e²/4>0`, and
`t-d/2=3e(3-r²)/4+3e²>0`. As `e -> 0`, `t -> 0` but `y^Tz -> r²`.
The common limiting objective value is `3r²/2+r⁴/4>0`, so the radial quotient
diverges on a fixed positive band. Choosing `r` arbitrarily small moves that
band arbitrarily close to the minimizer. The endpoint pairs vary with `e`;
they are not being called one infinite bad run.

This is a useful simpler companion to the three-branch example, not a replacement
for its independently checked formal proof. Promoting the new family into the
article should include a Lean specialization and a register entry.

## 6. What the examples do not establish

### 6.1 Covered objectives can have starts with no admissible next step

Consider the finite coercive convex degree-one function

\[
G(u,v)=\max\{u,-u+v,-u-v\}.
\]

It satisfies the objective hypotheses of `art:homogeneous`:
`G>=|u|`, `G>=|v|/2`, and its unique minimizer is zero. It is also a finite
polyhedral objective. At the differentiable point `x0=(1,0)` with `H0=I`, the
gradient is `(1,0)` and the search ray is `(1-alpha,0)`.

For `0<alpha<1` the gradient remains `(1,0)`, so weak Wolfe would require
`-alpha >= -c2 alpha`, which is impossible for `c2<1`. For `alpha>=1` the
objective is nondifferentiable (at zero or on the negative horizontal ray).
There is therefore **no differentiable acceptable point on this ray** for any
valid line-search pair. The same obstruction occurs at `(epsilon,0)` for every
`epsilon>0`.

This does not contradict the convergence theorem: there is no infinite
admissible run from those initial data. It shows why an existence witness for a
class must not be silently upgraded to a universal nonbreakdown guarantee.
Nor is this itself a stagnating infinite-run counterexample. The general
`AdmissibleRunExistence` theorem does not apply to this objective: the indicated
line contains a whole ray of nondifferentiability.

The repository already contains a formal obstruction of this kind:
`BfgsVerification.FivePieceObstruction.no_differentiable_armijo_wolfe`, for
`max{-x,y+z,-y+z,x/4,-z}` at `(-2,0,1)`, `H0=I`, constants `(1/4,1/2)`.
It is presented in `companion/chapters/06_F.tex:189-203`. Thus the limitation is
supported by existing Lean evidence as well as the simpler analytic example
above. Full-space differentiability of the objective is essential; smoothness
of its one-dimensional restriction is not enough.

### 6.2 A certificate is sufficient, not necessary

The article explicitly makes this distinction (`sections/energy.tex:318-321`).
Companion Chapter 5 gives scalar convergent cases with no certificate on the
specified positive bands; Chapter 10 gives
`max{u²+v,3u²,2u²-v}` with an explicit nonradial certificate despite flat contour
pieces and failure of radial control. Thus neither the planar strict-contour
route nor the fixed radial field exhausts the abstract certificate theorem,
and the certificate theorem does not exhaust successful BFGS behavior.

The positive routes also overlap without being identical: `u²+|v|` satisfies
both the radial and planar hypotheses, whereas the ℓ₁ norm has flat positive
contours but still belongs to the global homogeneous/radial class. The printed
three-quadratic example goes in the other direction: its planar hypotheses hold
but its radial condition fails locally.

### 6.3 The negative results delimit the guarantees, not typical performance

The two local failure objectives and their starts are constructed together;
the specified deterministic search is proved to generate their full histories.
One uses four convex C²,¹ branches with an upper Hessian bound but no common
positive lower bound. The other uses four uniformly strongly convex C¹,¹
branches, the first three not twice differentiable at the minimizer. Both use
`H0=I` and the stated range `0<c1<=1/3`, `c1<c2<1`.

These two local embeddings do not settle the every-start **local-neighborhood**
convergence question for finitely many uniformly strongly convex C² branches,
outside the nondegenerate planar case. Global convergence for that class already
fails for the quadratic-perturbed seed in `art:quadratic_failure`:

\[
Q_\mu(x)=\max_i\{\tfrac\mu2\|x\|^2+g_i^Tx\},\qquad\mu>0.
\]

Each of its three branches has Hessian `mu I`, yet the constructed implemented
run converges to the nonoptimal origin; `min Q_mu=-1/(514 mu)<0`.
This is not a failure from every sufficiently small neighborhood of its true
minimizer. The article explains why the local embeddings violate the positive
planar theorem's nondegeneracy at the minimizer in
`sections/verification.tex:22-38`. It leaves the more general **local**
C²/strong-convexity question and the almost-sure semialgebraic challenge open
(`sections/verification.tex:53-63`). No positive-measure bad-initialization set
or generic-failure result has been established here.

### 6.4 One companion non-vacuity question is genuinely open

Chapter 7's common-tilt family `f(u,t)=t+max_i b_i^T u` and Theorem 7.B(ii)
remain conditional on an infinite admissible run. Existing Lean results prove
that such runs do **not** exist in dimension at most two and for the specified
collinear/two-piece cases in any dimension. The noncollinear higher-dimensional
case is open. This is already recorded in `TODO_LEAN_REVIEW.md`, under
“Companion Chapter 7 (H): run statements that may be vacuous.”

It should be stated explicitly alongside that companion result. It is not an
unresolved satisfiability problem for the article's centered, polyhedral or
explicit planar convergence examples.

## 7. Recommended presentation changes

The review suggests an expository addition, rather than changing the theorem
claims:

1. Follow the existing scope table with a short “How to verify the hypotheses”
   table: simple sufficient test, explicit objective, actual-run witness, and
   local/global scope.
2. Show one complete certificate and nonsmooth BFGS history (Section 3). This
   explains what the long field definition is asking for and why matrix
   degeneration is allowed.
3. For centered objectives give `-grad psi(x*) in partial gamma(0)`; for a
   finite linear maximum give positive spanning; for Lasso give a transparent
   sufficient uniqueness assumption; for planar maxima give the strong-convexity
   special case and the small active-gradient linear system.
4. State the run-existence result for the existing three-quadratic example in
   the manuscript, not just in the Lean module and coverage notes. Retain the
   distinction from universal success of a chosen line-search implementation.
5. Use the simple two-branch family in Section 5 if a further worked example
   would help, with its proof/Lean coverage added when it is promoted.
6. Say explicitly that the conditions describe substantial sufficient classes,
   not a generic classification of convex nonsmooth BFGS, and flag the existing
   Chapter 7 exception where it is stated.

Tracked as M42 in `TODO_MANUSCRIPT_REVIEW.md`. The non-vacuity question of
Chapter 7 retains its existing open entry in `TODO_LEAN_REVIEW.md`.

## 8. Review and evidence record

The independent formal-evidence audit inspected the released PDFs as well as
the source statements and constructions. It found no new main-result vacuity
or proof gap. A cached-import Lean check resolved 29 signatures and inspected
14 axiom dependencies, all standard; see `FORMAL_CHECKS.lean.txt` and
`FORMAL_CHECKS.log`. The strongest evidence is not limited to scalar examples:

| Joint witness | Existing formal evidence | Exact scope of the witness |
|---|---|---|
| Mixed ridge `u²+|v|` | `BfgsVerification.UnexcitedMetric.run` | Full-BFGS run for every valid pair after choosing its contraction factor; special diagonal initial matrix. |
| Two-dimensional, varying-Hessian PLQ | `BfgsCoverage.Companion.Ch04R.plq2d_low_runs` | For every positive basin height a run starts at or below it; the proof uses `H0=I`, `(1/4,1/2)`. |
| Non-axis ℓ₁ run | `BfgsCoverage.Companion.Ch07H.bw_run_exists` | Several exact two-dimensional steps with a non-diagonal initial matrix, followed by an infinite continuation. |
| Printed three-quadratic objective | `BfgsVerification.PlanarQuadraticExample.nonradial_example_nonvacuous`; anonymous example in `Coverage/Companion/Ch09C.lean:4722-4751` | Every SPD matrix and valid pair; an explicit start in `F<1/100`, and starts in arbitrarily small positive basins. |
| Flat-contour parabolic certificate | `BfgsCoverage.Companion.Ch10Q.example_run_exists`, together with `BfgsVerification.Parabolic.Family.hasBandCertificates` | Every differentiable start, every SPD matrix and valid pair; moving rank-one fields on the bands. |
| Both local negative constructions | `BfgsCoverage.Article.NegativeUpper.local_failure`; `BfgsCoverage.Article.NegativeLower.local_failure_lower` | Actual implemented infinite runs, identity initialization, uniform over the stated constant range. |

The independent mathematical reviewer verified the complete mixed-ridge
certificate and run, the support-function family, positive-spanning test,
Lasso basin, two-quadratic family and its arbitrary-data run existence,
radial-obstruction formulas, and the max-linear first-step obstruction.
Three scope corrections to the draft were applied:

| Review finding | Resolution |
|---|---|
| R1: reversed relation between affine criticality and stationarity | Section 4.4 now says that stationarity implies affine criticality, not conversely. |
| R2: blanket exclusion of affine intercepts | Section 4.2 distinguishes general affine maxima from redundant offset branches and removable additive constants. |
| R3: omitted local qualifier in the open C²/strong-convexity question | Section 6.3 explicitly separates the open local guarantee from the already-proved global failure for strongly convex quadratic maxima. |

The suggested clarifications were also applied: loss regularity is explicitly
locally C¹,¹, the two-quadratic theorem application uses positive sublevels,
and the scope table distinguishes illustrative examples from already printed
ones. The existing-source audit's presentation recommendations NV-F1–NV-F4
are incorporated in M42; its Chapter 7 finding retains the existing open TODO.

The existing-source audit did not locate a concrete dimension-at-least-two
higher-rank certificate example in the package. The focused follow-up now
supplies one as a new scratch proof (`HIGHER_RANK.md`), including the theorem's
full conjunction of assumptions and an actual run, rather than just a matrix
identity. Its objective uses the Euclidean `sqNorm`, not the ambient Pi norm;
the field rank is exactly the arbitrary dimension. The six inspected axiom
dependencies are standard. This closes the illustrative gap for the present
review while leaving incorporation into the manuscript/package under M42.

Repository checks at completion: `check_coverage.py --strict` passes for all
2475 registered items, and the October correspondence check
`editorial/release_20261015/refresh_correspondence.py --check` passes. The new
proof input and output are archived with this review for replay.
