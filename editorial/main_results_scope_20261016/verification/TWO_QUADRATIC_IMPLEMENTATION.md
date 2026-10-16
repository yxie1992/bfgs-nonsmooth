# M42: complete two-quadratic-family verification

## Result

**Complete, including the optional fixed-band radial obstruction.**

Repository file: `bfgs_lean_article/BfgsArticle/TwoQuadraticExample.lean` (1036 lines).
Namespace: `BfgsVerification.TwoQuadraticExample`, with radial specialization in
`BfgsVerification.TwoQuadraticExample.Radial`.

Source SHA-256:
`cd5e4550d341a44442925692125100e3bb952c1e110d0a75dc8004ee545ba518`.

The assignment named HEAD `6145363`. The shared repository was at
`3de9c74910a13b0c2a52fa8c537eb5b82cf8d5e7` when completion metadata was read.
This subagent made no git mutations. The only repository file written is the
owned module; all compile artifacts and this report are in the assigned scratch
directory. The owned module was untracked at handoff.

Imports are exactly:

```lean
import BfgsArticle.AdmissibleRunExistence
import BfgsVerification.PlanarMaxHessianBasin
```

No root or coverage import, stage1 modification, Lake build/update/clean/exe,
proof placeholder, extra axiom, native decision procedure, or linter suppression
was used. Each Lean invocation ran alone with `LEAN_NUM_THREADS=4`.

## TeX-ready family statement

The following statement is fully proved, with the quantifiers as written.

```tex
Let $a,b,c>0$, and set
\[
 f_0(u,v)=au^2+bv^2+v,\qquad
 f_1(u,v)=cu^2+bv^2-v,\qquad F=\max\{f_0,f_1\},
 \qquad \mu=2\min\{a,b,c\}>0.
\]
Both branches are convex quadratic polynomials and are $C^\infty$ on $\R^2$.
Their actual gradients and Hessians are
\[
 \nabla f_0=(2au,2bv+1),\quad \nabla f_1=(2cu,2bv-1),\qquad
 \nabla^2 f_0=\operatorname{diag}(2a,2b),\quad
 \nabla^2 f_1=\operatorname{diag}(2c,2b),
\]
and $\nabla^2 f_i\succeq\mu I$. The finite convex objective $F$ is
$\mu$-strongly convex in the Euclidean norm and satisfies
\[
 F(u,v)\ge\frac{a+c}{2}u^2+bv^2,\qquad F(0)=0.
\]
Thus $0$ is its unique minimizer. Every sublevel is compact, and the boundary
of every sublevel contains no nontrivial line segment.

Full-space differentiability holds exactly when
$v\ne(c-a)u^2/2$. On the tie curve,
\[
 \det\bigl(\nabla f_0,\nabla f_1\bigr)
 =-2u\bigl[a+c+b(c-a)^2u^2\bigr].
\]
The active gradients are linearly independent at every nonzero tie point,
and the affine-critical set is exactly $\{0\}$.
At every point outside this set the objective satisfies the smooth or
regular convex two-branch alternative of Theorem~\ref{art:planar-cluster}.
At the minimizer the two indexed active gradients are $(0,1)$ and $(0,-1)$;
they are affinely independent and balanced by the strictly positive weights
$(1/2,1/2)$.

Consequently, for every $B>0$, all the hypotheses of
Theorem~\ref{art:planar-cluster} and Corollary~\ref{art:planar-convergence}
hold on $K_B=\{F\le B\}$. The hypotheses of
Corollary~\ref{art:planar-max} hold as well, with the global two-branch
representation. Every infinite admissible full-BFGS run converges in value
and iterates to $0$, and its Euclidean distance to $\arg\min F$ tends to zero.

Moreover, for every full-space differentiability point $x_0$, every SPD
matrix $H_0$, and every fixed pair $0<c_1<c_2<1$, there exists an infinite
admissible full-BFGS run with precisely these initial data and constants.
Its initial gradient is $\nabla F(x_0)$, and it converges in value and
iterates to zero.
```

The value/iterate conclusion is global: the formal theorem chooses
`B = F(R.x 0) + 1`. For any separately prescribed `B>0`, the same theorem
applies to every run with `F(R.x 0) ≤ B`. The local finite-max theorem is also
instantiated directly, yielding `∃ ε>0, ∀ R, F(R.x 0)<ε → convergence`, with
the basin chosen before the run, matrix, and constants.

The run-existence statement concerns a choice of accepted steps. It asserts
existence of the full infinite `AdmissibleBFGSRun`, not success of a specified
line-search implementation.

## Full-space derivative and existence verification

`differentiableAt_iff` is an equivalence for `DifferentiableAt ℝ F x` on
`Vec 2`, with no restriction to any ray or interface. Its proof works for all
real `a,b,c`, hence in particular for the positive family. Strict branch gaps
give the actual ambient Fréchet derivative. At a tie, differentiability of
`F` would force both active branch gradients to equal its derivative: each
`F-f_i` has a local minimum there. Their second coordinates differ by two,
which gives a contradiction.

For every `x,p : Vec 2` with `F` differentiable at `x`, the bad-time set
`{t : ℝ | ¬ DifferentiableAt ℝ F (x+t • p)}` is finite. This includes `p=0`.
The polynomial used is

```tex
 (a-c)p_u^2 t^2+
 \bigl[2(a-c)x_u p_u+2p_v\bigr]t+
 \bigl[(a-c)x_u^2+2x_v\bigr].
```

Its constant term is nonzero by the full-space differentiability equivalence.
`AdmissibleRunExistence.quadratic_zeros_finite` gives finiteness, hence the
required countability. The module proves convexity, boundedness below, and
absence of a zero gradient at any differentiability point; it then applies
`AdmissibleRunExistence.exists_admissible_run` with arbitrary prescribed
`x₀,H₀,c₁,c₂`. This argument covers both `a≠c` and `a=c`.

## Exact hypothesis packages and library APIs

The library exposes the main results through theorem arguments rather than one
pre-existing all-hypotheses record. The new proposition records bundle those
arguments with this example's fixed minimizer and domain:

- `PaperRegularAt` (line 486): literally the article/coverage neighborhood
  alternative, including an open neighborhood, convex `C²` branches, both
  branches active, and linear independence of their `coordinateGradient`s.
- `paper_planar_hypotheses` (526): one conjunction of the literal article
  hypotheses for any `B>0`, including `IsLeast (range F) 0`, compactness, strict
  contours, `PaperRegularAt`, and
  `C_aff ∩ {F≤B} ⊆ argmin F`.
- `PlanarHypotheses` (545): convexity, attained minimum zero, `0<B`, compact
  sublevel, strict contours, the native library regularity alternative
  `ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p`, and
  `AffineCriticalObjective.AffineCorrectAt F p` throughout the sublevel.
  `planar_hypotheses` constructs every field from `a,b,c>0`.
- `FiniteMaxHypotheses` (605): convexity, unique minimizer zero, convex `C²`
  branches on `univ`, global `IsGreatest` representation, low strict contours,
  indexed affine independence, positive weights, sum one, and zero weighted
  gradient. The active index type is literally
  `ConvexSubdifferential.activeIndices F f 0`, not a deduplicated set of
  gradients. `I_*={0,1}` is proved at line 566, and `finite_max_hypotheses`
  uses the constant weight function `1/2`. The domain `U=univ` is open and
  contains zero; these facts are passed directly to the library theorem.
- The private conversion at line 630 reindexes the actual active subtype by
  `activeIndexMap` using its order isomorphism. `local_finite_max_convergence`
  directly applies `PlanarMaxRegular.finite_max_local_basin` with those data.
- `convergence_on_sublevel` directly applies
  `AdmissibleBFGSRun.planar_convergence_on_sublevel` with the proved native
  package; uniqueness supplies the whole-sequence limit.

`FixedNormal.EuclideanStrongConvexOn univ μ F` means precisely that
`F(x) - (μ/2)*sqNorm x` is convex. `sqNorm` is the sum of the two coordinate
squares. Thus the modulus is Euclidean, despite the ambient Pi space carrying
the sup norm. `RadialHessian.matrix` is the matrix of the actual second Fréchet
derivative; it is proved equal to the displayed diagonal matrix.

`AffineCriticalObjective.IsAffineCritical` is the library's affine hull of
the actual convex subdifferential. The proof uses the exact finite-max
subdifferential formula and affine coefficients, not a chosen gradient subset
or an assumed correctness certificate.

## TeX-ready radial specialization

This optional part is fully implemented.

```tex
For $a=b=1,c=2$, fix $r>0$ with $r^2<3$, set $v_0=r^2/2$, and for
$\varepsilon>0$ put
\[
 x=(r,v_0+\varepsilon),\qquad z=(r,v_0-\varepsilon/2).
\]
The branches $f_0$ and $f_1$, respectively, are strictly active at the
endpoints, which are differentiable in the ambient plane. With the actual
endpoint gradients, the pair quantities satisfy
\[
 \begin{aligned}
 d&=\tfrac32\varepsilon(1+r^2+2\varepsilon),&
 t&=3\varepsilon+\tfrac92\varepsilon^2,\\
 \Delta&=(\tfrac12+\tfrac32r^2)\varepsilon+\tfrac34\varepsilon^2,&
 N=y^Tz&=r^2+(1-\tfrac32r^2)\varepsilon+\tfrac32\varepsilon^2.
 \end{aligned}
\]
These pairs are eligible for $(c_1,c_2)=(1/4,1/2)$ for every
$\varepsilon>0$. As $\varepsilon\downarrow0$, $d\to0$, $t\to0^+$,
$N\to r^2$, and $N^2/t\to+\infty$.

Set $\ell(r)=3r^2/2+r^4/4>0$ and
$A_r=\{\ell(r)/2\le F\le2\ell(r)\}$. For every $\delta>0$ and every
$C\in\R$, there is an $\varepsilon>0$ for which both endpoints belong to
this same fixed band, the pair is eligible, $d\le\delta$, and $N^2>Ct$.
For every neighborhood $U$ of zero, some $r>0$, $r^2<3$, has
$A_r\subset U$ and the preceding property. In particular the radial
secant condition fails on every neighborhood of zero and on every
positive sublevel.
```

The quantifier order is explicit in `Radial.radial_obstruction_in_every_neighborhood`:
`∀ U ∈ 𝓝 0, ∃ r>0, ... band r ⊆ U ∧ ∀ δ>0, ∀ C, ∃ ε>0, ...`.
Thus neither the band nor its positive lower level depends on `ε`, `δ`, or `C`.
The entire band is placed in `U` by the proved unique-minimizer localization
theorem. The endpoint pairs used here vary with `ε`; the convergence theorem
and the actual-run witnesses remain as stated above.

## Principal declarations and line references

All short names below have prefix `BfgsVerification.TwoQuadraticExample.`.

| Name | Line | Proved content |
|---|---:|---|
| `branch`, `objective` | 39, 44 | Literal family |
| `modulus`, `modulus_pos` | 56, 58 | `2 min(a,b,c)` and positivity |
| `branch_quadratic`, `branch_contDiff` | 62, 69 | Exact quadratic form; all smoothness orders |
| `branch_hasGradient`, `gradient_coordinates` | 77, 93 | Actual derivatives and gradient formulas |
| `coordinateGradient_eq` | 99 | Identifies the library gradient coordinates |
| `branch_second_hasFDerivAt`, `branch_actual_hessian` | 119, 133 | Actual second derivative and Hessian |
| `branch_actual_hessian_lower_bound` | 153 | Global uniform Hessian lower bound |
| `branch_convex`, `branch_strongConvex` | 158, 170 | Branch convexity and Euclidean modulus |
| `objective_isGreatest`, `localFiniteMax` | 189, 198 | Genuine finite-max representation |
| `objective_convex`, `objective_strongConvex` | 202, 206 | Convexity and strong convexity of the maximum |
| `objective_lower`, `objective_zero`, `objective_unique_zero` | 213, 220, 227 | Averaging lower bound and unique zero |
| `objective_isLeast`, `sublevel_compact` | 245, 249 | Attained minimum and all compact sublevels |
| `tie_equation` | 258 | Exact tie parabola |
| `not_differentiableAt_of_tie`, `differentiableAt_iff` | 299, 313 | Full-space nondifferentiability and exact iff |
| `contDiffAt_of_not_tie` | 323 | Full-space smoothness off the tie |
| `gradient_affineIndependent` | 336 | Original indexed gradients affinely independent everywhere |
| `tie_determinant`, `tie_determinant_ne_zero` | 352, 360 | Exact determinant and its nonvanishing away from zero |
| `tie_gradients_linearIndependent` | 390 | Independent active gradients at every nonzero tie |
| `subdifferential_formula` | 395 | Actual active-gradient convex hull |
| `affineCritical_iff`, `affineCritical_set`, `affineCorrect` | 402, 431, 436 | Exact affine-critical set and global correctness |
| `strict_contours` | 444 | No boundary segments for every level |
| `regular`, `regular_paper` | 472, 493 | Native and literal article regularity |
| `argmin_eq` | 513 | `argmin F = {0}` |
| `paper_planar_hypotheses`, `planar_hypotheses` | 526, 556 | All planar hypotheses jointly, for every positive upper level |
| `initial_activeIndices`, `initial_gradients` | 566, 572 | Both original branches active and gradients `(0,±1)` |
| `initial_balance`, `initial_active_family` | 576, 584 | Positive half weights, indexed independence and balance |
| `finite_max_hypotheses` | 619 | All local finite-max assumptions jointly |
| `local_finite_max_convergence` | 654 | Direct local-theorem application with basin before the run |
| `convergence_on_sublevel`, `global_convergence` | 667, 682 | Value, Euclidean distance, and whole-iterate convergence |
| `nondifferentiable_line_finite` | 695 | Finite bad times on every line through a differentiable start |
| `gradient_ne_zero_of_hasFDerivAt` | 715 | No differentiable stationary point |
| `objective_run_hypotheses`, `exists_admissible_run` | 731, 744 | General existence premises and arbitrary-data run existence |
| `joint_witness` | 760 | All hypotheses, universal convergence, and actual convergent prescribed-data run |
| `Radial.base_value` | 797 | Common limiting level `3r²/2+r⁴/4` |
| `Radial.pair_decrease`, `Radial.pair_curvature` | 822, 829 | Exact `d,t` formulas |
| `Radial.pair_value_difference`, `Radial.radial_numerator` | 837, 845 | Exact `Δ,N` formulas |
| `Radial.pair_eligible` | 856 | Actual eligible pairs for every positive separation |
| `Radial.radial_quotient_tendsto` | 918 | Radial quotient tends to `+∞` |
| `Radial.eligible_radial_unbounded_on_fixed_band` | 928 | Fixed-band failure for all thresholds and candidate constants |
| `Radial.radial_obstruction_in_every_neighborhood` | 959 | Entire fixed positive band inside any neighborhood |
| `Radial.not_radial_secant_on_neighborhood` | 987 | Negation of the native radial-secant property |
| `Radial.not_radial_secant_on_sublevel` | 1002 | Failure on every positive sublevel |
| `concrete_joint_witness` | 1016 | Fully numerical initialization and actual convergent run |

## Genuine numerical example

`concrete_joint_witness` takes `a=b=1,c=2`, `x₀=(0,1/4)`, `H₀=I`,
`c₁=1/4`, `c₂=1/2`. It proves simultaneously:

1. all planar hypotheses for every `B>0`;
2. the local finite-max hypotheses with the indexed half weights;
3. radial-secant failure on every neighborhood of zero;
4. an actual infinite admissible run with precisely these initial data,
   initial objective `5/16`, and values and iterates converging to zero.

This is a concrete specialization of the stronger arbitrary-data `joint_witness`.

## Compilation and axiom checks

The final source compiled successfully with **empty output, no errors and no
warnings**. Log: `final_compile.log` (0 bytes). Command, from
`bfgs_lean_article/`:

```sh
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  -o /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/twoquadratic/BfgsArticle/TwoQuadraticExample.olean \
  BfgsArticle/TwoQuadraticExample.lean
```

The earlier plain `LEAN_NUM_THREADS=4 lake env lean
BfgsArticle/TwoQuadraticExample.lean` check also passed with empty output
(`compile09.log`). The final scratch `.olean` was freshly generated from the
reported source and imported by `AxiomCheck.lean`, with the scratch directory
first in `LEAN_PATH`. A scratch symlink resolves the unchanged cached
`AdmissibleRunExistence.olean` dependency. The axiom check completed with exit 0.

`AxiomCheck.lean` contains **32** principal `#print axioms` commands, covering
all geometry, both hypothesis packages, full-space differentiability, line
finiteness, run existence, global and local convergence, both joint witnesses,
and the radial obstruction. `axioms.log` records every result. **Every inspected
declaration uses only `[propext, Classical.choice, Quot.sound]`.**

The final source scan found no forbidden placeholder/trust tactic or linter
suppression, and no forbidden root/coverage import.

## Handoff and unresolved concerns

No unresolved mathematical or implementation concern was identified. The
optional radial part is complete. The coordinator can now arrange the
independent review and then continue this session for any fix pass, as planned.
Manuscript text, coverage registers, root imports, TODO records and git actions
are the coordinator's integration work.

## Fix pass

Read `../review_twoquadratic/REVIEW.md` and accept its **PASS** verdict:
no required or should-fix findings; all 107 reviewed axiom checks use only
standard axioms. The literal joint hypotheses, arbitrary-initial-data run
quantifiers, and optional fixed-band radial obstruction are confirmed.

The optional exported “at most two” cardinality theorem is unnecessary for
the countability premise. Retain the proved `nondifferentiable_line_finite`
contract. The sharper polynomial-root connecting argument was independently
reviewed analytically under the coverage policy and is correct; the article's
main claims need no weakening.

Original-agent disposition: no core or scratch-olean changes, no repeated Lean
checks, and no remaining concerns. Fix pass complete; ready for integration.
