# M42 independent review: the two-quadratic family

## Verdict

**PASS. No required fixes.** The same literal objective, for every `a,b,c > 0`,
satisfies the complete joint planar and local finite-maximum assumptions. The
implementation proves existence of an actual infinite admissible full-BFGS run
from **every full-space differentiability point, every SPD initial matrix, and
every fixed `0 < c₁ < c₂ < 1`**. It separately proves convergence of **every**
infinite admissible run. Neither conclusion is obtained by assuming the other.
Both joint witnesses are non-vacuous. The optional radial obstruction also has
the required fixed-band quantifiers and uses actual eligible endpoint gradients.

The draft family proposition and general run-existence lemma are mathematically
correct and compatible with their Lean evidence. I found no omitted hypothesis,
reversed quantifier, substitute geometric property, or false mathematical claim
in the reviewed text.

### Findings and disposition

- **Must fix:** none.
- **Should fix:** none.
- **Optional evidence strengthening:**
  `paper/appendices/hypothesis_examples.tex:155–158` says there are **at most two**
  nondifferentiability points on such a line. This is correct: the tie polynomial
  has degree at most two and a nonzero constant term. The public contract of
  `TwoQuadraticExample.nondifferentiable_line_finite` at
  `bfgs_lean_article/BfgsArticle/TwoQuadraticExample.lean:695–713` exports
  finiteness, rather than the sharper cardinal bound. If a separately exported
  version of this exact proof step is desired, add a theorem bounding the
  bad-time set's cardinality by two using the same polynomial and the polynomial
  root-cardinality bound. **No correction is required:** this is an undisplayed
  connecting step inside the proof, which the coverage policy explicitly leaves
  to the line-by-line mathematical review
  (`editorial/lean_coverage/README.md:11–13,100–104`), and finiteness is stronger
  than the countability premise actually needed for run existence. This is a
  difference in the granularity of exported evidence, not a source error or a
  missing joint hypothesis.

## Reviewed snapshot and method

- Repository: `/Users/yxie/Projects/bfgs-nonsmooth`.
- HEAD recorded during verification:
  `3de9c74910a13b0c2a52fa8c537eb5b82cf8d5e7`.
- Production module: `bfgs_lean_article/BfgsArticle/TwoQuadraticExample.lean`,
  1036 lines; namespace `BfgsVerification.TwoQuadraticExample`, with `Radial`
  nested inside it.
- Module SHA-256:
  `cd5e4550d341a44442925692125100e3bb952c1e110d0a75dc8004ee545ba518`.
  This agrees with `../twoquadratic/FINAL_REPORT.md`.
- Read `AGENTS.md`, `HANDOFF.md`, the implementation report, the entire production
  module, and the exact definitions/contracts used by its principal applications.
- Draft scope: `hypothesis_examples.tex:87–162`, the relevant added summaries in
  `geometry.tex:111–138` and `local.tex:444–451`, and the underlying article
  results at `local.tex:214–229,276–287,303–361`.
- All 102 explicit production declarations were inspected, including 83 theorems
  and both private helper theorems. The declaration inventory with exact starting
  lines is `declarations.json`.
- All work products are in this review directory. There were no repository edits
  or git mutations. The recorded Lean and TeX source hashes were identical before
  and after the compilation/audit (`metadata.json`).

## Literal objective, derivatives, and geometry

The definitions at lines 39–56 are exactly

\[
f_0(u,v)=au^2+bv^2+v,\quad f_1(u,v)=cu^2+bv^2-v,\quad
F=\max(f_0,f_1),\quad \mu=2\min(a,\min(b,c)).
\]

The original index type is `Fin 2`; no branch is silently removed or deduplicated.

1. **Actual Euclidean derivatives.** `branch_hasGradient` proves the ambient
   Fréchet derivative represented by `gradientFunctional`, whose application is
   the ordinary coordinate dot product. `gradient_coordinates` gives
   `(2au,2bv+1)` and `(2cu,2bv−1)`. `coordinateGradient_eq` identifies the
   library's gradient with these vectors. `branch_second_hasFDerivAt` differentiates
   the actual first derivative; `branch_actual_hessian` identifies its matrix
   with `diag(2a,2b)` or `diag(2c,2b)`. This is not a formal Hessian assigned
   independently of differentiation.
2. **Positive common curvature.** `modulus_pos` supplies strict positivity under
   the three positive parameter assumptions. `hessian_lower_bound` and
   `branch_actual_hessian_lower_bound` give the global PSD differences from
   `μ I`. Their validity for arbitrary real parameters is intentional: positivity
   of the modulus is a separate theorem.
3. **Euclidean strong convexity and finite convexity.** The strong-convexity
   predicate is literally convexity of `F − (μ/2) * sqNorm`; `sqNorm` is the sum
   of squared coordinates. Thus there is no confusion with the sup norm on
   `Vec 2`. Branch convexity, finite-max representation, objective convexity,
   and strong convexity are all proved for these definitions.
4. **Minimum and sublevels.** The averaging bound
   `((a+c)/2)u² + bv² ≤ F(u,v)`, together with `F(0)=0`, gives nonnegativity,
   the attained minimum, and its uniqueness. `sublevel_compact` covers every real
   upper level, not merely one preselected positive level. Its use of the proved
   finite-dimensional localization theorem has the required attained-minimum and
   uniqueness premises.
5. **Strict contours.** `strict_contours` excludes any nontrivial segment in the
   frontier of every sublevel. It uses the strong-convexity midpoint inequality
   with `μ>0`, not a replacement such as uniqueness of the minimizer or strictness
   of individual branches alone.
6. **Full-space differentiability.** `differentiableAt_iff` says precisely
   `DifferentiableAt ℝ F x ↔ x₁ ≠ (c−a)x₀²/2`. Off the tie, a strict winner
   persists on an ambient neighborhood. On the tie, differentiability would
   force both active branch gradients to equal the derivative of `F`, because
   each `F−fᵢ` has a local minimum there. Their second components differ by two.
   The proof covers all real parameters, including `a=c`; it does not infer
   ambient differentiability from differentiability along a line.
7. **Determinant and genuine affine criticality.** On the tie, direct substitution
   gives
   \[
   \det(g_0,g_1)=-2u\,[a+c+b(c-a)^2u^2].
   \]
   The bracket is positive when `a,b,c>0`; a tie with `u=0` is the origin. Thus
   the gradients are linearly independent at every nonzero tie point. For
   `a=c`, the determinant is `−4au`, so the line case is included. The
   subdifferential formula is for the actual global convex supporting-vector
   set. `affineCritical_iff` uses its affine hull, through the library's exact
   coordinate/Euclidean equivalence, and proves `C_aff={0}`. It does not define
   criticality using a convenient chosen subset of gradients.
8. **Local regularity.** At a nonzero tie, `regular_paper` supplies both original
   convex `C²` branches on an open neighborhood, the exact max representation,
   both active equalities, and linear independence at the point. Off the tie it
   supplies an open set on which `F` is `C²`. The native `regular` theorem also
   uses the actual library two-branch contract.

## Exact joint hypothesis and quantifier coverage

| Article requirement | Production evidence | Review result |
|---|---|---|
| Finite convex `F : ℝ² → ℝ`, attained minimum `F*=0` | `objective`, `objective_convex`, `objective_isLeast` | Literal total real-valued family; no extended-value/domain restriction. |
| For each prescribed `B>0`, compact `K_B={F≤B}` | `paper_planar_hypotheses:526–540`, `planar_hypotheses:556–561` | `∀ B>0` is outside any choice of run or initial matrix. |
| No boundary segment for **every** `0<t≤B` | Those packages, using `strict_contours:444–470` | Correct level and endpoint quantifiers; actually established for all levels. |
| Smooth or regular convex two-branch chart at **every** `p∈K_B\C_aff` | `PaperRegularAt:486–491`, `regular_paper:493–511`; native field at `552–553` | The paper version includes an open neighborhood and all branch/activation/independence data. It is not merely pointwise differentiability. |
| `C_aff∩K_B ⊆ argmin F` | Final conjunct of `paper_planar_hypotheses`; `PlanarHypotheses.correct` | Proved from actual affine criticality. Native `AffineCorrectAt` means `0∈∂F`, exactly optimality here. |
| Unique minimizer, locally convex `C²` branches, finite-max representation | `FiniteMaxHypotheses:605–617`, `finite_max_hypotheses:619–628` | Stronger global branch/domain data are supplied; `U=univ` is open and contains zero. |
| Strict sufficiently low positive contours | `FiniteMaxHypotheses.contours` | Supplies an upper level `B=1` before the run, with all intermediate levels included. |
| Affine independence of the **indexed active family** at zero | `initial_activeIndices:566–569`, `initial_active_family:584–601` | The actual active subtype contains both original indices. No set-level deduplication weakens the claim. |
| Strictly positive weights, sum one, zero weighted gradient | `initial_gradients`, `initial_balance`, `initial_active_family` | The two actual gradients are `(0,1),(0,−1)` with explicit weights `1/2,1/2`. |
| Local basin independent of matrix and constants | `local_finite_max_convergence:654–664` | Direct application of `PlanarMaxRegular.finite_max_local_basin`; `∃ ε>0, ∀ R` in that order. |
| Convergence on every positive sublevel | `convergence_on_sublevel:667–679` | Includes objective values, Euclidean distance to `argmin F`, and the whole iterate sequence. |
| Convergence of every infinite admissible run globally | `global_convergence:682–688` | Takes `B=F(R.x 0)+1`, which is proved positive. No initial-value restriction remains. |
| Arbitrary differentiable start, arbitrary SPD matrix, arbitrary fixed valid constants | `exists_admissible_run:744–754`, `joint_witness:760–777` | Exact equalities pin the initial point, initial gradient, initial matrix, `c₁`, and `c₂`. |

The native library regularity predicate was inspected in
`bfgs_lean_stage1/BfgsVerification/PlanarConvexCorner.lean:12–17`; the convergence
and finite-max applications were compared with `PlanarConvergence.lean:34–51`
and `PlanarFiniteMaxBasin.lean:12–25`. The explicit `PaperRegularAt` package avoids
any need to treat the native predicate as an unexplained replacement for the
article's neighborhood condition. The private `active_family_conversion` uses
an order isomorphism of the actual active subtype, preserving its weights and
indices when calling the library finite-max theorem.

## Actual infinite runs and non-vacuity

`objective_run_hypotheses:731–739` proves the four existence premises together:
global convexity, boundedness below, finite full-space bad-time sets, and absence
of any zero gradient at a differentiability point.

The line polynomial used at `695–713` is

\[
(a-c)p_u^2t^2+
\bigl(2(a-c)x_up_u+2p_v\bigr)t+
\bigl((a-c)x_u^2+2x_v\bigr).
\]

Its constant term is nonzero at a differentiability point by the proved ambient
equivalence. This works for `a=c`, for tangent directions, and even for `p=0`.
Finite bad-time sets therefore supply the general theorem's countability
hypothesis for every nonzero direction. A differentiable stationary point would
be the unique minimizer by convexity, whereas the origin is proved
nondifferentiable; hence every accepted differentiable endpoint remains
nonstationary.

I checked the existing `AdmissibleRunExistence.lean:85–190,199–244` against the
draft `art:examples-run-existence`:

- SPD and a nonzero actual gradient give `p=−Hg≠0` and `gᵀp<0`.
- The secant slope is continuous on the positive axis, tends to `gᵀp` at zero,
  and exceeds `c₁gᵀp` at a sufficiently large positive step by boundedness below.
- An open interval with slope in `(c₂gᵀp,c₁gᵀp)` contains a point outside the
  full-space exceptional set. The supporting inequality at that endpoint gives
  strict weak Wolfe; the upper slope inequality gives strict Armijo.
- Under global differentiable nonstationarity, the construction chooses a next
  state from **every** valid state and recursively constructs sequences indexed
  by all natural numbers. Positive curvature preserves SPD under the actual
  inverse-BFGS update.

The result is an `AdmissibleBFGSRun`, whose inspected definition at
`ObjectiveDefinitions.lean:30–53` contains all steps, full updates, actual
gradients, nonzero gradients, positive step lengths, and fixed valid line-search
constants. Convergence is not a field of that definition. This is a genuine
infinite-run construction, not a collection of finite prefixes or a theorem
conditional on an assumed infinite run.

`joint_witness` puts the parameter-only hypotheses, universal convergence, and
the prescribed-data existential run in the same conjunction. Its input
conditions are consistent for every positive parameter triple: for example
`(0,1)` lies off the tie for every such triple, the identity is SPD, and
`(c₁,c₂)=(1/4,1/2)` is valid. `concrete_joint_witness:1016–1034` has **no
hypotheses** and specializes to `a=b=1,c=2`, `x₀=(0,1/4)`, `H₀=I`, with these
constants and the independently correct initial value `5/16`. Its existential
run converges in values and iterates. The run existence is not inferred from
the optional radial endpoint construction.

## Optional radial obstruction

**PASS, including the order of all geometric and endpoint quantifiers.**

- Lines 785–795 fix `F=objective 1 1 2`, the tie point
  `(r,r²/2)`, endpoints `(r,r²/2+ε)` and `(r,r²/2−ε/2)`, their actual branch
  gradients, `ℓ(r)=3r²/2+r⁴/4`, and the band
  `A_r={ℓ(r)/2≤F≤2ℓ(r)}`.
- `crossing_active` proves strict winners, and `pair_eligible` obtains the
  **ambient** endpoint derivatives from the winning-branch derivative theorems.
- I independently checked the algebra at lines 817–851:
  \[
  d=\tfrac32\varepsilon(1+r^2+2\varepsilon),\quad
  t=3\varepsilon+\tfrac92\varepsilon^2,
  \]
  \[
  \Delta=(\tfrac12+\tfrac32r^2)\varepsilon+
  \tfrac34\varepsilon^2,\qquad
  N=r^2+(1-\tfrac32r^2)\varepsilon+\tfrac32\varepsilon^2.
  \]
  For `ε>0`, the eligibility margins are
  `Δ−d/4=(1+9r²)ε/8>0`, `d−Δ=ε+9ε²/4>0`, and
  `t−d/2=3(3−r²)ε/4+3ε²>0` when `r²<3`. The constants are the fixed valid
  pair `(1/4,1/2)`.
- The limits at lines 870–924 use the nontrivial right-neighborhood filter:
  both points tend to the fixed tie point, `d→0`, `t→0⁺`, `N→r²`, and
  `N²/t→+∞` for `r>0`.
- `eligible_radial_unbounded_on_fixed_band:928–954` fixes `r>0`, `r²<3`
  **before** `∀ δ>0, ∀ C∈ℝ, ∃ ε>0`. Both endpoints belong to this one
  positive band, satisfy eligibility and `d≤δ`, and violate `N²≤Ct`.
- `radial_obstruction_in_every_neighborhood:959–985` has the exact order
  `∀ U∈𝓝0, ∃ r>0, ... A_r⊆U ∧ ∀ δ>0, ∀ C, ∃ ε>0, ...`.
  The localization theorem puts the **entire band** inside the prescribed
  neighborhood. Neither its positive lower level nor `r` depends on `δ`, `C`,
  or `ε`.
- The final two negation theorems contradict the native
  `RadialCertificate.HasRadialSecantBounds` using ordered, differentiable
  endpoints with strictly positive curvature. Failure is established on every
  neighborhood and every positive sublevel.

These are varying eligible endpoint pairs. The theorem contracts and the
implementation report correctly keep them distinct from successive pairs of
one infinite BFGS trajectory. No claim that one run realizes the obstruction is
made. The optional construction is not asserted in the current draft TeX.

## Remaining declaration-level checks

The following groups complete the contract review of all declarations; each was
also included individually in the axiom inspection.

| Lines | Declarations / contract check |
|---|---|
| 39–75 | `branch`, `objective`, `linearPart`, `hessianDiagonal`, `hessian`, `gradient`, `modulus`, `modulus_pos`, `branch_quadratic`, `branch_contDiff`: exact formulas, index order, and arbitrary smoothness order. |
| 77–139 | `branch_hasGradient`, `gradient_coordinates`, `coordinateGradient_eq`, `hessianFunctional`, `hessianFunctional_apply`, `branch_second_hasFDerivAt`, `branch_actual_hessian`: actual first/second derivatives and coordinate identification. |
| 141–181 | `hessian_lower_bound`, `branch_actual_hessian_lower_bound`, `branch_convex`, `branch_strongConvex`: correct PSD and convexity contracts; positivity hypotheses occur where needed. |
| 183–210 | `branch_le_objective`, `objective_isGreatest`, `localFiniteMax`, `objective_convex`, `objective_strongConvex`: genuine finite maximum, not just upper bounds. |
| 213–253 | `objective_lower`, `objective_zero`, `objective_nonneg`, `objective_unique_zero`, `objective_minimum`, `objective_isLeast`, `sublevel_compact`: attained unique minimum and every-level compactness. |
| 258–332 | `tie_equation`, both `winner_*_eventuallyEq`, both `winner_*_hasGradient`, `gradient_eq_of_active`, `not_differentiableAt_of_tie`, `differentiableAt_iff`, `contDiffAt_of_not_tie`: exact ambient locus and local winner contracts. |
| 336–440 | `gradient_affineIndependent`, `tie_determinant`, `tie_determinant_ne_zero`, private `linearIndependent_of_pairDet_ne_zero`, `tie_gradients_linearIndependent`, `subdifferential_formula`, `affineCritical_iff`, `affineCritical_set`, `affineCorrect`: distinct indexed gradients, correct determinant orientation, actual convex subdifferential and affine hull. |
| 444–561 | `strict_contours`, `regular`, `PaperRegularAt`, `regular_paper`, `argmin_eq`, `paper_planar_hypotheses`, `PlanarHypotheses`, `planar_hypotheses`: literal article and native hypotheses as detailed above. |
| 563–650 | `initial_active`, `initial_activeIndices`, `initial_gradients`, `initial_balance`, `initial_active_family`, `FiniteMaxHypotheses`, `finite_max_hypotheses`, private `active_family_conversion`: actual subtype, positive half weights, and lossless reindexing. |
| 654–777 | `local_finite_max_convergence`, `convergence_on_sublevel`, `global_convergence`, `nondifferentiable_line_finite`, `gradient_ne_zero_of_hasFDerivAt`, `objective_run_hypotheses`, `exists_admissible_run`, `joint_witness`: objective/run assumptions and quantifiers checked separately and together. |
| 785–808 | Radial `F`, `base`, `oldPoint`, `newPoint`, `oldGradient`, `newGradient`, `tieValue`, `band`, `base_value`, `tieValue_pos`: exact specialization, positive fixed levels. |
| 810–868 | Radial `crossing_active`, `pair_step`, `pair_decrease`, `pair_curvature`, `pair_value_difference`, `radial_numerator`, `pair_eligible`: exact endpoint algebra and fixed-constant eligibility. |
| 870–924 | Radial `pair_points_tendsto`, `radial_numerator_tendsto`, `pair_decrease_tendsto`, `pair_curvature_tendsto`, `radial_quotient_tendsto`: correct one-sided filters and positive denominator limit. |
| 928–1010 | Radial `eligible_radial_unbounded_on_fixed_band`, `radial_obstruction_in_every_neighborhood`, `not_radial_secant_on_neighborhood`, `not_radial_secant_on_sublevel`: fixed-band quantifier order and genuine negation of radial bounds. |
| 1016–1034 | `concrete_joint_witness`: closed numerical theorem, actual infinite run, initial value, convergence, and independent radial failure. |

## Draft article and visual inspection

- `hypothesis_examples.tex:89–115`: the general existence lemma and its proof
  agree with `AdmissibleRunExistence.exists_wolfe_step` and
  `AdmissibleRunExistence.exists_admissible_run`. Lines 117–120 correctly specify
  ambient differentiability and the existential nature of accepted-step choices.
- `hypothesis_examples.tex:124–162`: every statement of the family proposition
  is supported with the claimed parameter and initialization quantifiers. The
  determinant, average, Hessian lower bound, critical set, and half weights in
  the proof are correct. The `a=c` case is explicitly acknowledged and fully
  included in Lean.
- The proposition states the active-family assumptions of `art:planar-max`
  explicitly; the module proves **all** of that corollary's hypotheses. The
  shorter statement is an exposition choice, not missing mathematical coverage.
- `geometry.tex:111–138` and `local.tex:444–451` accurately summarize the
  hypothesis checks and distinguish infinite-run existence from the convergence
  quantifier. The family includes curved switching when `a≠c` and a line when
  `a=c`; the summary's description of a family with curved switching does not
  contradict the explicit degeneracy clause. The references to actual runs for
  the printed three-branch example are supported by the existing arbitrary-data
  existence theorem in `AdmissibleRunExistence.lean:431–438`.
- Inspected the supplied `draft_visual/page_06.png`, `page_51.png`, and
  `page_52.png`. The reviewed general-existence/family statements, formulas, and
  references are legible and resolved. The family proposition continues normally
  from page 51 to page 52. No mathematical typesetting discrepancy was found.

## Compilation, axioms, and import hygiene

**Fresh source elaboration: PASS, exit 0, 41.553 seconds, no errors or warnings.**
`Audit.lean` contains the exact complete production source as its prefix,
followed by 107 `#print axioms` commands and principal-type `#check` commands.
The exact-prefix check and complete output parsing both passed.

Command run from `bfgs_lean_article/`, with one Lean process and four threads:

```sh
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/review_twoquadratic/Audit.lean
```

The 107 axiom results comprise **all 102 explicit module declarations** and five
principal imported results: the general step/run existence theorems, quadratic
zero finiteness, planar sublevel convergence, and the finite-max local basin.
Every result uses only `propext`, `Classical.choice`, and `Quot.sound`.
In particular this includes both private helpers, all three hypothesis packages,
both joint witnesses, all run-existence/convergence results, and every radial
declaration. There is no extra axiom or proof placeholder.

The only direct imports are `BfgsArticle.AdmissibleRunExistence` and
`BfgsVerification.PlanarMaxHessianBasin`. A recursive source inspection found 148
project modules in the import closure, no missing project module, and **no
`Coverage.*` or root-module import** anywhere in that project closure. The
production source has no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`implemented_by`, `ofReduceBool`, external implementation annotation, debug trust
option, or linter suppression. Namespace scope is correct.

### Review artifacts

- `Audit.lean`: exact-source compilation and axiom/type inspection input.
- `audit.log`: complete successful Lean output.
- `metadata.json`: command, elapsed time, hashes before/after, HEAD, and diagnostics.
- `axiom_summary.json`: all 107 parsed axiom results and exact-prefix confirmation.
- `declarations.json`: all 102 explicit declarations with kind and starting line.
- `import_hygiene.json`, `project_import_graph.json`: transitive project-import scan.
- `run_audit.py`: reproducible scratch-only audit generator/runner.

**Final disposition:** all reviewed joint family assumptions and actual infinite-run
claims are established. The implementation and draft are ready for the
coordinator's integration, with no required mathematical or Lean fix.
