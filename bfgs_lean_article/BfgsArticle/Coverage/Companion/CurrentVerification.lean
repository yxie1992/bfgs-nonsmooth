import BfgsVerification.UnexcitedMetric
import BfgsArticle.Coverage.Article.Global

/-!
# Lean coverage: `companion/current_verification.tex`

The dated verification record that opens Chapter 14 of the companion (`\input` at
`companion/chapters/14_E.tex:5`): "The October 2026 Lean review" (before 15 October 2026 "The 13
October 2026 Lean review") and "The 12 September 2026 narrative-revision replay". The file is
written by hand. Register: `editorial/lean_coverage/register/C_current_verification.json`.

## Reading

* The sentences about builds, audits, counts, files and commands are `NON_CLAIM`; each count and
  path was checked (736 modules; the 12 September audit `SUMMARY.json`: 9,672 / 9,781 / 7,954, nine
  dependencies unchanged, status PASS; the two supplements: 3 module-owned theorems and 31,960
  dependencies, 11 declarations and 10,697; the article-geometry review: 14 declarations and 26,496;
  the branch review: 3 declarations and 37,525). Lines 8-11 were refreshed on 15 October 2026
  (wording point W30): "All 2026 Lean names" became the 5403 names of the axiom audit of that day
  (`bfgs_lean_article/AXIOM_AUDIT.json`, commit `9f03d7c`, PASS: every name then cited by the
  claim ledger or the coverage registers and the principal declarations of the package), and the
  kernel replay re-checked every project module except the two root modules, which contain only
  imports (783 of 785 modules; `bfgs_lean_article/KERNEL_REPLAY.json`, PASS).
* The mathematical sentences restate article and chapter results and are `SAME_AS` those items:
  the lower-curvature failures for every $0<c_1\le1/3$, $c_1<c_2<1$ with one orbit, objective and
  set of starts (lines 6-8: Proposition `art:quadratic_failure`, Theorem
  `art:local-failure-lower`); the mixed benchmark (lines 46-47: Corollary `art:mixed-benchmark`);
  matched-scaling covariance and the construction contracts (lines 51-52: the article's
  `art:matched-scaling` items and the embedding run items); the first three whitened branches are
  not twice differentiable at zero (lines 67-69: Theorem `art:local-failure-lower`, the restriction
  argument `A/lower_curvature/prose/020`; the statement is about the first three branches only, so
  the M8 pattern does not recur).
* No item needs its own Lean statement. The `example` below shows that the universally quantified
  mixed-benchmark statement is not vacuous.
-/

noncomputable section
open scoped Topology
open Filter BfgsVerification

namespace BfgsCoverage.Companion.CurrentVerification

/-- Non-vacuity for Item `C/current_verification/prose/020`
(`companion/current_verification.tex:45-46`): "The literal mixed-benchmark theorem quantifies over
every actual admissible run for $u^2+|v|$ and proves both value and whole-iterate convergence."
Admissible runs on $u^2+|v|$ exist (`UnexcitedMetric.run`, from $x_0=(0,1)$ with $c_1=1/4$,
$c_2=1/2$), and along such a run the values and the iterates converge to $0$ (the article's
Corollary `art:mixed-benchmark`). -/
example : ∃ (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F), (∀ x, F x = (x 0) ^ 2 + |x 1|) ∧
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hF : ∀ x, UnexcitedMetric.objective x = (x 0) ^ 2 + |x 1| := fun _ => rfl
  let R := UnexcitedMetric.run 1 1 (1 / 2) (1 / 4) (1 / 2) one_pos one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, R, hF, BfgsCoverage.Article.Global.mixed_benchmark _ hF R⟩

end BfgsCoverage.Companion.CurrentVerification
