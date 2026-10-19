import BfgsArticle.AdmissibleRunExistence

/-!
# Lean coverage: `companion/research_story.tex`

The hand-written opening of the companion ("The convergence question and this companion").
Register: `editorial/lean_coverage/register/C_research_story.json`. The text is history and
motivation; its mathematical sentences restate results of the chapters and of the article and are
`SAME_AS` their items (no sentence needs a new statement). The sentence "A different embedding
preserves uniform strong convexity with $C^{1,1}$ branches that lose second differentiability at
the accumulation point" (lines 51-53) repeated the article's discrepancy M8 and its wording issue
M30; it was corrected on 15 October 2026 to "…with $C^{1,1}$ branches, three of which lose second
differentiability at the minimizer" (`BfgsCoverage.Companion.Ch13L.branch_regularity_at_minimizer`);
see the register.

## Value convergence and bounded iterates (lines 30-31)

"The full noncompact homogeneous value alternatives are retained separately: they conclude
objective-value convergence without any conclusion about the iterates, …" (wording point W39,
applied on 15 October 2026; before "value convergence does not imply bounded iterates") is a scope
remark (`NON_CLAIM` in the register): Theorem 7.A
(`C/07_H/heading/001`) concludes objective values only and asserts nothing about the iterates;
whether the zero-value iterates of the degree-one homogeneous objectives converge in recurrent
dimension at least three is open (`BfgsCoverage.Companion.Ch07H.ZeroValueIterateQuestion`).
`value_convergence_unbounded_iterates` below only illustrates the general non-implication behind the
remark, outside the homogeneous class: on $F(x)=e^{x}$ every admissible run has $F(x_k)\to\inf F$
while $x_k\to-\infty$ (weak Wolfe forces $e^{x_{k+1}}\le c_2e^{x_k}$).
-/

noncomputable section
open Set Filter BfgsVerification
open scoped Topology

namespace BfgsCoverage.Companion.ResearchStory

/-- The objective $F(x)=e^{x}$ on $\mathbb R$, written on `Vec 1`. -/
def expObjective (x : Vec 1) : ℝ := Real.exp (x 0)

theorem expObjective_hasGradient (x : Vec 1) :
    HasFDerivAt expObjective (gradientFunctional ![Real.exp (x 0)]) x := by
  have hproj : HasFDerivAt (fun y : Vec 1 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have h := (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x hproj
  convert h using 1
  ext v
  simp [gradientFunctional_apply, dot, mul_comm]

theorem expObjective_gradient_eq {x g : Vec 1}
    (hg : HasFDerivAt expObjective (gradientFunctional g) x) : g 0 = Real.exp (x 0) := by
  have h := hg.unique (expObjective_hasGradient x)
  have := congrArg (fun L : Vec 1 →L[ℝ] ℝ => L (Pi.single 0 1)) h
  simpa [gradientFunctional_apply, dot] using this

theorem expObjective_convex : ConvexOn ℝ univ expObjective := by
  have h := convexOn_exp.comp_linearMap (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  simpa [Function.comp_def, expObjective] using h

/-- Along every admissible run on $F(x)=e^x$: $e^{x_{k+1}}\le c_2e^{x_k}$ (weak Wolfe). -/
theorem exp_run_contraction (R : AdmissibleBFGSRun 1 expObjective) (k : ℕ) :
    Real.exp (R.x (k + 1) 0) ≤ R.c₂ * Real.exp (R.x k 0) := by
  have hg0 := expObjective_gradient_eq (R.hasGradient k)
  have hg1 := expObjective_gradient_eq (R.hasGradient (k + 1))
  have hH := R.positive_definite k
  have hh : 0 < R.H k 0 0 := by
    have := hH.2 (Pi.single 0 1) (by simp)
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using this
  have hw := R.weak_wolfe k
  have hs : (bfgsStep (R.H k) (R.g k) (R.α k)) 0 = -(R.α k * (R.H k 0 0 * R.g k 0)) := by
    simp [bfgsStep, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  have hspos : (bfgsStep (R.H k) (R.g k) (R.α k)) 0 < 0 := by
    rw [hs, hg0]
    have := R.alpha_pos k
    have := Real.exp_pos (R.x k 0)
    have : 0 < R.α k * (R.H k 0 0 * Real.exp (R.x k 0)) := by positivity
    linarith
  simp only [dot, Fin.sum_univ_one] at hw
  rw [hg0, hg1] at hw
  nlinarith

/-- Illustration for Item `C/research_story/prose/017` (`companion/research_story.tex:28-30`), a
scope remark (`NON_CLAIM` in the register, not a claim covered by this theorem): "The full
noncompact homogeneous value alternatives are retained separately: they conclude objective-value
convergence without any conclusion about the iterates" (since 15 October 2026, wording point W39;
before "value convergence does not imply bounded iterates").

The general non-implication behind the remark, outside the homogeneous class, with $F(x)=e^x$:
$F$ is finite and convex with $\inf F=0$ (not attained); admissible runs exist (from every point,
for every $H_0\succ0$ and $0<c_1<c_2<1$: `AdmissibleRunExistence.exists_admissible_run`); and every
admissible run has $F(x_k)\to0=\inf F$ (value convergence) while $x_k\to-\infty$ (unbounded
iterates). -/
theorem value_convergence_unbounded_iterates :
    ConvexOn ℝ univ expObjective ∧ IsGLB (range expObjective) 0 ∧
      (∀ x, 0 < expObjective x) ∧ Nonempty (AdmissibleBFGSRun 1 expObjective) ∧
      ∀ R : AdmissibleBFGSRun 1 expObjective,
        Tendsto (fun k => expObjective (R.x k)) atTop (𝓝 0) ∧
          Tendsto (fun k => R.x k 0) atTop atBot := by
  have hpos : ∀ x, 0 < expObjective x := fun x => Real.exp_pos _
  refine ⟨expObjective_convex, ⟨?_, ?_⟩, hpos, ?_, fun R => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (hpos x).le
  · intro b hb
    have hlim : Tendsto (fun t : ℝ => expObjective ![t]) atBot (𝓝 0) := by
      simpa [expObjective] using Real.tendsto_exp_atBot
    exact ge_of_tendsto hlim (Eventually.of_forall fun t => hb ⟨![t], rfl⟩)
  · obtain ⟨R, -⟩ := AdmissibleRunExistence.exists_admissible_run expObjective_convex
      ⟨0, by rintro _ ⟨x, rfl⟩; exact (hpos x).le⟩
      (fun x p _ _ => by
        have : {t : ℝ | ¬ DifferentiableAt ℝ expObjective (x + t • p)} = ∅ := by
          ext t
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
          exact (expObjective_hasGradient _).differentiableAt
        rw [this]
        exact countable_empty)
      (fun y g hg h0 => by
        have := expObjective_gradient_eq hg
        rw [h0] at this
        simp at this
        exact (Real.exp_pos _).ne' this.symm)
      (expObjective_hasGradient 0) Matrix.PosDef.one (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨R⟩
  · have hc₂ : 0 < R.c₂ := R.c₁_pos.trans R.c₁_lt_c₂
    have hbound : ∀ k, expObjective (R.x k) ≤ R.c₂ ^ k * expObjective (R.x 0) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc expObjective (R.x (k + 1)) ≤ R.c₂ * expObjective (R.x k) := exp_run_contraction R k
          _ ≤ R.c₂ * (R.c₂ ^ k * expObjective (R.x 0)) := mul_le_mul_of_nonneg_left ih hc₂.le
          _ = R.c₂ ^ (k + 1) * expObjective (R.x 0) := by ring
    have hgeo : Tendsto (fun k => R.c₂ ^ k * expObjective (R.x 0)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc₂.le R.c₂_lt_one).mul_const
        (expObjective (R.x 0))
    have hval : Tendsto (fun k => expObjective (R.x k)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo
        (fun k => (hpos _).le) hbound
    refine ⟨hval, ?_⟩
    have hval' : Tendsto (fun k => Real.exp (R.x k 0)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hval, Eventually.of_forall fun k => hpos (R.x k)⟩
    have h := Real.tendsto_log_nhdsGT_zero.comp hval'
    simpa [Function.comp_def, Real.log_exp] using h

end BfgsCoverage.Companion.ResearchStory
