import BfgsVerification.MaxAffineCalculus

/-! F's literal coercive five-piece objective and its finite line-search obstruction. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace FivePieceObstruction

def family : MaxAffine.Family 3 5 where
  a := ![![-1,0,0],![0,1,1],![0,-1,1],![1/4,0,0],![0,0,-1]]
  b := 0
  nonempty := ⟨0⟩

def objective : Vec 3 → ℝ := family.objective

def ray (τ α : ℝ) : Vec 3 := ![τ*(α-2),0,τ]

def initialGradient : Vec 3 := ![-1,0,0]

def initialMetric (τ : ℝ) : Mat 3 := τ • 1

theorem objective_eq_of_dominates (x : Vec 3) (i : Fin 5)
    (hi : ∀ j, family.branch j x ≤ family.branch i x) : objective x = family.branch i x := by
  apply le_antisymm _ (family.branch_le i x)
  apply Finset.sup'_le
  intro j _
  exact hi j

theorem ray_value_before {τ α : ℝ} (hτ : 0 < τ) (hα : α ≤ 1) :
    objective (ray τ α) = τ*(2-α) := by
  have he := objective_eq_of_dominates (ray τ α) 0 (by
    intro j
    fin_cases j <;> simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray] <;>
      nlinarith [mul_nonneg hτ.le (show 0 ≤ 1-α by linarith)])
  convert he using 1
  simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray]
  ring

theorem ray_value_middle {τ α : ℝ} (hτ : 0 < τ) (hlo : 1 ≤ α) (hhi : α ≤ 6) :
    objective (ray τ α) = τ := by
  have he := objective_eq_of_dominates (ray τ α) 1 (by
    intro j
    fin_cases j <;> simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray] <;>
      nlinarith [mul_nonneg hτ.le (show 0 ≤ α-1 by linarith),mul_nonneg hτ.le (show 0 ≤ 6-α by linarith)])
  simpa [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray] using he

theorem ray_value_after {τ α : ℝ} (hτ : 0 < τ) (hα : 6 ≤ α) :
    objective (ray τ α) = τ*(α-2)/4 := by
  have he := objective_eq_of_dominates (ray τ α) 3 (by
    intro j
    fin_cases j <;> simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray] <;>
      nlinarith [mul_nonneg hτ.le (show 0 ≤ α-6 by linarith)])
  convert he using 1
  simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray]
  ring

theorem ray_gradient_before {τ α : ℝ} (hτ : 0 < τ) (hα : α < 1) :
    HasFDerivAt objective (gradientFunctional initialGradient) (ray τ α) := by
  apply family.strict_active_hasGradient (i := 0)
  intro j hj
  fin_cases j <;> simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray] at hj ⊢ <;>
    nlinarith [mul_pos hτ (show 0 < 1-α by linarith)]

theorem ray_not_differentiable_middle {τ α : ℝ} (hτ : 0 < τ) (hlo : 1 ≤ α) (hhi : α ≤ 6) :
    ¬ DifferentiableAt ℝ objective (ray τ α) := by
  intro hd
  have hg := hasFDerivAt_coordinateGradient hd
  have ha : family.branch 1 (ray τ α) = objective (ray τ α) := by
    rw [ray_value_middle hτ hlo hhi]
    simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray]
  have hb : family.branch 2 (ray τ α) = objective (ray τ α) := by
    rw [ray_value_middle hτ hlo hhi]
    simp [family,MaxAffine.Family.branch,dot,Fin.sum_univ_succ,ray]
  have he := (family.active_eq_gradient ha hg).trans (family.active_eq_gradient hb hg).symm
  have hc := congrArg (fun v : Vec 3 => v 1) he
  change (1 : ℝ) = -1 at hc
  norm_num at hc

/-- Literal source acceptance inequalities with (c1,c2)=(1/4,1/2).
The gradient and both function values are actual objective data. -/
theorem no_acceptable_step {τ α : ℝ} (hτ : 0 < τ) (hα : 0 < α) (g : Vec 3)
    (hg : HasFDerivAt objective (gradientFunctional g) (ray τ α))
    (hArmijo : objective (ray τ α) ≤ objective (ray τ 0)-(1/4)*τ*α)
    (hWolfe : -(1/2) ≤ g 0) : False := by
  by_cases ha : α < 1
  · have he := AffineProjection.gradientFunctional_injective (hg.unique (ray_gradient_before hτ ha))
    have hc := congrArg (fun v : Vec 3 => v 0) he
    simp only [initialGradient,Matrix.cons_val_zero] at hc
    linarith
  · have hlo : 1 ≤ α := le_of_not_gt ha
    by_cases hh : α ≤ 6
    · exact ray_not_differentiable_middle hτ hlo hh hg.differentiableAt
    · have h6 : 6 < α := lt_of_not_ge hh
      rw [ray_value_before (α := 0) hτ (by norm_num),ray_value_after hτ h6.le] at hArmijo
      nlinarith [mul_pos hτ (show 0 < α-6 by linarith)]

theorem objective_zero : objective 0 = 0 := by
  have he := objective_eq_of_dominates 0 0 (by
    intro j
    fin_cases j <;> simp [family,MaxAffine.Family.branch,dot])
  simpa [family,MaxAffine.Family.branch,dot] using he

theorem objective_nonneg (x : Vec 3) : 0 ≤ objective x := by
  have h0 := family.branch_le 0 x
  have h3 := family.branch_le 3 x
  change family.branch 0 x ≤ objective x at h0
  change family.branch 3 x ≤ objective x at h3
  change dot ![-1,0,0] x + 0 ≤ objective x at h0
  change dot ![1/4,0,0] x + 0 ≤ objective x at h3
  norm_num [dot,Fin.sum_univ_succ] at h0 h3
  linarith

theorem unique_minimum {x : Vec 3} (hx : objective x = 0) : x = 0 := by
  have h0 := family.branch_le 0 x
  have h1 := family.branch_le 1 x
  have h2 := family.branch_le 2 x
  have h3 := family.branch_le 3 x
  have h4 := family.branch_le 4 x
  change family.objective x = 0 at hx
  rw [hx] at h0 h1 h2 h3 h4
  change dot ![-1,0,0] x + 0 ≤ 0 at h0
  change dot ![0,1,1] x + 0 ≤ 0 at h1
  change dot ![0,-1,1] x + 0 ≤ 0 at h2
  change dot ![1/4,0,0] x + 0 ≤ 0 at h3
  change dot ![0,0,-1] x + 0 ≤ 0 at h4
  norm_num [dot,Fin.sum_univ_succ] at h0 h1 h2 h3 h4
  ext i
  fin_cases i
  · change x 0 = 0
    linarith
  · change x 1 = 0
    linarith
  · change x 2 = 0
    linarith

theorem objective_convex : ConvexOn ℝ univ objective := family.objective_convex

theorem sublevel_compact (a : ℝ) : IsCompact {x | objective x ≤ a} := by
  apply Localization.sublevel_compact objective_convex 0
  · intro x
    rw [objective_zero]
    exact objective_nonneg x
  · intro x hx
    rw [objective_zero] at hx
    exact unique_minimum hx

theorem objective_coercive : Tendsto objective (cocompact (Vec 3)) atTop := by
  apply tendsto_atTop.2
  intro a
  filter_upwards [(sublevel_compact a).compl_mem_cocompact] with x hx
  change ¬ objective x ≤ a at hx
  exact (lt_of_not_ge hx).le

theorem initialMetric_posDef {τ : ℝ} (hτ : 0 < τ) : (initialMetric τ).PosDef := by
  have he : initialMetric τ = Matrix.diagonal (fun _ : Fin 3 => τ) := by
    ext i j
    by_cases h : i = j <;> simp [initialMetric,Matrix.one_apply,Matrix.diagonal,h]
  rw [he]
  exact Matrix.PosDef.diagonal fun _ => hτ

theorem ray_step (τ α : ℝ) :
    ray τ α = ray τ 0 + bfgsStep (initialMetric τ) initialGradient α := by
  ext i
  fin_cases i <;> simp [ray,bfgsStep,initialMetric,initialGradient,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem step_pairings (τ α : ℝ) (g : Vec 3) :
    dot initialGradient (bfgsStep (initialMetric τ) initialGradient α) = -τ*α ∧
    dot g (bfgsStep (initialMetric τ) initialGradient α) = τ*α*g 0 := by
  simp [dot,bfgsStep,initialMetric,initialGradient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  constructor <;> ring

/-- The finite obstruction is stated using the actual SPD matrix, actual
BFGS search direction, and ordinary Armijo--weak-Wolfe inequalities. -/
theorem no_differentiable_armijo_wolfe {τ α : ℝ} (hτ : 0 < τ) (hα : 0 < α)
    (g : Vec 3)
    (hg : HasFDerivAt objective (gradientFunctional g) (ray τ α))
    (ha : objective (ray τ α) ≤ objective (ray τ 0) +
      (1/4)*dot initialGradient (bfgsStep (initialMetric τ) initialGradient α))
    (hw : (1/2)*dot initialGradient (bfgsStep (initialMetric τ) initialGradient α) ≤
      dot g (bfgsStep (initialMetric τ) initialGradient α)) : False := by
  obtain ⟨hp,hq⟩ := step_pairings τ α g
  rw [hp] at ha
  rw [hp,hq] at hw
  apply no_acceptable_step hτ hα g hg
  · nlinarith only [ha]
  · have ht : 0 < τ*α := mul_pos hτ hα
    nlinarith only [hw,ht]

/-- The same obstruction occurs arbitrarily near the unique minimizer;
the scaling and the initial matrix are constructed, not hypothesized. -/
theorem obstruction_in_every_neighborhood (K : Set (Vec 3)) (hK : K ∈ 𝓝 0) :
    ∃ τ : ℝ, 0 < τ ∧ ray τ 0 ∈ K ∧ (initialMetric τ).PosDef ∧
      HasFDerivAt objective (gradientFunctional initialGradient) (ray τ 0) ∧
      ∀ α : ℝ, 0 < α → ∀ g : Vec 3,
        HasFDerivAt objective (gradientFunctional g) (ray τ α) →
        ¬ (objective (ray τ α) ≤ objective (ray τ 0) +
            (1/4)*dot initialGradient (bfgsStep (initialMetric τ) initialGradient α) ∧
           (1/2)*dot initialGradient (bfgsStep (initialMetric τ) initialGradient α) ≤
            dot g (bfgsStep (initialMetric τ) initialGradient α)) := by
  have hc : Continuous (fun τ : ℝ => ray τ 0) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [ray] <;> fun_prop
  have h0 : ray 0 0 = 0 := by ext i; fin_cases i <;> simp [ray]
  have he : ∀ᶠ τ in 𝓝 (0 : ℝ), ray τ 0 ∈ K := by
    have hh := (hc.continuousAt : ContinuousAt (fun τ : ℝ => ray τ 0) 0).preimage_mem_nhds (by simpa [h0] using hK)
    exact hh
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  have hτ : 0 < δ/2 := by linarith
  refine ⟨δ/2,hτ,hball ?_,initialMetric_posDef hτ,ray_gradient_before hτ (by norm_num),?_⟩
  · rw [Real.dist_eq,sub_zero,abs_of_pos hτ]
    linarith
  · intro α hα g hg hacc
    exact no_differentiable_armijo_wolfe hτ hα g hg hacc.1 hacc.2

end FivePieceObstruction
end BfgsVerification
