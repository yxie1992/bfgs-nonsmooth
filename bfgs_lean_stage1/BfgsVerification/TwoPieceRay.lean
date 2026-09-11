import BfgsVerification.TwoPieceTermination
import BfgsVerification.FiniteRayLineSearch

noncomputable section
open Set Filter
open scoped Topology
namespace BfgsVerification.TwoPieceBudget

theorem differentiableAt_of_ne {x : Vec 2} (hx : x 0 ≠ 0) :
    DifferentiableAt ℝ objective x := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := x)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := x)
  rcases lt_or_gt_of_ne hx with hn | hp
  · exact ((h0.abs_of_neg hn).add h1).differentiableAt
  · exact ((h0.abs_of_pos hp).add h1).differentiableAt

theorem finite_bad_ray (x p : Vec 2) (hx : x 0 ≠ 0) :
    {t : ℝ | 0 < t ∧ ¬DifferentiableAt ℝ objective (x+t • p)}.Finite := by
  have hz (t : ℝ) (ht : ¬DifferentiableAt ℝ objective (x+t • p)) : x 0+t*p 0=0 := by
    by_contra hn
    exact ht (differentiableAt_of_ne hn)
  by_cases hp : p 0=0
  · apply (finite_empty : (∅ : Set ℝ).Finite).subset
    intro t ht
    have h := hz t ht.2
    simp only [hp,mul_zero,add_zero] at h
    exact (hx h).elim
  · apply (finite_singleton (-x 0/p 0)).subset
    intro t ht
    apply mem_singleton_iff.mpr
    apply (eq_div_iff hp).mpr
    linarith [hz t ht.2]

theorem ray_lower_bound (x p : Vec 2) (hs : 0 ≤ |p 0|+p 1) (t : ℝ) (ht : 0 ≤ t) :
    x 1-|x 0| ≤ objective (x+t • p) := by
  have hh : t*|p 0| ≤ |x 0+t*p 0|+|x 0| := by
    have ha := abs_add_le (x 0+t*p 0) (-x 0)
    have he : x 0+t*p 0+-x 0=t*p 0 := by ring
    rw [he,abs_neg,abs_mul,abs_of_nonneg ht] at ha
    exact ha
  have hm := mul_nonneg ht hs
  simp only [objective,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith [hh,hm]

theorem ray_upper_bound (x p : Vec 2) (t : ℝ) (ht : 0 ≤ t) :
    objective (x+t • p) ≤ objective x+t*(|p 0|+p 1) := by
  have hh := abs_add_le (x 0) (t*p 0)
  rw [abs_mul,abs_of_nonneg ht] at hh
  simp only [objective,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith [hh]

theorem terminal_direction_negative {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (S : State)
    (hterm : ¬∃ T : State, Step c₁ c₂ S T) :
    |(bfgsStep S.H S.g 1) 0|+(bfgsStep S.H S.g 1) 1 < 0 := by
  by_contra hn
  have hn' := le_of_not_gt hn
  have hx : S.x 0 ≠ 0 := by
    intro he
    have hp := (actual_gradient_shape S.derivative).2.2.1
    simp [he] at hp
  have hL (t : ℝ) (ht : 0 ≤ t) :
      S.x 1-|S.x 0| ≤ objective (S.x+bfgsStep S.H S.g t) := by
    rw [FiniteRayLineSearch.bfgsStep_scaling]
    exact ray_lower_bound S.x (bfgsStep S.H S.g 1) hn' t ht
  have hb : {t : ℝ | 0 < t ∧ ¬DifferentiableAt ℝ objective
      (S.x+bfgsStep S.H S.g t)}.Finite := by
    simpa only [bfgsStep,smul_smul,mul_neg,mul_one] using finite_bad_ray S.x (bfgsStep S.H S.g 1) hx
  obtain ⟨α,g,hα,hg,ha,hw⟩ := FiniteRayLineSearch.fullBFGS_step_exists objective_convex
    S.x S.g S.H S.positive S.gradient_nonzero S.derivative hc₁ hc hc₂ _ hL hb
  let T : State := {
    x := S.x+bfgsStep S.H S.g α
    H := inverseBFGS S.H (bfgsStep S.H S.g α) (g-S.g)
    g := g
    positive := inverseBFGS_posDef S.positive _ _
      (curvature_pos_of_weakWolfe S.positive S.gradient_nonzero g hα hc₂ hw.le)
    derivative := hg }
  exact hterm ⟨T,α,hα,rfl,rfl,ha.le,hw.le⟩

theorem terminal_direction_unbounded {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (S : State)
    (hterm : ¬∃ T : State, Step c₁ c₂ S T) :
    Tendsto (fun t : ℝ => objective (S.x+bfgsStep S.H S.g t)) atTop atBot := by
  let p := bfgsStep S.H S.g 1
  have hn : |p 0|+p 1 < 0 := terminal_direction_negative hc₁ hc hc₂ S hterm
  have hl : Tendsto (fun t : ℝ => objective S.x+t*(|p 0|+p 1)) atTop atBot := by
    have hm := tendsto_id.atTop_mul_const_of_neg hn
    exact tendsto_atBot_add_const_left atTop (objective S.x) hm
  apply tendsto_atBot_mono' atTop _ hl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [FiniteRayLineSearch.bfgsStep_scaling]
  exact ray_upper_bound S.x p t ht

end BfgsVerification.TwoPieceBudget
