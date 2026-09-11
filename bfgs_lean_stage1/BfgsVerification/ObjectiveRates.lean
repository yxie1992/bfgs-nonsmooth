import BfgsVerification.RateBudgets
import BfgsVerification.HomogeneousConsequences
import BfgsVerification.EuclideanEstimates
import BfgsVerification.FrameNorms
import BfgsVerification.CompactConvergence

/-! Module F: actual full-BFGS finite and asymptotic rate consequences.
The scalar budgets and reciprocal growth are discharged from the actual run. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem reciprocal_sum_pos {N : ℕ} (hN : 0 < N) :
    0 < ∑ k ∈ Finset.range N, (R.q k)⁻¹ := by
  exact Finset.sum_pos' (fun k _ => (inv_pos.mpr (R.q_pos k)).le)
    ⟨0, Finset.mem_range.mpr hN, inv_pos.mpr (R.q_pos 0)⟩

/-- Exact finite-horizon objective bound for a linear cumulative budget. -/
theorem reference_linear_budget_sqrt_bound (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (C : ℝ) {N : ℕ} (hN : 0 < N)
    (hC : (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤ C * (N : ℝ)) :
    F (R.x N) - F star ≤ Real.sqrt
      ((R.referenceEnergy star 0 + C * (N : ℝ)) /
        (∑ k ∈ Finset.range N, (R.q k)⁻¹)) := by
  apply RateBudgets.sqrt_bound (R.reciprocal_sum_pos hN)
  exact (R.fixed_reference_energy_bound star hmin N).trans (add_le_add_left hC _)

/-- Linear cumulative corrections give the source little-o square-root rate;
gradients are explicitly bounded here, with compactness discharging this below. -/
theorem value_rate_of_linear_corrections (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (C : ℝ)
    (hC : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤ C * (N : ℝ)) :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * (F (R.x N) - F star))
      atTop (𝓝 0) := by
  have hs := (objectiveLowerBoundGrowth n F R G (F star) hG hg
    (fun k => hmin (R.x k))).2.2.2
  exact RateBudgets.linear_budget_rate (fun k => sub_nonneg.mpr (hmin (R.x k)))
    (R.fixed_reference_energy_bound star hmin) hC hs

/-- Compactness derives all gradient and summability requirements for the rate. -/
theorem compact_value_rate_of_linear_corrections (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (hK : IsCompact R.initialSublevel) (C : ℝ)
    (hC : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤ C * (N : ℝ)) :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * (F (R.x N) - F star))
      atTop (𝓝 0) := by
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  exact R.value_rate_of_linear_corrections star hmin G hG hg C hC

/-- A pointwise uniform correction bound supplies the linear cumulative bound. -/
theorem compact_value_rate_of_bounded_corrections (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (hK : IsCompact R.initialSublevel) (C : ℝ)
    (hC : ∀ k, R.referenceCorrection star k ≤ C) :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * (F (R.x N) - F star))
      atTop (𝓝 0) := by
  apply R.compact_value_rate_of_linear_corrections star hmin hK C
  exact Eventually.of_forall fun N => by
    calc
      (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤
          ∑ _k ∈ Finset.range N, C := Finset.sum_le_sum (fun k _ => hC k)
      _ = C * (N : ℝ) := by simp [mul_comm]

/-- Nonnegative objective values make the actual homogeneous potential
nonnegative, without an iterate or matrix bound. -/
theorem homogeneous_potential_nonneg (hv : ∀ k, 0 ≤ F (R.x k)) (k : ℕ) :
    0 ≤ R.homogeneousPotential k := by
  have hc : 0 ≤ (1 - R.c₁) / R.c₁ :=
    div_nonneg (sub_nonneg.mpr (R.c₁_lt_c₂.trans R.c₂_lt_one).le) R.c₁_pos.le
  exact add_nonneg (R.referenceEnergy_nonneg 0 k) (mul_nonneg hc (hv k))

/-- The exact source weighted-sum bound from the homogeneous potential. -/
theorem homogeneous_weighted_sum_bound (hF : Homogeneous.PositiveDegreeOne F)
    (hv : ∀ k, 0 ≤ F (R.x k)) (N : ℕ) :
    (∑ k ∈ Finset.range N, (F (R.x k)) ^ 2 / R.q k) ≤ R.homogeneousPotential 0 := by
  have hacc : ∀ N, (∑ k ∈ Finset.range N, (F (R.x k)) ^ 2 / R.q k) +
      R.homogeneousPotential N ≤ R.homogeneousPotential 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [R.homogeneous_potential_step hF N]
  linarith [hacc N, R.homogeneous_potential_nonneg hv N]

/-- Monotonicity converts the weighted sum into the exact last-iterate bound. -/
theorem homogeneous_gap_sq_sum_bound (hF : Homogeneous.PositiveDegreeOne F)
    (hv : ∀ k, 0 ≤ F (R.x k)) (N : ℕ) :
    (F (R.x N)) ^ 2 * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      R.homogeneousPotential 0 := by
  apply le_trans _ (R.homogeneous_weighted_sum_bound hF hv N)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkN := R.objective_antitone (Nat.le_of_lt (Finset.mem_range.mp hk))
  have hs : (F (R.x N)) ^ 2 ≤ (F (R.x k)) ^ 2 := by nlinarith [hv N]
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (R.q_pos k).le)

/-- Exact homogeneous finite-horizon bound, with the actual initial potential. -/
theorem homogeneous_sqrt_bound (hF : Homogeneous.PositiveDegreeOne F)
    (hv : ∀ k, 0 ≤ F (R.x k)) {N : ℕ} (hN : 0 < N) :
    F (R.x N) ≤ Real.sqrt (R.homogeneousPotential 0 /
      (∑ k ∈ Finset.range N, (R.q k)⁻¹)) :=
  RateBudgets.sqrt_bound (R.reciprocal_sum_pos hN) (R.homogeneous_gap_sq_sum_bound hF hv N)

/-- Every lower-bounded homogeneous run has F(x_N)=o(1/N). No compactness,
iterate boundedness or matrix convergence is assumed. -/
theorem homogeneous_value_rate (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) :
    Tendsto (fun N : ℕ => (N : ℝ) * F (R.x N)) atTop (𝓝 0) := by
  have hl := R.homogeneous_value_zero_of_lower_bound hF L hL
  have hv : ∀ k, 0 ≤ F (R.x k) := fun k =>
    (R.homogeneous_finite_branch_positive hF 0 hl k).le
  obtain ⟨G, hG, hg⟩ := R.homogeneous_global_gradient_bound hF
  have hs := (objectiveGrowth_of_value_limit R G 0 hG hg hl).2.2.2
  exact RateBudgets.bounded_budget_rate hv (R.homogeneous_gap_sq_sum_bound hF hv) hs

/-- The source finite homogeneous bound for any run whose values are lower
bounded; nonnegative values are derived from the proved homogeneous dichotomy. -/
theorem homogeneous_sqrt_bound_of_lower_bound (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) {N : ℕ} (hN : 0 < N) :
    F (R.x N) ≤ Real.sqrt (R.homogeneousPotential 0 /
      (∑ k ∈ Finset.range N, (R.q k)⁻¹)) := by
  have hl := R.homogeneous_value_zero_of_lower_bound hF L hL
  exact R.homogeneous_sqrt_bound hF
    (fun k => (R.homogeneous_finite_branch_positive hF 0 hl k).le) hN

end AdmissibleBFGSRun
namespace Homogeneous

/-- Coercivity and degree-one homogeneity derive a positive Euclidean radial
lower bound. The constant is not supplied as an extra hypothesis. -/
theorem coercive_euclidean_lower_bound {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hh : PositiveDegreeOne F)
    (hc : Tendsto F (cocompact (Vec n)) atTop) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖euclideanVector x‖ ≤ F x := by
  classical
  have hpos : ∀ x : Vec n, x ≠ 0 → 0 < F x := fun x hx =>
    positive_of_bounded_zero_sublevel hh (bounded_zero_sublevel_of_coercive hc) hx
  have hmin : ∀ x, F 0 ≤ F x := by
    intro x
    by_cases hx : x = 0
    · subst x; exact le_rfl
    · rw [value_zero hh]
      exact (hpos x hx).le
  have hu : ∀ x, F x = F 0 → x = 0 := by
    intro x he
    by_contra hx
    have hp := hpos x hx
    rw [he, value_zero hh] at hp
    exact lt_irrefl 0 hp
  have hK := Localization.sublevel_compact hF 0 hmin hu 1
  obtain ⟨R, hR, hbound⟩ := compact_sqNorm_radius hK 0
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [euclideanVector, value_zero hh]
  have hp := hpos x hx
  let y := (F x)⁻¹ • x
  have hy : F y ≤ 1 := by
    dsimp [y]
    rw [hh _ (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
  have hnormsq : ‖euclideanVector y‖ ^ 2 = sqNorm y :=
    FrameNorms.euclidean_norm_sq (euclideanVector y)
  have hyn : ‖euclideanVector y‖ ≤ R := by
    have hb := hbound y hy
    rw [sub_zero] at hb
    nlinarith [norm_nonneg (euclideanVector y)]
  have hxy : x = (F x) • y := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  have hnx : ‖euclideanVector x‖ ≤ R * F x := by
    conv_lhs => rw [hxy]
    change ‖(F x) • euclideanVector y‖ ≤ R * F x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnx (inv_nonneg.mpr hR.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul] using hm

end Homogeneous
namespace AdmissibleBFGSRun

/-- Coercive homogeneous objectives also have Euclidean iterate norm=o(1/N),
with both the gradient and positive radial bounds derived from the objective. -/
theorem homogeneous_coercive_norm_rate {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (hF : Homogeneous.PositiveDegreeOne F)
    (hc : Tendsto F (cocompact (Vec n)) atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖euclideanVector (R.x N)‖) atTop (𝓝 0) := by
  obtain ⟨μ, hμ, hl⟩ := Homogeneous.coercive_euclidean_lower_bound R.convex hF hc
  have hv : ∀ k, 0 ≤ F (R.x k) := fun k =>
    (mul_nonneg hμ.le (norm_nonneg _)).trans (hl (R.x k))
  have hr := (R.homogeneous_value_rate hF 0 hv).div_const μ
  apply squeeze_zero (fun N => mul_nonneg (Nat.cast_nonneg N) (norm_nonneg _)) _
    (by simpa using hr)
  intro N
  apply (le_div_iff₀ hμ).2
  have hm := mul_le_mul_of_nonneg_left (hl (R.x N)) (Nat.cast_nonneg N)
  nlinarith

end AdmissibleBFGSRun
end BfgsVerification
