import BfgsVerification.ObjectiveEnergy
import BfgsVerification.RunShift

/-! Finite convex homogeneous objectives and their global supporting vectors.
Positive homogeneity is required only for nonnegative scalar factors. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification
namespace Homogeneous

/-- Positive degree-one homogeneity for an everywhere real-valued objective. -/
def PositiveDegreeOne {n : ℕ} (F : Vec n → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t * F x

/-- The ordinary global convex supporting-vector inequality. -/
def Supports {n : ℕ} (F : Vec n → ℝ) (x g : Vec n) : Prop :=
  ∀ z, dot g (z - x) ≤ F z - F x

theorem value_zero {n : ℕ} {F : Vec n → ℝ} (hF : PositiveDegreeOne F) : F 0 = 0 := by
  simpa using hF 0 le_rfl 0

/-- Euler's identity follows from supporting inequalities at zero and twice x. -/
theorem supporting_euler {n : ℕ} {F : Vec n → ℝ} (hF : PositiveDegreeOne F)
    {x g : Vec n} (hg : Supports F x g) : dot g x = F x := by
  have hzero := hg 0
  have htwo := hg ((2 : ℝ) • x)
  rw [value_zero hF] at hzero
  have hneg : dot g (0 - x) = -dot g x := by
    change g ⬝ᵥ (0 - x) = -(g ⬝ᵥ x)
    simp only [zero_sub, dotProduct_neg]
  have hsub : (2 : ℝ) • x - x = x := by module
  rw [hF 2 (by norm_num) x, hsub] at htwo
  rw [hneg] at hzero
  linarith

/-- Every support plane of a homogeneous convex objective passes through zero. -/
theorem supporting_linear_le {n : ℕ} {F : Vec n → ℝ} (hF : PositiveDegreeOne F)
    {x g : Vec n} (hg : Supports F x g) (z : Vec n) : dot g z ≤ F z := by
  have h := hg z
  have he := supporting_euler hF hg
  have hd : dot g (z - x) = dot g z - dot g x := dotProduct_sub _ _ _
  rw [hd, he] at h
  linarith

theorem supports_at_zero {n : ℕ} {F : Vec n → ℝ} (hF : PositiveDegreeOne F)
    {x g : Vec n} (hg : Supports F x g) : Supports F 0 g := by
  intro z
  simpa only [sub_zero, value_zero hF] using supporting_linear_le hF hg z

/-- All supports are globally bounded, using only the compact singleton {0}.
No assumption is made on accepted iterates or on a finite gradient alphabet. -/
theorem global_supporting_bound {n : ℕ} {F : Vec n → ℝ}
    (hconvex : ConvexOn ℝ Set.univ F) (hF : PositiveDegreeOne F) :
    ∃ G : ℝ, 0 < G ∧ ∀ x g, Supports F x g → sqNorm g ≤ G ^ 2 := by
  obtain ⟨G, hG, hbound⟩ := convex_supporting_bound_on_compact hconvex
    (isCompact_singleton (x := (0 : Vec n)))
  exact ⟨G, hG, fun x g hg => hbound 0 (Set.mem_singleton _) g (supports_at_zero hF hg)⟩

end Homogeneous

namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem homogeneous_euler (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    dot (R.g k) (R.x k) = F (R.x k) :=
  Homogeneous.supporting_euler hF (convex_supporting_inequality R.convex (R.hasGradient k))

theorem homogeneous_support (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) (z : Vec n) :
    dot (R.g k) z ≤ F z :=
  Homogeneous.supporting_linear_le hF (convex_supporting_inequality R.convex (R.hasGradient k)) z

theorem homogeneous_global_gradient_bound (hF : Homogeneous.PositiveDegreeOne F) :
    ∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (R.g k) ≤ G ^ 2 := by
  obtain ⟨G, hG, hbound⟩ := Homogeneous.global_supporting_bound R.convex hF
  exact ⟨G, hG, fun k => hbound (R.x k) (R.g k)
    (convex_supporting_inequality R.convex (R.hasGradient k))⟩

theorem homogeneous_new_pairing (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    dot (R.gradientChange k) (R.x (k + 1)) =
      R.d k - (F (R.x k) - F (R.x (k + 1))) := by
  have hstep : dot (R.g k) (R.x (k + 1)) = F (R.x k) - R.d k := by
    rw [R.step]
    change R.g k ⬝ᵥ (R.x k + bfgsStep (R.H k) (R.g k) (R.α k)) = _
    rw [dotProduct_add]
    change dot (R.g k) (R.x k) + dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) = _
    rw [R.homogeneous_euler hF k, R.dot_step_eq_neg_d]
    ring
  change (R.g (k + 1) - R.g k) ⬝ᵥ R.x (k + 1) = _
  rw [sub_dotProduct]
  change dot (R.g (k + 1)) (R.x (k + 1)) - dot (R.g k) (R.x (k + 1)) = _
  rw [R.homogeneous_euler hF (k + 1), hstep]
  ring

theorem homogeneous_new_pairing_nonneg (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    0 ≤ dot (R.gradientChange k) (R.x (k + 1)) := by
  rw [R.homogeneous_new_pairing hF]
  exact sub_nonneg.mpr (R.convexity_decrease_upper k)

theorem homogeneous_old_pairing_nonpos (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    dot (R.gradientChange k) (R.x k) ≤ 0 := by
  change (R.g (k + 1) - R.g k) ⬝ᵥ R.x k ≤ 0
  rw [sub_dotProduct]
  change dot (R.g (k + 1)) (R.x k) - dot (R.g k) (R.x k) ≤ 0
  rw [R.homogeneous_euler hF k]
  exact sub_nonpos.mpr (R.homogeneous_support hF (k + 1) (R.x k))

theorem homogeneous_pairing_le_curvature (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    dot (R.gradientChange k) (R.x (k + 1)) ≤ R.curvature k := by
  have h : R.curvature k = dot (R.gradientChange k) (R.x (k + 1)) -
      dot (R.gradientChange k) (R.x k) := by
    have hx : R.displacement k = R.x (k + 1) - R.x k := by rw [R.step]; simp [displacement]
    unfold curvature
    rw [hx]
    exact dotProduct_sub _ _ _
  rw [h]
  linarith [R.homogeneous_old_pairing_nonpos hF k]

/-- The homogeneous correction is bounded by the actual new-point pairing. -/
theorem homogeneous_referenceCorrection_le_pairing (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    R.referenceCorrection 0 k ≤ dot (R.gradientChange k) (R.x (k + 1)) := by
  have hnonneg := R.homogeneous_new_pairing_nonneg hF k
  have hle := R.homogeneous_pairing_le_curvature hF k
  unfold referenceCorrection
  rw [sub_zero]
  apply (div_le_iff₀ (R.curvature_pos k)).2
  change _ ≤ _ * R.curvature k
  nlinarith

/-- Source H.5's sharper correction budget in units of actual objective decrease. -/
theorem homogeneous_referenceCorrection_le_drop (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    R.referenceCorrection 0 k ≤ ((1 - R.c₁) / R.c₁) *
      (F (R.x k) - F (R.x (k + 1))) := by
  apply (R.homogeneous_referenceCorrection_le_pairing hF k).trans
  rw [R.homogeneous_new_pairing hF]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ R.c₁_pos).2
  nlinarith [R.armijo_decrease k]

theorem homogeneous_referenceCorrection_le_d (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    R.referenceCorrection 0 k ≤ R.d k := by
  have hnonneg := R.homogeneous_new_pairing_nonneg hF k
  have hle := R.homogeneous_pairing_le_curvature hF k
  have hbound : R.referenceCorrection 0 k ≤ dot (R.gradientChange k) (R.x (k + 1)) := by
    unfold referenceCorrection
    rw [sub_zero]
    apply (div_le_iff₀ (R.curvature_pos k)).2
    change _ ≤ _ * R.curvature k
    nlinarith
  apply hbound.trans
  rw [R.homogeneous_new_pairing hF]
  have hdec := (R.objective_strict_decrease k).le
  linarith

theorem homogeneous_energy_identity (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    R.referenceEnergy 0 (k + 1) = R.referenceEnergy 0 k -
      (F (R.x k)) ^ 2 / R.q k + R.referenceCorrection 0 k := by
  have he := R.fixed_reference_energy 0 k
  simpa only [referencePairing, sub_zero, R.homogeneous_euler hF k] using he

/-- The exact homogeneous potential used in source H.5.2. -/
def homogeneousPotential (k : ℕ) : ℝ :=
  R.referenceEnergy 0 k + ((1 - R.c₁) / R.c₁) * F (R.x k)

/-- The source potential decreases by the actual squared-value energy. -/
theorem homogeneous_potential_step (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    R.homogeneousPotential (k + 1) ≤ R.homogeneousPotential k - (F (R.x k)) ^ 2 / R.q k := by
  unfold homogeneousPotential
  rw [R.homogeneous_energy_identity hF k]
  nlinarith [R.homogeneous_referenceCorrection_le_drop hF k]

end AdmissibleBFGSRun
end BfgsVerification
