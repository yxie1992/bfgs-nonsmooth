import BfgsVerification.BFGSGradientScaling
import BfgsVerification.RadialCertificate

/-! Positive affine changes of objective values preserve actual full BFGS.
The matrices are divided by the positive value scale. No trajectory or
matrix convergence is assumed, and all accepted lengths are unchanged. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter

namespace BfgsVerification.ObjectiveValueScale

def objective {n : ℕ} (a b : ℝ) (F : Vec n → ℝ) : Vec n → ℝ :=
  fun x => a * F x + b

theorem convex {n : ℕ} (a b : ℝ) (ha : 0 ≤ a) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) : ConvexOn ℝ univ (objective a b F) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy t u ht hu htu
  have h := mul_le_mul_of_nonneg_left (hF.2 hx hy ht hu htu) ha
  change a * F (t • x + u • y) + b ≤ t * (a * F x + b) + u * (a * F y + b)
  calc
    _ ≤ a * (t * F x + u * F y) + b := add_le_add_right h b
    _ = a * (t * F x + u * F y) + (t + u) * b := by rw [htu, one_mul]
    _ = _ := by ring

theorem gradientFunctional_scale {n : ℕ} (a : ℝ) (g : Vec n) :
    gradientFunctional (a • g) = a • gradientFunctional g := by
  ext v
  simp only [gradientFunctional_apply, ContinuousLinearMap.smul_apply,
    PlanarUpdate.dot_scale_left, smul_eq_mul]

theorem hasGradient {n : ℕ} (a b : ℝ) {F : Vec n → ℝ} {x g : Vec n}
    (h : HasFDerivAt F (gradientFunctional g) x) :
    HasFDerivAt (objective a b F) (gradientFunctional (a • g)) x := by
  rw [gradientFunctional_scale]
  exact (h.const_smul a).add_const b

theorem step {n : ℕ} (a : ℝ) (ha : a ≠ 0) (H : Mat n) (g : Vec n) (α : ℝ) :
    bfgsStep (a⁻¹ • H) (a • g) α = bfgsStep H g α := by
  rw [bfgsStep_scale_matrix, bfgsStep_scale_gradient, smul_smul,
    inv_mul_cancel₀ ha, one_smul]

theorem update {n : ℕ} (a : ℝ) (ha : a ≠ 0) (H : Mat n) (s y : Vec n) :
    inverseBFGS (a⁻¹ • H) s (a • y) = a⁻¹ • inverseBFGS H s y := by
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul,
    inverseBFGS_scale_secant_pair H s y ha] using
    (inverseBFGS_scale H (a • s) (a • y) (inv_ne_zero ha))

theorem posDef {n : ℕ} {H : Mat n} (hH : H.PosDef) {a : ℝ} (ha : 0 < a) :
    (a • H).PosDef := by
  constructor
  · change (a • H)ᴴ = a • H
    rw [Matrix.conjTranspose_smul, star_trivial, hH.1.eq]
  · intro v hv
    simpa only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul,
      star_trivial] using mul_pos ha (hH.2 v hv)

theorem energy {n : ℕ} (a : ℝ) (ha : a ≠ 0) (H : Mat n) (g : Vec n) :
    metricEnergy (a⁻¹ • H) (a • g) = a * metricEnergy H g := by
  simp only [metricEnergy, Matrix.smul_mulVec_assoc, Matrix.mulVec_smul,
    smul_smul, inv_mul_cancel₀ ha, mul_inv_cancel₀ ha, one_smul,
    PlanarUpdate.dot_scale_left]

def run {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) : AdmissibleBFGSRun n (objective a b F) where
  convex := convex a b ha.le R.convex
  x := R.x
  H k := a⁻¹ • R.H k
  g k := a • R.g k
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := posDef R.initial_posDef (inv_pos.mpr ha)
  alpha_pos := R.alpha_pos
  gradient_nonzero k := by
    exact smul_ne_zero ha.ne' (R.gradient_nonzero k)
  hasGradient k := hasGradient a b (R.hasGradient k)
  step k := by rw [step a ha.ne']; exact R.step k
  update k := by
    rw [← smul_sub, step a ha.ne', update a ha.ne', R.update]
  armijo k := by
    rw [step a ha.ne', PlanarUpdate.dot_scale_left]
    have h := mul_le_mul_of_nonneg_left (R.armijo k) ha.le
    dsimp only [objective]
    nlinarith
  weak_wolfe k := by
    rw [step a ha.ne', PlanarUpdate.dot_scale_left, PlanarUpdate.dot_scale_left]
    have h := mul_le_mul_of_nonneg_left (R.weak_wolfe k) ha.le
    nlinarith

@[simp] theorem run_x {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run a b ha R).x k = R.x k := rfl
@[simp] theorem run_H {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run a b ha R).H k = a⁻¹ • R.H k := rfl
@[simp] theorem run_g {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run a b ha R).g k = a • R.g k := rfl
@[simp] theorem run_alpha {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run a b ha R).α k = R.α k := rfl
@[simp] theorem run_c1 {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) : (run a b ha R).c₁ = R.c₁ := rfl
@[simp] theorem run_c2 {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) : (run a b ha R).c₂ = R.c₂ := rfl
@[simp] theorem run_value {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    objective a b F ((run a b ha R).x k) = a * F (R.x k) + b := rfl

@[simp] theorem run_q {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run a b ha R).q k = a * R.q k :=
  energy a ha.ne' (R.H k) (R.g k)

@[simp] theorem run_d {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run a b ha R).d k = a * R.d k := by
  simp only [AdmissibleBFGSRun.d, run_alpha, run_q]
  ring

@[simp] theorem run_displacement {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    (run a b ha R).displacement k = R.displacement k := step a ha.ne' _ _ _

@[simp] theorem run_gradientChange {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    (run a b ha R).gradientChange k = a • R.gradientChange k := (smul_sub a _ _).symm

@[simp] theorem run_curvature {n : ℕ} {F : Vec n → ℝ} (a b : ℝ) (ha : 0 < a)
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    (run a b ha R).curvature k = a * R.curvature k := by
  simp only [AdmissibleBFGSRun.curvature, run_gradientChange, run_displacement,
    PlanarUpdate.dot_scale_left]

theorem optimizerIntercept {n : ℕ} (a b : ℝ) (F : Vec n → ℝ) (star x g : Vec n) :
    RadialCertificate.optimizerIntercept (objective a b F) star x (a • g) =
      a * RadialCertificate.optimizerIntercept F star x g := by
  simp only [RadialCertificate.optimizerIntercept, objective, PlanarUpdate.dot_scale_left]
  ring

theorem secantCurvature {n : ℕ} (a : ℝ) (x z g h : Vec n) :
    RadialCertificate.secantCurvature x z (a • g) (a • h) =
      a * RadialCertificate.secantCurvature x z g h := by
  simp only [RadialCertificate.secantCurvature, ← smul_sub, PlanarUpdate.dot_scale_left]

end BfgsVerification.ObjectiveValueScale
