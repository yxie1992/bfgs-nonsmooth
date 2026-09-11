import BfgsVerification.TransportedCertificateAlgebra
import BfgsVerification.RunShift
import BfgsVerification.ResidualBudget

/-! Objective-pair certificates instantiated at actual full-BFGS accepted iterates.
Eligibility, PSD Hessians, annihilation, and all trace recurrences are derived. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification.AdmissibleBFGSRun

open TransportedCertificate
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem accepted_pair_step (k : ℕ) : pairStep (R.x k) (R.x (k + 1)) = R.displacement k := by
  rw [pairStep, R.step]
  exact add_sub_cancel_left _ _

theorem accepted_pair_decrease (k : ℕ) :
    pairDecrease (R.x k) (R.x (k + 1)) (R.g k) = R.d k := by
  rw [pairDecrease, R.accepted_pair_step, displacement, R.dot_step_eq_neg_d, neg_neg]

theorem accepted_pair_curvature (k : ℕ) :
    pairCurvature (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1)) = R.curvature k := by
  rw [pairCurvature, R.accepted_pair_step]
  rfl

/-- Every actual accepted pair satisfies exactly the objective-only eligibility condition. -/
theorem accepted_pair_eligible (k : ℕ) :
    EligiblePair F R.c₁ R.c₂ (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1)) where
  gradient_x := R.hasGradient k
  gradient_z := R.hasGradient (k + 1)
  decrease_pos := by rw [R.accepted_pair_decrease]; exact R.d_pos k
  armijo := by rw [R.accepted_pair_decrease]; exact R.armijo_decrease k
  convex_decrease := by rw [R.accepted_pair_decrease]; exact R.convexity_decrease_upper k
  curvature := by rw [R.accepted_pair_decrease, R.accepted_pair_curvature]; exact R.curvature_lower_bound k

/-- Eligibility of accepted pairs includes a nonzero actual displacement. -/
theorem accepted_displacement_ne_zero (k : ℕ) : R.displacement k ≠ 0 := by
  intro hz
  have h := R.dot_step_eq_neg_d k
  change dot (R.g k) (R.displacement k) = -R.d k at h
  rw [hz] at h
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  linarith [R.d_pos k]

/-- The source's energy against a finite certificate field. -/
def certificateEnergy (W : Vec n → Mat n) (k : ℕ) : ℝ :=
  (R.hessian k * W (R.x k)).trace

theorem certificateEnergy_nonneg {K : Set (Vec n)} {fstar η : ℝ}
    (C : BandCertificate F K fstar R.c₁ R.c₂ η) (k : ℕ)
    (hx : R.x k ∈ positiveBand F K fstar η) : 0 ≤ R.certificateEnergy C.W k :=
  trace_mul_nonneg (R.hessian_posDef k).posSemidef
    (C.positive_semidefinite _ hx (R.hasGradient k).differentiableAt)

/-- T.6 is proved for actual BFGS matrices from a certificate's eligible-pair bounds. -/
theorem certificate_trace_step {K : Set (Vec n)} {fstar η : ℝ}
    (C : BandCertificate F K fstar R.c₁ R.c₂ η) (k : ℕ)
    (hx : R.x k ∈ positiveBand F K fstar η)
    (hz : R.x (k + 1) ∈ positiveBand F K fstar η)
    (hsmall : R.d k ≤ C.δ) :
    R.certificateEnergy C.W (k + 1) ≤
      (1 + C.L * R.d k) * (R.certificateEnergy C.W k - C.m / R.q k) + C.C := by
  let M := R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)
  have hpair := R.accepted_pair_eligible k
  have hsmall' : pairDecrease (R.x k) (R.x (k + 1)) (R.g k) ≤ C.δ := by
    rwa [R.accepted_pair_decrease]
  have hT := C.transport _ _ _ _ hx hz hpair hsmall'
  rw [R.accepted_pair_decrease, R.accepted_pair_step] at hT
  have htrace := projected_transport_trace M (R.annihilated_hessian_posSemidef k)
    (R.displacement k) (R.annihilated_hessian_mul_displacement k)
    (C.W (R.x k)) (C.W (R.x (k + 1))) (1 + C.L * R.d k) hT
  have hS := C.secant _ _ _ _ hx hz hpair hsmall'
  rw [R.accepted_pair_curvature] at hS
  have hcorr : metricEnergy (C.W (R.x (k + 1))) (R.gradientChange k) / R.curvature k ≤ C.C :=
    (div_le_iff₀ (R.curvature_pos k)).mpr hS
  have hV := C.visibility _ hx (R.g k) (R.hasGradient k)
  have hbase : (M * C.W (R.x k)).trace ≤ R.certificateEnergy C.W k - C.m / R.q k := by
    dsimp only [M, certificateEnergy]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, trace_outer_mul]
    have hdiv := div_le_div_of_nonneg_right hV (R.q_pos k).le
    simp only [smul_eq_mul, div_eq_mul_inv] at hdiv ⊢
    linarith
  have hmult : 0 ≤ 1 + C.L * R.d k := add_nonneg zero_le_one (mul_nonneg C.L_nonneg (R.d_pos k).le)
  have hbound := htrace.trans (mul_le_mul_of_nonneg_left hbase hmult)
  have he : R.certificateEnergy C.W (k + 1) =
      (M * C.W (R.x (k + 1))).trace +
        metricEnergy (C.W (R.x (k + 1))) (R.gradientChange k) / R.curvature k := by
    unfold certificateEnergy
    rw [R.hessian_update, Matrix.add_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_smul, trace_outer_mul]
    simp only [M, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he]
  linarith

/-- A fixed positive-band certificate cannot contain a full infinite run of
small eligible steps. Its trace recurrence is derived above, never assumed. -/
theorem band_certificate_incompatible {K : Set (Vec n)} {fstar η : ℝ}
    (C : BandCertificate F K fstar R.c₁ R.c₂ η)
    (hx : ∀ k, R.x k ∈ positiveBand F K fstar η)
    (hsmall : ∀ k, R.d k ≤ C.δ)
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hs : Summable R.d) : False := by
  let C₀ := max C.C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hrec : ∀ k, R.certificateEnergy C.W (k + 1) ≤
      (1 + C.L * R.d k) * (R.certificateEnergy C.W k - C.m / R.q k) + C₀ * (k + 1) := by
    intro k
    have hstep := R.certificate_trace_step C k (hx k) (hx (k + 1)) (hsmall k)
    have hcc : C.C ≤ C₀ := le_max_left _ _
    have hmul : 0 ≤ C₀ * (k : ℝ) := mul_nonneg hC₀ (Nat.cast_nonneg k)
    linarith
  have hsuper := superquadraticReciprocalGrowth n R.toFullBFGSRun G (1 - R.c₂)
    hG R.wolfe_constant_pos hg R.beta_lower_bound hs
  exact ResidualBudget.residual_recurrence_incompatible
    (fun k => R.certificateEnergy_nonneg C k (hx k)) R.q_pos
    (fun k => mul_nonneg C.L_nonneg (R.d_pos k).le) (hs.mul_left C.L)
    C.m_pos hC₀ hrec hsuper

end BfgsVerification.AdmissibleBFGSRun
