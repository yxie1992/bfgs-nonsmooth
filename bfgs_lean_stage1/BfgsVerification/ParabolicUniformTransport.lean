import BfgsVerification.ParabolicQuantitativeAlgebra
import BfgsVerification.ParabolicEnvelopeScale

/-! Q's uniform compensated logarithm and actual rank-one vector transport.
All constants are chosen before the actual eligible pair. -/
noncomputable section
open scoped BigOperators Topology
open Set Matrix
namespace BfgsVerification
namespace Parabolic
namespace Family
open TransportedCertificate
variable {m : ℕ} (P : Family m)

def calibratedVector (x : Vec 2) : Vec 2 := P.calibratedScale x • radialDirection x

def compensatedMultiplier (x z : Vec 2) : ℝ :=
  P.calibratedScale z * quotientMultiplier x z / P.calibratedScale x

theorem calibrated_vector_transport {x z : Vec 2} (hD : stepDeterminant x z ≠ 0) :
    P.calibratedVector z = P.compensatedMultiplier x z • P.calibratedVector x +
      (P.calibratedScale z * stepMultiplier x z) • pairStep x z := by
  have hs := (P.calibratedScale_pos x).ne'
  rw [calibratedVector, radial_direction_transport hD, smul_add, smul_smul]
  simp only [calibratedVector, compensatedMultiplier, smul_smul]
  congr 1
  congr 1
  field_simp

/-- The calibrated multiplier is positive and has logarithm O(d), uniformly on
both positive-level endpoints in any compact set. No branch selector regularity,
nonzero horizontal step, or iterate/matrix convergence is assumed. -/
theorem exists_uniform_log_transport {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ x ∈ K, ∀ z ∈ K, ∀ g h : Vec 2,
        EligiblePair P.objective c₁ c₂ x z g h → η ≤ P.objective x → η ≤ P.objective z →
        pairDecrease x z g ≤ δ →
        stepDeterminant x z ≠ 0 ∧ 0 < P.compensatedMultiplier x z ∧
          |Real.log (P.compensatedMultiplier x z)| ≤ C * pairDecrease x z g := by
  obtain ⟨R, hR, hrad⟩ := compact_sqNorm_radius hK (0 : Vec 2)
  obtain ⟨CD, δD, hCD, hδD, hden⟩ := P.exists_small_denominator_bounds hK hη hc₁ hc₂
  obtain ⟨CE, hCE, hcal⟩ := P.exists_calibration_deficit_bound
  let A := P.maxQuadratic
  let a := P.minQuadratic
  let B := R*CD/η
  let T := A*R/η
  let S := 2*T^2/a+2*B^2
  let U := A/(2*η*a)+A*R^2/(2*η^2)
  let C := 2*S+B+U+CE/η
  let δ := min δD (min 1 (1/(4*(S+1))))
  have hA : 0 < A := P.maxQuadratic_pos
  have ha : 0 < a := P.minQuadratic_pos
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδD (lt_min zero_lt_one (by positivity))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨C, δ, hC, hδ, hδ1, ?_⟩
  intro x hx z hz g h hp hFx hFz hdδ
  have hxp : 0 < P.objective x := hη.trans_le hFx
  have hzp : 0 < P.objective z := hη.trans_le hFz
  have hd := hp.decrease_pos
  have hd1 := hdδ.trans hδ1
  obtain ⟨_hdD, hhD, hD⟩ := hden x hx z hz g h hp hFx (hdδ.trans (min_le_left _ _))
  obtain ⟨i, hi, hgi⟩ := P.gradient_from_active hp.gradient_x
  obtain ⟨j, hj, hhj⟩ := P.gradient_from_active hp.gradient_z
  have hr (v : Vec 2) (hv : v ∈ K) (l : Fin 2) : |v l| ≤ R :=
    abs_coordinate_of_sqNorm_le hR.le (by simpa only [sub_zero] using hrad v hv) l
  have hzsq : (z 0)^2 ≤ R^2 := by nlinarith [hr z hz 0, sq_abs (z 0), abs_nonneg (z 0)]
  let α := P.a i*x 0/P.objective x
  have hα : |α| ≤ T := by
    dsimp [α, T]
    rw [abs_div, abs_mul, abs_of_pos (P.a_pos i), abs_of_pos hxp]
    exact ratio_bound (mul_nonneg (P.a_pos i).le (abs_nonneg _))
      (mul_le_mul (P.le_maxQuadratic i) (hr x hx 0) (abs_nonneg _) hA.le) hη hFx
  have hcanc := P.quotient_cancellation (z := z) hi hxp.ne' hD
  rw [← hgi] at hcanc
  have hres : |quotientMultiplier x z-1+α*horizontalStep x z| ≤ B*pairDecrease x z g :=
    cancellation_residual_bound hη hFx hD hR.le hCD.le hd.le (hr x hx 1) hhD hcanc
  have hhor := P.eligible_horizontal_sq_le hc₁ hi hp
  have hsq : (quotientMultiplier x z-1)^2 ≤ S*pairDecrease x z g :=
    compensation_square_bound ha hT.le hB.le hd.le hd1 hα hhor hres
  have hdsmall : pairDecrease x z g ≤ 1/(4*(S+1)) :=
    hdδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hclose, hbase⟩ := close_multiplier_of_small_decrease hS hd.le hdsmall hsq
  have hlog := compensation_log_bound hd.le hclose hsq hres
  have hdrop : 0 ≤ P.objective x-P.objective z := (mul_nonneg hc₁ hd.le).trans hp.armijo
  have hexp : |P.a i*(z 0)^2/(2*P.objective z)-P.a i*(x 0)^2/(2*P.objective x)-
      α*horizontalStep x z| ≤ U*pairDecrease x z g := by
    dsimp only [α]
    rw [P.exponent_increment hxp.ne' hzp.ne']
    exact exponent_remainder_bound (P.a_pos i).le (P.le_maxQuadratic i)
      hη hFx hFz ha hd.le hdrop hp.convex_decrease hhor hzsq
  have hcalb : |(P.a j-P.a i)*(z 0)^2/(2*P.objective z)+P.calibration j-P.calibration i| ≤
      (CE/η)*pairDecrease x z g := by
    have hh := ratio_bound (mul_nonneg hCE.le (P.deficit_nonneg i z))
      (mul_le_mul_of_nonneg_left (P.eligible_deficit_le hc₁ hi hp) hCE.le) hη hFz
    exact (hcal i j z hj hzp).trans (hh.trans_eq (by ring))
  have hmul : 0 < P.compensatedMultiplier x z := by
    exact div_pos (mul_pos (P.calibratedScale_pos z) hbase) (P.calibratedScale_pos x)
  refine ⟨hD, hmul, ?_⟩
  have hlogid : Real.log (P.compensatedMultiplier x z) =
      Real.log (quotientMultiplier x z) +
        (P.a j*(z 0)^2/(2*P.objective z)+P.calibration j)-
        (P.a i*(x 0)^2/(2*P.objective x)+P.calibration i) := by
    rw [compensatedMultiplier, Real.log_div
      (mul_ne_zero (P.calibratedScale_pos z).ne' hbase.ne') (P.calibratedScale_pos x).ne',
      Real.log_mul (P.calibratedScale_pos z).ne' hbase.ne',
      P.log_calibratedScale, P.log_calibratedScale,
      P.calibratedExponent_eq_active hj hzp, P.calibratedExponent_eq_active hi hxp]
    ring
  rw [hlogid]
  have hsum := (abs_add
    (Real.log (quotientMultiplier x z)+α*horizontalStep x z)
    ((P.a i*(z 0)^2/(2*P.objective z)-P.a i*(x 0)^2/(2*P.objective x)-α*horizontalStep x z)+
      ((P.a j-P.a i)*(z 0)^2/(2*P.objective z)+P.calibration j-P.calibration i))).trans
    (add_le_add hlog ((abs_add _ _).trans (add_le_add hexp hcalb)))
  convert hsum using 1 <;> dsimp only [C] <;> congr 1 <;> ring

/-- Q.17--Q.18 for the actual calibrated direction, with uniform finite L and
small-decrease threshold chosen before all eligible endpoint pairs. -/
theorem exists_uniform_vector_transport {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ x ∈ K, ∀ z ∈ K, ∀ g h : Vec 2,
        EligiblePair P.objective c₁ c₂ x z g h → η ≤ P.objective x → η ≤ P.objective z →
        pairDecrease x z g ≤ δ → ∃ ell β : ℝ,
          P.calibratedVector z = ell • P.calibratedVector x + β • pairStep x z ∧
          ell^2 ≤ 1+L*pairDecrease x z g := by
  obtain ⟨C, δ, hC, hδ, hδ1, hb⟩ := P.exists_uniform_log_transport hK hη hc₁ hc₂
  refine ⟨Real.exp (2*C)-1, δ, ?_, hδ, hδ1, ?_⟩
  · have hh := Real.exp_le_exp.mpr (show 0 ≤ 2*C by positivity)
    rw [Real.exp_zero] at hh
    linarith
  · intro x hx z hz g h hp hFx hFz hd
    obtain ⟨hD, hmul, hlog⟩ := hb x hx z hz g h hp hFx hFz hd
    exact ⟨P.compensatedMultiplier x z, P.calibratedScale z*stepMultiplier x z,
      P.calibrated_vector_transport hD,
      squared_multiplier_bound hmul ((le_abs_self _).trans hlog) hp.decrease_pos.le (hd.trans hδ1)⟩

end Family
end Parabolic
end BfgsVerification
