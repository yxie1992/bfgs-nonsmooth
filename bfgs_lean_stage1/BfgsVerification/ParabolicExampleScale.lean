import BfgsVerification.ParabolicExampleContrast
import Mathlib.Topology.Piecewise
import BfgsVerification.TransportedNormalization

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace Parabolic
namespace Example

theorem objective_middle_closed {x : Vec 2}
    (hlo : -(x 0)^2 ≤ x 1) (hhi : x 1 ≤ 2*(x 0)^2) :
    objective x = 3*(x 0)^2 := by
  rw [objective_eq_max]
  apply le_antisymm
  · apply max_le
    · apply max_le <;> linarith
    · linarith
  · exact le_max_of_le_left (le_max_right _ _)

theorem sourceScale_continuousOn : ContinuousOn sourceScale {x | 0 < objective x} := by
  have hF : Continuous objective := family.objective_continuous
  have hq : Continuous (fun x : Vec 2 => (x 0)^2) := by fun_prop
  have hn : Continuous (fun x : Vec 2 => -(x 0)^2) := hq.neg
  have htwo : Continuous (fun x : Vec 2 => 2*(x 0)^2) := by fun_prop
  have hratio : ContinuousOn (fun x : Vec 2 => (x 0)^2/objective x) {x | 0 < objective x} :=
    hq.continuousOn.div hF.continuousOn (fun x hx => hx.ne')
  have hlower : ContinuousOn (fun x : Vec 2 => Real.exp ((x 0)^2/objective x-1/3))
      {x | 0 < objective x} := Real.continuous_exp.comp_continuousOn (hratio.sub continuousOn_const)
  have hupper : ContinuousOn (fun x : Vec 2 => Real.exp ((x 0)^2/(2*objective x)-1/6))
      {x | 0 < objective x} := by
    have hr2 : ContinuousOn (fun x : Vec 2 => (x 0)^2/(2*objective x)) {x | 0 < objective x} := by
      convert hratio.div_const 2 using 1
      funext x
      ring
    exact Real.continuous_exp.comp_continuousOn (hr2.sub continuousOn_const)
  have hinner : ContinuousOn (fun x : Vec 2 => if 2*(x 0)^2 < x 1 then
      Real.exp ((x 0)^2/(2*objective x)-1/6) else 1) {x | 0 < objective x} := by
    apply ContinuousOn.if _ (hupper.mono inter_subset_left) (continuousOn_const.mono inter_subset_left)
    intro x hx
    have he : 2*(x 0)^2 = x 1 := frontier_lt_subset_eq htwo (continuous_apply 1) hx.2
    have hv : objective x = 3*(x 0)^2 := objective_middle_closed
      (by nlinarith [sq_nonneg (x 0)]) he.symm.le
    have hf : objective x ≠ 0 := hx.1.ne'
    have hzero : (x 0)^2/(2*objective x)-1/6 = 0 := by
      field_simp [hf]
      nlinarith
    rw [hzero, Real.exp_zero]
  unfold sourceScale
  apply ContinuousOn.if _ (hlower.mono inter_subset_left) (hinner.mono inter_subset_left)
  intro x hx
  have he : x 1 = -(x 0)^2 := frontier_lt_subset_eq (continuous_apply 1) hn hx.2
  have hv : objective x = 3*(x 0)^2 := objective_middle_closed he.symm.le
    (by nlinarith [sq_nonneg (x 0)])
  have hf : objective x ≠ 0 := hx.1.ne'
  have hzero : (x 0)^2/objective x-1/3 = 0 := by
    field_simp [hf]
    nlinarith
  have hnot : ¬ 2*(x 0)^2 < x 1 := by nlinarith [sq_nonneg (x 0)]
  rw [if_neg hnot, hzero, Real.exp_zero]

theorem calibration_differences :
    family.calibration 0 = family.calibration 1+1/3 ∧
      family.calibration 2 = family.calibration 1+1/6 := by
  have hvp : objective ![(1 : ℝ), 2] = 3 := by
    rw [objective_middle_closed (by norm_num) (by norm_num)]
    norm_num
  have hvn : objective ![(1 : ℝ), -1] = 3 := by
    rw [objective_middle_closed (by norm_num) (by norm_num)]
    norm_num
  have hp0 : family.Active 0 ![(1 : ℝ), 2] := by
    change objective ![(1 : ℝ), 2] = _
    rw [hvp]
    norm_num [Family.branch, family]
  have hp1 : family.Active 1 ![(1 : ℝ), 2] := by
    change objective ![(1 : ℝ), 2] = _
    rw [hvp]
    norm_num [Family.branch, family]
  have hn1 : family.Active 1 ![(1 : ℝ), -1] := by
    change objective ![(1 : ℝ), -1] = _
    rw [hvn]
    norm_num [Family.branch, family]
  have hn2 : family.Active 2 ![(1 : ℝ), -1] := by
    change objective ![(1 : ℝ), -1] = _
    rw [hvn]
    change 3 = 2*1^2+(-1)*(-1)
    norm_num
  have he1 := family.calibration_interface_identity 2 hp0 hp1
  have he2 := family.calibration_interface_identity (-1) hn1 hn2
  change family.calibration 1-family.calibration 0 = -(3-1)/(2*objective ![1,2]) at he1
  change family.calibration 2-family.calibration 1 = -(2-3)/(2*objective ![1,-1]) at he2
  rw [hvp] at he1
  rw [hvn] at he2
  constructor <;> linarith

/-- The global multiplicative normalization identifying the explicitly
printed scale with the selector-free finite-envelope construction. -/
def sourceNormalization : ℝ := Real.exp (-(family.calibration 1+1/2))

theorem sourceNormalization_pos : 0 < sourceNormalization := Real.exp_pos _

theorem sourceScale_eq_normalized {x : Vec 2} (hx : 0 < objective x) :
    sourceScale x = sourceNormalization*family.calibratedScale x := by
  unfold sourceScale
  split_ifs with hlo hhi
  · have hactive : family.Active 2 x := by
      change objective x = family.branch 2 x
      rw [objective_eq_max]
      have hb : family.branch 2 x = 2*(x 0)^2-x 1 := by
        change 2*(x 0)^2+(-1)*x 1 = _
        ring
      rw [hb]
      apply max_eq_right
      apply max_le <;> nlinarith [sq_nonneg (x 0)]
    rw [family.calibratedScale_eq_active hactive hx, sourceNormalization, ← Real.exp_add]
    congr 1
    change (x 0)^2/objective x-1/3 =
      -(family.calibration 1+1/2)+(2*(x 0)^2/(2*objective x)+family.calibration 2)
    rw [calibration_differences.2]
    ring
  · have hactive : family.Active 0 x := objective_upper_region hhi
    rw [family.calibratedScale_eq_active hactive hx, sourceNormalization, ← Real.exp_add]
    congr 1
    change (x 0)^2/(2*objective x)-1/6 =
      -(family.calibration 1+1/2)+(1*(x 0)^2/(2*objective x)+family.calibration 0)
    rw [calibration_differences.1]
    ring
  · have hv : objective x = 3*(x 0)^2 := objective_middle_closed (le_of_not_gt hlo) (le_of_not_gt hhi)
    have hactive : family.Active 1 x := by
      change objective x = family.branch 1 x
      simpa [Family.branch, family] using hv
    rw [family.calibratedScale_eq_active hactive hx, sourceNormalization, ← Real.exp_add]
    have he : -(family.calibration 1+1/2)+(family.a 1*(x 0)^2/(2*family.objective x)+family.calibration 1) = 0 := by
      change -(family.calibration 1+1/2)+(3*(x 0)^2/(2*objective x)+family.calibration 1) = 0
      field_simp [hx.ne']
      nlinarith
    rw [he, Real.exp_zero]

open TransportedCertificate Family

def sourceVector (x : Vec 2) : Vec 2 := sourceScale x • radialDirection x

theorem sourceVector_eq_normalized (x : Vec 2) :
    sourceVector x = sourceNormalization • family.calibratedVector x := by
  by_cases hx : 0 < objective x
  · simp only [sourceVector, sourceScale_eq_normalized hx, calibratedVector, smul_smul]
  · have hz : objective x = 0 := le_antisymm (le_of_not_gt hx) (family.objective_nonneg x)
    have hx0 : x = 0 := family.unique_zero x hz
    subst x
    ext i
    fin_cases i <;> simp [sourceVector, calibratedVector, radialDirection]

theorem exists_source_bandCertificate {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ B : BandCertificate objective K 0 c₁ c₂ η,
      ∀ x, B.W x = outer (sourceVector x) (sourceVector x) := by
  obtain ⟨B, hW⟩ := family.exists_bandCertificate hK hη hc₁ hc₂
  let w : ℝ := sourceNormalization^2
  have hw : 0 < w := sq_pos_of_pos sourceNormalization_pos
  let C := B.rescale hc₂ (fun _ => w) w w B.L hw B.L_nonneg
    (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun _ _ _ _ _ _ _ _ => by rw [mul_comm])
  refine ⟨C, ?_⟩
  intro x
  change w • B.W x = _
  rw [hW, sourceVector_eq_normalized]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, outer, Pi.smul_apply]
  dsimp [w]
  ring

end Example
end Parabolic
end BfgsVerification
