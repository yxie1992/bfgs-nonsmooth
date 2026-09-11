import BfgsVerification.TransportedCertificateDefinitions
import BfgsVerification.HessianUpdate

/-! Module G: every eligible objective pair is individually realizable by
an ordinary first full-BFGS step. This does not assert one common history. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification
namespace TransportedCertificate

/-- The explicit first-step metric printed in Module G. -/
def realizingMetric {n : ℕ} (g s : Vec n) : Mat n :=
  1 - (sqNorm g)⁻¹ • outer g g + (-dot g s)⁻¹ • outer s s

theorem realizingMetric_posDef {n : ℕ} (g s : Vec n) (hd : 0 < -dot g s) :
    (realizingMetric g s).PosDef := by
  have hg : g ≠ 0 := by
    intro he
    subst g
    simpa [dot] using hd
  have ht : dot s (bfgsStep (1 : Mat n) g 1) = -dot g s := by
    simp only [bfgsStep, Matrix.one_mulVec, dot_smul_right, neg_mul, one_mul]
    exact congrArg Neg.neg (dotProduct_comm s g)
  have he : metricEnergy (1 : Mat n) g = sqNorm g := by
    simp [metricEnergy, dot, sqNorm, pow_two]
  have hupdate := hessianUpdate (H := (1 : Mat n)) Matrix.PosDef.one hg s
    (α := 1) zero_lt_one (ht.symm ▸ hd)
  have hp := (inverseBFGS_posDef (H := (1 : Mat n)) Matrix.PosDef.one
    (bfgsStep 1 g 1) s (ht.symm ▸ hd)).inv
  rw [hupdate, ht, he, inv_one] at hp
  exact hp

theorem realizingMetric_mul_gradient {n : ℕ} (g s : Vec n) (hd : 0 < -dot g s) :
    (realizingMetric g s).mulVec g = -s := by
  have hg : g ≠ 0 := by
    intro he
    subst g
    simpa [dot] using hd
  have hq : sqNorm g ≠ 0 := by
    have h := metricEnergy_pos (H := (1 : Mat n)) Matrix.PosDef.one hg
    simpa [metricEnergy, dot, sqNorm, pow_two] using h.ne'
  have hgg : dot g g = sqNorm g := by simp [dot, sqNorm, pow_two]
  have hsg : dot s g = dot g s := dotProduct_comm _ _
  simp only [realizingMetric, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc, outer_mulVec, hgg, hsg, smul_smul,
    inv_mul_cancel₀ hq, one_smul, sub_self, zero_add]
  have hcoef : (-dot g s)⁻¹ * dot g s = -1 := by
    field_simp [hd.ne']
  rw [hcoef, neg_one_smul]

theorem realizingMetric_step {n : ℕ} (g s : Vec n) (hd : 0 < -dot g s) :
    bfgsStep (realizingMetric g s) g 1 = s := by
  simp [bfgsStep, realizingMetric_mul_gradient g s hd]

/-- Individual pair realizability with unit step length and the original
predicted decrease; no multi-pair trajectory compatibility is inferred. -/
theorem eligible_pair_realizable {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ}
    {x z g h : Vec n} (hp : EligiblePair F c₁ c₂ x z g h) :
    ∃ H : Mat n, H.PosDef ∧ bfgsStep H g 1 = pairStep x z ∧
      metricEnergy H g = pairDecrease x z g := by
  have hd : 0 < -dot g (pairStep x z) := hp.decrease_pos
  refine ⟨realizingMetric g (pairStep x z), realizingMetric_posDef g _ hd,
    realizingMetric_step g _ hd, ?_⟩
  simp only [metricEnergy, realizingMetric_mul_gradient g _ hd]
  simp only [pairDecrease, pairStep, dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

end TransportedCertificate
end BfgsVerification
