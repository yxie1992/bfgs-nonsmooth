import BfgsVerification.HomogeneousPlanarAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Module C's angular frame identities and exact planar transport coefficients.
The source's displayed triangular determinant formula is corrected for the
orientation det(T,n)=-1; absolute-value estimates are unaffected. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarTransport
open HomogeneousPlanar

def normal (θ : ℝ) : Vec 2 := ![Real.cos θ,Real.sin θ]
def tangent (θ : ℝ) : Vec 2 := ![-Real.sin θ,Real.cos θ]
def angularFrame (h hθ : ℝ → ℝ) (θ : ℝ) : Vec 2 := h θ • normal θ+hθ θ • tangent θ

theorem normal_norm_sq (θ : ℝ) : sqNorm (normal θ) = 1 := by
  simpa [sqNorm,normal,Fin.sum_univ_two,add_comm] using Real.sin_sq_add_cos_sq θ

theorem tangent_norm_sq (θ : ℝ) : sqNorm (tangent θ) = 1 := by
  simpa [sqNorm,tangent,Fin.sum_univ_two] using Real.sin_sq_add_cos_sq θ

theorem normal_dot_tangent (θ : ℝ) : dot (normal θ) (tangent θ) = 0 := by
  simp [dot,normal,tangent,Fin.sum_univ_two]
  ring

theorem tangent_normal_det (θ : ℝ) : pairDet (tangent θ) (normal θ) = -1 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp [pairDet,normal,tangent]
  nlinarith

theorem reconstruct (θ : ℝ) (v : Vec 2) :
    dot (normal θ) v • normal θ+dot (tangent θ) v • tangent θ = v := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i
  fin_cases i <;> simp [dot,normal,tangent,Fin.sum_univ_two]
  · nlinarith [congrArg (fun a : ℝ => a*v 0) h]
  · nlinarith [congrArg (fun a : ℝ => a*v 1) h]

/-- The corner formula is exact on both sides of the interface. -/
theorem angularFrame_eq_constant (h hθ : ℝ → ℝ) (θ : ℝ) (v : Vec 2)
    (hh : h θ = dot (normal θ) v) (hd : hθ θ = dot (tangent θ) v) :
    angularFrame h hθ θ = v := by
  rw [angularFrame,hh,hd]
  exact reconstruct θ v

theorem normal_pairing_angularFrame (h hθ : ℝ → ℝ) (θ : ℝ) :
    dot (normal θ) (angularFrame h hθ θ) = h θ := by
  have hn : dot (normal θ) (normal θ) = 1 := by
    simpa only [dot,sqNorm,pow_two] using normal_norm_sq θ
  change dotProduct (normal θ) (h θ • normal θ+hθ θ • tangent θ) = _
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
  change h θ*dot (normal θ) (normal θ)+hθ θ*dot (normal θ) (tangent θ)=_
  rw [hn,normal_dot_tangent]
  ring

theorem normal_hasDerivAt (θ : ℝ) : HasDerivAt normal (tangent θ) θ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [normal,tangent] using Real.hasDerivAt_cos θ
  · simpa [normal,tangent] using Real.hasDerivAt_sin θ

theorem tangent_hasDerivAt (θ : ℝ) : HasDerivAt tangent (-normal θ) θ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [normal,tangent] using (Real.hasDerivAt_sin θ).neg
  · simpa [normal,tangent] using Real.hasDerivAt_cos θ

/-- C's exact angular identity; no sign condition on h+h'' is needed. -/
theorem angularFrame_hasDerivAt (h hθ : ℝ → ℝ) (θ h1 h2 : ℝ)
    (hh : HasDerivAt h h1 θ) (hd : HasDerivAt hθ h2 θ) (he : hθ θ = h1) :
    HasDerivAt (angularFrame h hθ) ((h θ+h2) • tangent θ) θ := by
  convert (hh.smul (normal_hasDerivAt θ)).add (hd.smul (tangent_hasDerivAt θ)) using 1
  ext i
  fin_cases i <;> simp [normal,tangent,he] <;> ring

/-- Correct ambient determinant for the ordered orthonormal basis (T,n).
The source displayed its negative; subsequent absolute-value bounds agree. -/
theorem triangular_determinant (θ sT sn a b e : ℝ) :
    pairDet (sT • tangent θ+sn • normal θ)
      ((a*sT+b*sn) • tangent θ+(e*sn) • normal θ) = sn*((a-e)*sT+b*sn) := by
  have hid : pairDet (sT • tangent θ+sn • normal θ)
      ((a*sT+b*sn) • tangent θ+(e*sn) • normal θ) =
      (Real.sin θ^2+Real.cos θ^2)*(sn*((a-e)*sT+b*sn)) := by
    simp only [pairDet,normal,tangent,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  rw [hid,Real.sin_sq_add_cos_sq,one_mul]

/-- Every nondegenerate planar step/frame pair has the exact determinant
transport representation. It is not an assumed frame transport law. -/
theorem determinant_transport (s w z : Vec 2) (hd : pairDet s w ≠ 0) :
    z = (pairDet s z/pairDet s w) • w+(pairDet z w/pairDet s w) • s := by
  have hd' : s 0*w 1-s 1*w 0 ≠ 0 := hd
  ext i
  fin_cases i <;> simp only [pairDet,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  · field_simp [hd']
    <;> ring
  · field_simp [hd']
    <;> ring

theorem determinant_transport_positive (s w z : Vec 2)
    (hsign : 0 < pairDet s z*pairDet s w) :
    0 < pairDet s z/pairDet s w ∧
      z = (pairDet s z/pairDet s w) • w+(pairDet z w/pairDet s w) • s := by
  have hd : pairDet s w ≠ 0 := by intro h; rw [h,mul_zero] at hsign; linarith
  refine ⟨?_,determinant_transport s w z hd⟩
  exact div_pos_iff.mpr (mul_pos_iff.mp hsign)

end PlanarTransport
end BfgsVerification
