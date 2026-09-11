import BfgsVerification.HomogeneousMaxLinear
import BfgsVerification.AffineProjection

/-! Exact two-slope endpoint algebra for H.C. The inverse is an actual 2×2
matrix inverse. Uniformity comes from a finite slope alphabet, with no bounded
iterate or matrix-sequence premise. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace HomogeneousPlanar

def pairMatrix (a b : Vec 2) : Mat 2 := fun i => if i = 0 then a else b

def pairDet (a b : Vec 2) : ℝ := a 0 * b 1 - a 1 * b 0

theorem pairMatrix_det (a b : Vec 2) : (pairMatrix a b).det = pairDet a b := by
  simp [pairMatrix, Matrix.det_fin_two, pairDet]

theorem cross_dot_identity (a b w x : Vec 2) :
    dot a w * dot b x - dot b w * dot a x = pairDet a b * pairDet w x := by
  simp only [dot, Fin.sum_univ_two, pairDet]
  ring

/-- Two distinct positive-active supporting slopes with a common strictly
negative direction must be independent in the plane. This includes the source
exclusion of positively proportional and opposing dependent transitions. -/
theorem pairDet_ne_zero_of_supports (a b x z w : Vec 2)
    (ha : 0 < dot a x) (hb : 0 < dot b z)
    (hbx : dot b x ≤ dot a x) (haz : dot a z ≤ dot b z)
    (haw : dot a w < 0) (hbw : dot b w < 0) (hne : a ≠ b) : pairDet a b ≠ 0 := by
  intro hd
  have hx := cross_dot_identity a b w x
  have hz := cross_dot_identity a b w z
  rw [hd, zero_mul] at hx hz
  have he : dot a w = dot b w := by
    have h1 := mul_le_mul_of_nonpos_left hbx haw.le
    have h2 := mul_le_mul_of_nonpos_left haz hbw.le
    nlinarith
  apply hne
  have h0 : dot a w * b 0 - dot b w * a 0 = -pairDet a b * w 1 := by
    simp only [dot, Fin.sum_univ_two, pairDet]
    ring
  have h1 : dot a w * b 1 - dot b w * a 1 = pairDet a b * w 0 := by
    simp only [dot, Fin.sum_univ_two, pairDet]
    ring
  rw [hd, neg_zero, zero_mul, ← he] at h0
  rw [hd, zero_mul, ← he] at h1
  ext i
  fin_cases i
  · exact (mul_left_cancel₀ haw.ne (by linarith : dot a w * b 0 = dot a w * a 0)).symm
  · exact (mul_left_cancel₀ haw.ne (by linarith : dot a w * b 1 = dot a w * a 1)).symm

theorem pairMatrix_mulVec_norm_le (a b x : Vec 2) :
    ‖(pairMatrix a b).mulVec x‖ ≤ |dot a x| + |dot b x| := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
  intro i
  fin_cases i <;> simp [Matrix.mulVec, pairMatrix, dot, dotProduct, Real.norm_eq_abs]

theorem pair_inverse_bound (a b x : Vec 2) (hd : pairDet a b ≠ 0) :
    ‖x‖ ≤ ‖AffineProjection.matrixCLM (pairMatrix a b)⁻¹‖ * (|dot a x| + |dot b x|) := by
  have hdet : (pairMatrix a b).det ≠ 0 := by rwa [pairMatrix_det]
  have hi : (pairMatrix a b)⁻¹.mulVec ((pairMatrix a b).mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet.isUnit, Matrix.one_mulVec]
  calc
    ‖x‖ = ‖AffineProjection.matrixCLM (pairMatrix a b)⁻¹ ((pairMatrix a b).mulVec x)‖ := by rw [AffineProjection.matrixCLM_apply, hi]
    _ ≤ ‖AffineProjection.matrixCLM (pairMatrix a b)⁻¹‖ * ‖(pairMatrix a b).mulVec x‖ :=
      (AffineProjection.matrixCLM (pairMatrix a b)⁻¹).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left (pairMatrix_mulVec_norm_le a b x) (norm_nonneg _)

theorem finite_pair_scalar_bound {ι : Type*} (A : Finset ι) (c : ι → ι → ℝ)
    (hc : ∀ a b, 0 ≤ c a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ A, ∀ b ∈ A, c a b ≤ C := by
  let C := ∑ a ∈ A, ∑ b ∈ A, c a b
  refine ⟨C, Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hc _ _)), ?_⟩
  intro a ha b hb
  have h1 : c a b ≤ ∑ b ∈ A, c a b :=
    Finset.single_le_sum (s := A) (f := c a) (fun b _ => hc a b) hb
  have h2 : (∑ b ∈ A, c a b) ≤ C :=
    Finset.single_le_sum (s := A) (f := fun a => ∑ b ∈ A, c a b)
      (fun a _ => Finset.sum_nonneg (fun b _ => hc a b)) ha
  exact h1.trans h2

/-- A finite alphabet supplies a uniform actual inverse bound for every
independent pair, even when dependent pairs also occur in the alphabet. -/
theorem finite_pair_inverse_bound (A : Finset (Vec 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ x, pairDet a b ≠ 0 →
      ‖x‖ ≤ C * (|dot a x| + |dot b x|) := by
  obtain ⟨C, hC, hbound⟩ := finite_pair_scalar_bound A
    (fun a b => ‖AffineProjection.matrixCLM (pairMatrix a b)⁻¹‖)
    (fun _ _ => norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro a ha b hb x hd
  exact (pair_inverse_bound a b x hd).trans
    (mul_le_mul_of_nonneg_right (hbound a ha b hb) (add_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- Vanishing pairings and a finite independent-pair alphabet force the actual
endpoint sequence to zero, without assuming the endpoints bounded. -/
theorem endpoints_tendsto_zero (A : Finset (Vec 2)) (a b x : ℕ → Vec 2)
    (ha : ∀ k, a k ∈ A) (hb : ∀ k, b k ∈ A)
    (hd : ∀ k, pairDet (a k) (b k) ≠ 0)
    (hax : Tendsto (fun k => dot (a k) (x k)) atTop (𝓝 0))
    (hbx : Tendsto (fun k => dot (b k) (x k)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := finite_pair_inverse_bound A
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg (x k)) (fun k => hC _ (ha k) _ (hb k) _ (hd k))
  simpa using (hax.abs.add hbx.abs).const_mul C

end HomogeneousPlanar
end BfgsVerification
