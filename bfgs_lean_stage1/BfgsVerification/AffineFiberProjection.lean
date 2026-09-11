import BfgsVerification.AffineLifting

/-! The fixed BFGS lift is exactly the projection onto a fiber in the inverse
initial metric. The characterization is proved by an actual Pythagorean identity. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection

def fiberPoint {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (H : Mat n)
    (x₀ : Vec n) (z : Vec r) : Vec n := x₀ + (lift A H).mulVec (z - A.mulVec x₀)

theorem fiberPoint_in_fiber {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) (x₀ : Vec n) (z : Vec r) :
    A.mulVec (fiberPoint A H x₀ z) = z := by
  unfold fiberPoint
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_lift A hA hH, Matrix.one_mulVec]
  abel

theorem inverse_mul_lift {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    {H : Mat n} (hH : H.PosDef) : H⁻¹ * lift A H = Aᵀ * (compress A H)⁻¹ := by
  unfold lift
  simp only [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.one_mul]

theorem energy_add_vectors {n : ℕ} (B : Mat n) (hB : B.IsSymm) (u v : Vec n) :
    metricEnergy B (u + v) = metricEnergy B u + 2 * dot u (B.mulVec v) + metricEnergy B v := by
  have hswap : dot v (B.mulVec u) = dot u (B.mulVec v) := by
    change v ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ (B *ᵥ v)
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  unfold metricEnergy
  change (u + v) ⬝ᵥ (B *ᵥ (u + v)) = _
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  change dot u (B.mulVec u) + dot u (B.mulVec v) +
    (dot v (B.mulVec u) + dot v (B.mulVec v)) = _
  rw [hswap]
  ring

/-- Orthogonality to a fiber is derived from the actual initial inverse metric. -/
theorem fiber_cross_term_zero {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) (x₀ x : Vec n) (z : Vec r)
    (hx : A.mulVec x = z) :
    dot (x - fiberPoint A H x₀ z) (H⁻¹.mulVec (fiberPoint A H x₀ z - x₀)) = 0 := by
  have hk : A.mulVec (x - fiberPoint A H x₀ z) = 0 := by
    rw [Matrix.mulVec_sub, hx, fiberPoint_in_fiber A hA hH, sub_self]
  have hp : fiberPoint A H x₀ z - x₀ = (lift A H).mulVec (z - A.mulVec x₀) := by
    unfold fiberPoint
    abel
  rw [hp, Matrix.mulVec_mulVec, inverse_mul_lift A hH, ← Matrix.mulVec_mulVec]
  rw [show dot (x - fiberPoint A H x₀ z)
      (Aᵀ.mulVec ((compress A H)⁻¹.mulVec (z - A.mulVec x₀))) =
    dot (Aᵀ.mulVec ((compress A H)⁻¹.mulVec (z - A.mulVec x₀)))
      (x - fiberPoint A H x₀ z) from dotProduct_comm _ _]
  rw [dot_transpose_mulVec, hk]
  simp [dot]

/-- Pythagoras in H⁻¹ for the actual affine fiber; no optimization oracle is used. -/
theorem fiber_pythagoras {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) (x₀ x : Vec n) (z : Vec r)
    (hx : A.mulVec x = z) :
    metricEnergy H⁻¹ (x - x₀) = metricEnergy H⁻¹ (fiberPoint A H x₀ z - x₀) +
      metricEnergy H⁻¹ (x - fiberPoint A H x₀ z) := by
  have hsym : H⁻¹.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.inv.isHermitian.eq
  calc
    _ = metricEnergy H⁻¹ ((x - fiberPoint A H x₀ z) + (fiberPoint A H x₀ z - x₀)) := by
      congr 1
      abel
    _ = _ := by
      rw [energy_add_vectors _ hsym, fiber_cross_term_zero A hA hH x₀ x z hx]
      ring

/-- The explicit fiber point minimizes squared initial-metric distance. -/
theorem fiberPoint_minimizes {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) (x₀ x : Vec n) (z : Vec r)
    (hx : A.mulVec x = z) :
    metricEnergy H⁻¹ (fiberPoint A H x₀ z - x₀) ≤ metricEnergy H⁻¹ (x - x₀) := by
  rw [fiber_pythagoras A hA hH x₀ x z hx]
  have hn : 0 ≤ metricEnergy H⁻¹ (x - fiberPoint A H x₀ z) := by
    simpa only [metricEnergy, dot, dotProduct, star_trivial] using
      hH.inv.posSemidef.2 (x - fiberPoint A H x₀ z)
  linarith

/-- Equality in the minimum-distance bound uniquely identifies the lifted point. -/
theorem fiberPoint_minimizer_unique {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) (x₀ x : Vec n) (z : Vec r)
    (hx : A.mulVec x = z) :
    metricEnergy H⁻¹ (x - x₀) = metricEnergy H⁻¹ (fiberPoint A H x₀ z - x₀) ↔
      x = fiberPoint A H x₀ z := by
  constructor
  · intro he
    by_contra hn
    have hp := metricEnergy_pos hH.inv (sub_ne_zero.mpr hn)
    have hid := fiber_pythagoras A hA hH x₀ x z hx
    linarith
  · intro he
    rw [he]

end AffineProjection
end BfgsVerification
