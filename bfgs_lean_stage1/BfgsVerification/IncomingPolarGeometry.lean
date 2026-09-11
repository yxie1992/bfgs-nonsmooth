import BfgsVerification.PointwiseCertificateFeasibility
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.Normed.Module.Dual

/-! The source incoming-direction set is the actual absolute polar of the
closed absolutely convex hull of all normalized incoming jumps. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Set Matrix Filter

namespace BfgsVerification.PointwiseFeasibility

def dotPairing {n : ℕ} : Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] ℝ := Matrix.toBilin' (1 : Mat n)

theorem dotPairing_apply {n : ℕ} (x y : Vec n) : dotPairing x y = dot x y := by
  change Matrix.toBilin' (1 : Mat n) x y = dot x y
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
  rfl

/-- The dot-product polar is unaffected by taking the closed absolutely
convex hull. There is no finiteness assumption on the generator set. -/
theorem dotPolar_closedAbsConvexHull {n : ℕ} (S : Set (Vec n)) :
    dotPairing.polar (closedAbsConvexHull ℝ S) = dotPairing.polar S := by
  apply Set.Subset.antisymm (dotPairing.polar_antitone subset_closedAbsConvexHull)
  intro v hv
  let T : Set (Vec n) := dotPairing.flip.polar {v}
  have hST : S ⊆ T := by
    intro w hw
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hv w hw
  have hc : AbsConvex ℝ T := LinearMap.polar_AbsConvex {v}
  have hclosed : IsClosed T := by
    change IsClosed (dotPairing.flip.polar {v})
    rw [LinearMap.polar_singleton]
    apply isClosed_le _ continuous_const
    simp only [LinearMap.flip_apply, dotPairing_apply]
    unfold dot
    fun_prop
  intro w hw
  exact (closedAbsConvexHull_min hST hc hclosed hw) v rfl

theorem incomingPolar_eq_normalized_polar {n : ℕ} {β : Type*}
    (y : β → Vec n) (t : β → ℝ) (ht : ∀ j, 0 < t j) :
    incomingPolar y t = dotPairing.polar (Set.range (fun j => (Real.sqrt (t j))⁻¹ • y j)) := by
  ext v
  constructor
  · intro hv
    rintro w ⟨j, rfl⟩
    have hs := Real.sqrt_pos.mpr (ht j)
    have he : dot ((Real.sqrt (t j))⁻¹ • y j) v = (Real.sqrt (t j))⁻¹ * dot (y j) v := by
      simp [dot, Finset.mul_sum, mul_assoc]
    rw [dotPairing_apply, he, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hs)]
    calc
      _ ≤ (Real.sqrt (t j))⁻¹ * Real.sqrt (t j) :=
        mul_le_mul_of_nonneg_left (hv j) (inv_nonneg.mpr hs.le)
      _ = 1 := inv_mul_cancel₀ hs.ne'
  · intro hv j
    have hh := hv _ (Set.mem_range_self j)
    have hs := Real.sqrt_pos.mpr (ht j)
    have he : dot ((Real.sqrt (t j))⁻¹ • y j) v = (Real.sqrt (t j))⁻¹ * dot (y j) v := by
      simp [dot, Finset.mul_sum, mul_assoc]
    rw [dotPairing_apply, he, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hs)] at hh
    have hm := mul_le_mul_of_nonneg_left hh hs.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_one] using hm

/-- Literal polar formulation of Module G's D(z), using every normalized
incoming jump, including the empty predecessor case. -/
theorem incomingPolar_eq_closedHull_polar {n : ℕ} {β : Type*}
    (y : β → Vec n) (t : β → ℝ) (ht : ∀ j, 0 < t j) :
    incomingPolar y t = dotPairing.polar
      (closedAbsConvexHull ℝ (Set.range (fun j => (Real.sqrt (t j))⁻¹ • y j))) := by
  rw [dotPolar_closedAbsConvexHull, incomingPolar_eq_normalized_polar y t ht]

theorem incomingPolar_empty {n : ℕ} {β : Type*} [IsEmpty β]
    (y : β → Vec n) (t : β → ℝ) : incomingPolar y t = univ := by
  ext v
  simp [incomingPolar, isEmptyElim]

/-- The closed-hull polar identity specialized to every actual source
predecessor at the fixed threshold, with curvature positivity derived from
weak Wolfe. -/
theorem sourceIncomingPolar_eq_closedHull_polar {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η δ : ℝ} (hc₂ : c₂ < 1) (z : BandPoint F K fstar η) :
    incomingPolar (sourceJump (c₁ := c₁) (c₂ := c₂) (δ := δ) z) (sourceCurvature z) =
      dotPairing.polar (closedAbsConvexHull ℝ
        (Set.range (fun x : IncomingPoint F K fstar c₁ c₂ η δ z =>
          (Real.sqrt (sourceCurvature z x))⁻¹ • sourceJump z x))) := by
  apply incomingPolar_eq_closedHull_polar
  intro x
  exact (mul_pos (sub_pos.mpr hc₂) x.property.1.decrease_pos).trans_le x.property.1.curvature

end BfgsVerification.PointwiseFeasibility
