import BfgsVerification.AffineCriticalObjective
import BfgsVerification.FiniteMaxLocalCorrectness
import BfgsVerification.HomogeneousPlanarAlgebra

/-! Source C's active-cardinality and two-gradient transversality deductions.
These concern actual affine hulls, not a assumed regular-switching certificate. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace AffineCriticalObjective
open ConvexSubdifferential

theorem isAffineCritical_iff_coordinate_affineSpan {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    IsAffineCritical F x ↔ (0 : Vec n) ∈ affineSpan ℝ (subdifferential F x) := by
  let e := (WithLp.linearEquiv 2 ℝ (Vec n)).symm
  rw [IsAffineCritical,range_subgradientFamily]
  have hm := AffineSubspace.map_span e.toAffineEquiv.toAffineMap (subdifferential F x)
  change (affineSpan ℝ (subdifferential F x)).map e.toAffineEquiv.toAffineMap =
    affineSpan ℝ (euclideanVector '' subdifferential F x) at hm
  rw [← hm]
  constructor
  · rintro ⟨g,hg,he⟩
    have hz : g = 0 := e.injective (he.trans (by simp))
    simpa only [hz] using hg
  · intro hz
    exact ⟨0,hz,by simp⟩

end AffineCriticalObjective
namespace PlanarActiveGeometry
open HomogeneousPlanar AffineCriticalObjective ConvexSubdifferential

theorem cardinal_le_two_of_affineIndependent_not_critical {m : ℕ} (g : Fin m → Vec 2)
    (hi : AffineIndependent ℝ g) (hn : (0 : Vec 2) ∉ affineSpan ℝ (range g)) : m ≤ 2 := by
  classical
  have hv : Module.finrank ℝ (vectorSpan ℝ (range g)) ≤ 2 := by
    simpa using Submodule.finrank_le (vectorSpan ℝ (range g))
  have hm' : m ≤ Module.finrank ℝ (vectorSpan ℝ (range g))+1 := by
    simpa using hi.card_le_finrank_succ
  have hm : m ≤ 3 := by omega
  by_contra h
  have hm3 : m = 3 := by omega
  have htop : affineSpan ℝ (range g) = ⊤ :=
    hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hm3])
  apply hn
  rw [htop]
  trivial

/-- Distinct dependent planar vectors have an affine line through zero. -/
theorem affine_zero_of_pairDet_zero (a b : Vec 2) (hne : a ≠ b) (hd : pairDet a b = 0) :
    (0 : Vec 2) ∈ affineSpan ℝ (range ![a,b]) := by
  have hx : a 0 ≠ b 0 ∨ a 1 ≠ b 1 := by
    by_contra h
    push_neg at h
    apply hne
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hmem (r : ℝ) : AffineMap.lineMap a b r ∈ affineSpan ℝ (range ![a,b]) :=
    AffineMap.lineMap_mem r
      (mem_affineSpan ℝ (by exact ⟨0,rfl⟩)) (mem_affineSpan ℝ (by exact ⟨1,rfl⟩))
  rcases hx with hx | hx
  · have he : AffineMap.lineMap a b (a 0/(a 0-b 0)) = 0 := by
      have hn : a 0-b 0 ≠ 0 := sub_ne_zero.mpr hx
      ext i
      fin_cases i <;> simp only [AffineMap.lineMap_apply_module,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      · field_simp [hn]
        <;> ring
      · field_simp [hn]
        dsimp only [pairDet] at hd
        nlinarith [congrArg (fun v : ℝ => v*(a 0-b 0)) hd]
    simpa only [he] using hmem (a 0/(a 0-b 0))
  · have he : AffineMap.lineMap a b (a 1/(a 1-b 1)) = 0 := by
      have hn : a 1-b 1 ≠ 0 := sub_ne_zero.mpr hx
      ext i
      fin_cases i <;> simp only [AffineMap.lineMap_apply_module,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      · field_simp [hn]
        dsimp only [pairDet] at hd
        nlinarith [congrArg (fun v : ℝ => v*(a 1-b 1)) hd]
      · field_simp [hn]
        <;> ring
    simpa only [he] using hmem (a 1/(a 1-b 1))

theorem pairDet_ne_zero_of_not_critical (a b : Vec 2) (hne : a ≠ b)
    (hn : (0 : Vec 2) ∉ affineSpan ℝ (range ![a,b])) : pairDet a b ≠ 0 :=
  fun hd => hn (affine_zero_of_pairDet_zero a b hne hd)

/-- Exact source equal-increase velocity from the actual invertible gradient
row matrix, prior to the implicit-function construction of its curve. -/
theorem inverse_common_rate (a b : Vec 2) (hd : pairDet a b ≠ 0) :
    dot a ((pairMatrix a b)⁻¹.mulVec 1) = 1 ∧
      dot b ((pairMatrix a b)⁻¹.mulVec 1) = 1 := by
  have hdet : (pairMatrix a b).det ≠ 0 := by rwa [pairMatrix_det]
  have he : (pairMatrix a b).mulVec ((pairMatrix a b)⁻¹.mulVec 1) = 1 := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hdet.isUnit,Matrix.one_mulVec]
  constructor
  · simpa [Matrix.mulVec,pairMatrix,dot] using congrFun he 0
  · simpa [Matrix.mulVec,pairMatrix,dot] using congrFun he 1

end PlanarActiveGeometry
end BfgsVerification
