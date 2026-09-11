import BfgsVerification.FiniteSmoothCovers
import BfgsVerification.OrderedCylindricalTargets
import BfgsVerification.PolynomialFibers

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem parameterPoint_recover (v : Option (Fin n) → ℝ) :
    parameterPoint (fun i => v (some i)) (v none) = v := by
  funext i
  cases i <;> rfl

theorem parameterPoint_contDiff :
    ContDiff ℝ ∞ (fun z : Vec n × ℝ => parameterPoint z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_snd
  | some i => exact (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).contDiff.comp contDiff_fst

theorem parameterPoint_image_semialgebraic {T : Set (Vec n × ℝ)}
    (hT : IsSemialgebraicCylinder T) :
    IsSemialgebraic ((fun z : Vec n × ℝ => parameterPoint z.1 z.2) '' T) := by
  change IsSemialgebraic {v : Option (Fin n) → ℝ | ((fun i => v (some i)),v none) ∈ T} at hT
  convert hT using 1
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact hz
  · intro hv
    exact ⟨((fun i => v (some i)),v none),hv,parameterPoint_recover v⟩

theorem finite_smooth_cylinder_coordinate_cover {ι : Type*} [Fintype ι]
    (C : ι → Set (Vec n × ℝ))
    (hsa : ∀ i, IsSemialgebraicCylinder (C i))
    (hpath : ∀ i, PiecewiseSmoothConnected (C i)) {S : Set (Vec n)}
    (hcover : (⋃ i, C i) = {z : Vec n × ℝ | z.1 ∈ S}) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ | (fun i => v (some i)) ∈ S} := by
  have h := HasFiniteSmoothSemialgebraicCover.iUnion (fun i =>
    HasFiniteSmoothSemialgebraicCover.of_connected (parameterPoint_image_semialgebraic (hsa i))
      ((hpath i).image parameterPoint_contDiff.contDiffOn))
  convert h using 1
  ext v
  constructor
  · intro hv
    have hm : ((fun i => v (some i)),v none) ∈ ⋃ i, C i := by rw [hcover]; exact hv
    obtain ⟨i,hi⟩ := mem_iUnion.mp hm
    exact mem_iUnion.mpr ⟨i,((fun j => v (some j)),v none),hi,parameterPoint_recover v⟩
  · intro hv
    obtain ⟨i,hi⟩ := mem_iUnion.mp hv
    obtain ⟨z,hz,rfl⟩ := hi
    have hm : z ∈ ⋃ i, C i := mem_iUnion.mpr ⟨i,hz⟩
    rw [hcover] at hm
    exact hm

theorem ordered_cylinder_has_finite_smooth_cover {r : ℕ} (S : Set (Vec n))
    (f : Fin r → Vec n → ℝ) (hS : IsSemialgebraic S) (hpath : PiecewiseSmoothConnected S)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (f i) S)
    (horder : ∀ x ∈ S, StrictMono (fun i => f i x))
    (hgraph : ∀ i, IsSemialgebraicCylinder (orderedGraphCell S f i)) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ | (fun i => v (some i)) ∈ S} := by
  apply finite_smooth_cylinder_coordinate_cover (orderedCylindricalCell S f)
    (orderedCylindricalCell_semialgebraic S f hS hgraph)
  · intro i
    exact orderedCylindricalCell_piecewiseSmoothConnected S f hpath hsmooth horder i
  · exact orderedCylindricalCell_cover S f horder

end RealAlgebraicGeometry
end BfgsVerification
