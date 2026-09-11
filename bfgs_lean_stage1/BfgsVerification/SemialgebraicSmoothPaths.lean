import BfgsVerification.SmoothPathWitnesses
import BfgsVerification.SemialgebraicCurveGraphs

/-! Actual finite-piece-smooth paths with semialgebraic restricted graphs. -/
noncomputable section
open Set
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

structure SemialgebraicPiecewiseSmoothPath (S : Set (σ → ℝ)) (x y : σ → ℝ) where
  path : PiecewiseSmoothPath S x y
  semialgebraic : IsSemialgebraicCurveOn path.curve (Icc 0 1)

def SemialgebraicPiecewiseSmoothPathIn (S : Set (σ → ℝ)) (x y : σ → ℝ) : Prop :=
  Nonempty (SemialgebraicPiecewiseSmoothPath S x y)

theorem SemialgebraicPiecewiseSmoothPathIn.forget {S : Set (σ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) : PiecewiseSmoothPathIn S x y := by
  obtain ⟨p⟩ := h
  exact ⟨p.path⟩

theorem SemialgebraicPiecewiseSmoothPathIn.mem {S : Set (σ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) : x ∈ S ∧ y ∈ S := h.forget.mem

theorem SemialgebraicPiecewiseSmoothPathIn.refl {S : Set (σ → ℝ)} {x : σ → ℝ}
    (hx : x ∈ S) : SemialgebraicPiecewiseSmoothPathIn S x x := by
  exact ⟨⟨constantSmoothPath hx, IsSemialgebraicCurveOn.const x⟩⟩

theorem SemialgebraicPiecewiseSmoothPathIn.mono {S T : Set (σ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) (hST : S ⊆ T) :
    SemialgebraicPiecewiseSmoothPathIn T x y := by
  obtain ⟨p⟩ := h
  exact ⟨⟨{ p.path with mapsTo := fun _ ht => hST (p.path.mapsTo ht) }, p.semialgebraic⟩⟩

theorem SemialgebraicPiecewiseSmoothPathIn.symm {S : Set (σ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) :
    SemialgebraicPiecewiseSmoothPathIn S y x := by
  obtain ⟨p⟩ := h
  exact ⟨⟨reversedSmoothPath p.path, p.semialgebraic.symm⟩⟩

theorem SemialgebraicPiecewiseSmoothPathIn.segment {S : Set (σ → ℝ)}
    (hS : Convex ℝ S) {x y : σ → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    SemialgebraicPiecewiseSmoothPathIn S x y := by
  exact ⟨⟨segmentSmoothPath hS hx hy, IsSemialgebraicCurveOn.segment x y⟩⟩

theorem SemialgebraicPiecewiseSmoothPathIn.map {S : Set (σ → ℝ)}
    {T : Set (τ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) {G : (σ → ℝ) → τ → ℝ}
    (hG : ContDiffOn ℝ ∞ G S) (hGsa : IsSemialgebraicMapOn G S)
    (hGT : MapsTo G S T) : SemialgebraicPiecewiseSmoothPathIn T (G x) (G y) := by
  obtain ⟨p⟩ := h
  exact ⟨⟨mappedSmoothPath p.path hG hGT, p.semialgebraic.map hGsa p.path.mapsTo⟩⟩

/-- The map's semialgebraic domain may be larger than the path's actual set. -/
theorem SemialgebraicPiecewiseSmoothPathIn.mapOn {S U : Set (σ → ℝ)}
    {T : Set (τ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) {G : (σ → ℝ) → τ → ℝ}
    (hG : ContDiffOn ℝ ∞ G S) (hGsa : IsSemialgebraicMapOn G U)
    (hSU : S ⊆ U) (hGT : MapsTo G S T) :
    SemialgebraicPiecewiseSmoothPathIn T (G x) (G y) := by
  obtain ⟨p⟩ := h
  exact ⟨⟨mappedSmoothPath p.path hG hGT,
    p.semialgebraic.map hGsa (fun _ ht => hSU (p.path.mapsTo ht))⟩⟩

end RealAlgebraicGeometry
end BfgsVerification
