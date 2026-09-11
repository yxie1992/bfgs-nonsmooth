import BfgsVerification.ContinuousSemialgebraicPaths
import BfgsVerification.SemialgebraicActualPathComponents
import BfgsVerification.SemialgebraicCurveSmooth

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]

/-- Smoothness off a finite set is derived for the very same continuous path. -/
theorem ContinuousSemialgebraicPathIn.toSemialgebraicPiecewiseSmoothPathIn
    {S : Set (σ → ℝ)} {x y : σ → ℝ} (h : ContinuousSemialgebraicPathIn S x y) :
    SemialgebraicPiecewiseSmoothPathIn S x y := by
  obtain ⟨p⟩ := h
  obtain ⟨E, hE⟩ := semialgebraic_curve_smooth_except_finite p.semialgebraic
  exact ⟨⟨⟨p.curve, p.continuousOn, p.source, p.target, p.mapsTo, E,
    fun t ht he => hE t ⟨ht.1.le, ht.2.le⟩ he⟩, p.semialgebraic⟩⟩

theorem continuous_semialgebraic_path_iff_piecewise_smooth
    (S : Set (σ → ℝ)) (x y : σ → ℝ) :
    ContinuousSemialgebraicPathIn S x y ↔ SemialgebraicPiecewiseSmoothPathIn S x y :=
  ⟨fun h => h.toSemialgebraicPiecewiseSmoothPathIn,
    fun h => h.toContinuousSemialgebraicPathIn⟩

theorem continuousSemialgebraicComponent_eq (S : Set (σ → ℝ)) (x : σ → ℝ) :
    continuousSemialgebraicComponent S x = semialgebraicSmoothComponent S x := by
  ext y
  exact continuous_semialgebraic_path_iff_piecewise_smooth S x y

theorem continuousSemialgebraicPathIn_equivalence (S : Set (σ → ℝ)) :
    Equivalence (fun x y : S => ContinuousSemialgebraicPathIn S x.val y.val) := by
  have he : (fun x y : S => ContinuousSemialgebraicPathIn S x.val y.val) =
      (fun x y : S => SemialgebraicPiecewiseSmoothPathIn S x.val y.val) := by
    funext x y
    exact propext (continuous_semialgebraic_path_iff_piecewise_smooth S x.val y.val)
  rw [he]
  exact semialgebraicPiecewiseSmoothPathIn_equivalence S

theorem continuousSemialgebraicComponent_connected (S : Set (σ → ℝ)) (x : σ → ℝ) :
    SemialgebraicPiecewiseSmoothConnected (continuousSemialgebraicComponent S x) := by
  rw [continuousSemialgebraicComponent_eq]
  exact semialgebraicSmoothComponent_connected S x

/-- The component operator here uses arbitrary continuous semialgebraic paths.
The equivalent finite-piece-smooth witnesses and the finite cover are derived. -/
theorem continuous_semialgebraic_components {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    (continuousSemialgebraicComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (continuousSemialgebraicComponent S x) ∧
      ContinuousSemialgebraicPathConnected (continuousSemialgebraicComponent S x) ∧
      SemialgebraicPiecewiseSmoothConnected (continuousSemialgebraicComponent S x) := by
  have h := semialgebraic_actual_path_components hS
  have he : continuousSemialgebraicComponent S = semialgebraicSmoothComponent S := by
    funext x
    exact continuousSemialgebraicComponent_eq S x
  refine ⟨?_, fun x => ?_⟩
  · simpa only [he] using h.1
  · have hx := h.2 x
    rw [← continuousSemialgebraicComponent_eq] at hx
    exact ⟨hx.1, hx.2.toContinuousSemialgebraicPathConnected, hx.2⟩

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def SemialgebraicPathRegularityEquivalenceTarget : Prop := ∀ {σ : Type} [Fintype σ]
    (S : Set (σ → ℝ)) (x y : σ → ℝ),
    ContinuousSemialgebraicPathIn S x y ↔ SemialgebraicPiecewiseSmoothPathIn S x y

theorem semialgebraicPathRegularityEquivalence : SemialgebraicPathRegularityEquivalenceTarget :=
  continuous_semialgebraic_path_iff_piecewise_smooth

def ContinuousSemialgebraicComponentsTarget : Prop := ∀ {σ : Type} [Fintype σ]
    {S : Set (σ → ℝ)}, IsSemialgebraic S →
    (continuousSemialgebraicComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (continuousSemialgebraicComponent S x) ∧
      ContinuousSemialgebraicPathConnected (continuousSemialgebraicComponent S x) ∧
      SemialgebraicPiecewiseSmoothConnected (continuousSemialgebraicComponent S x)

theorem continuousSemialgebraicComponents : ContinuousSemialgebraicComponentsTarget :=
  continuous_semialgebraic_components

end BfgsVerification
