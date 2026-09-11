import BfgsVerification.SemialgebraicOrderedCells

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
open RealAlgebraicGeometry

def SemialgebraicPathCompositionTarget : Prop := ∀ {σ : Type} [Fintype σ]
    {S : Set (σ → ℝ)} {x y z : σ → ℝ},
    SemialgebraicPiecewiseSmoothPathIn S x y → SemialgebraicPiecewiseSmoothPathIn S y z →
    SemialgebraicPiecewiseSmoothPathIn S x z

theorem semialgebraicPathComposition : SemialgebraicPathCompositionTarget :=
  SemialgebraicPiecewiseSmoothPathIn.trans

def SemialgebraicPathMappingTarget : Prop := ∀ {σ τ : Type} [Fintype σ] [Fintype τ]
    {S : Set (σ → ℝ)} {T : Set (τ → ℝ)} {x y : σ → ℝ},
    SemialgebraicPiecewiseSmoothPathIn S x y → ∀ {G : (σ → ℝ) → τ → ℝ},
    ContDiffOn ℝ ∞ G S → IsSemialgebraicMapOn G S → MapsTo G S T →
    SemialgebraicPiecewiseSmoothPathIn T (G x) (G y)

theorem semialgebraicPathMapping : SemialgebraicPathMappingTarget :=
  SemialgebraicPiecewiseSmoothPathIn.map

def SemialgebraicOrderedPathsTarget : Prop := ∀ {σ : Type} [Fintype σ] {r : ℕ}
    (S : Set (σ → ℝ)) (f : Fin r → (σ → ℝ) → ℝ),
    IsSemialgebraic S → SemialgebraicPiecewiseSmoothConnected S →
    (∀ i, ContDiffOn ℝ ∞ (f i) S) → (∀ x ∈ S, StrictMono (fun i => f i x)) →
    (∀ i, IsSemialgebraic {v : Option σ → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))}) →
    ∀ i : Fin r ⊕ Fin (r+1), SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      ((fun k => v (some k)), v none) ∈ orderedCylindricalCell S f i}

theorem semialgebraicOrderedPaths : SemialgebraicOrderedPathsTarget :=
  orderedCylindricalCell_semialgebraicPiecewiseSmoothConnected

end BfgsVerification
