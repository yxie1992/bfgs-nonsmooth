import BfgsVerification.OrderedCellsSemialgebraic

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem orderedCylindricalCell_count (r : ℕ) :
    Fintype.card (Fin r ⊕ Fin (r+1)) = 2*r+1 := by simp; omega

theorem ordered_cylindrical_smooth_partition {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    (S : Set E) (f : Fin r → E → ℝ) (hS : PiecewiseSmoothConnected S)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (f i) S)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x)) :
    (⋃ i, orderedCylindricalCell S f i) = {z : E × ℝ | z.1 ∈ S} ∧
    Pairwise (fun i j => Disjoint (orderedCylindricalCell S f i) (orderedCylindricalCell S f j)) ∧
    ∀ i, PiecewiseSmoothConnected (orderedCylindricalCell S f i) :=
  ⟨orderedCylindricalCell_cover S f hf, orderedCylindricalCell_pairwise_disjoint S f hf,
    orderedCylindricalCell_piecewiseSmoothConnected S f hS hsm hf⟩

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def OrderedSmoothPartitionTarget : Prop := ∀ {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    (S : Set E) (f : Fin r → E → ℝ), PiecewiseSmoothConnected S →
    (∀ i, ContDiffOn ℝ ∞ (f i) S) →
    (∀ x ∈ S, StrictMono (fun i => f i x)) →
    (⋃ i, orderedCylindricalCell S f i) = {z : E × ℝ | z.1 ∈ S} ∧
    Pairwise (fun i j => Disjoint (orderedCylindricalCell S f i) (orderedCylindricalCell S f j)) ∧
    ∀ i, PiecewiseSmoothConnected (orderedCylindricalCell S f i)

theorem orderedSmoothPartition : OrderedSmoothPartitionTarget := ordered_cylindrical_smooth_partition

def OrderedSemialgebraicCellsTarget : Prop := ∀ {n r : ℕ} (S : Set (Vec n))
    (f : Fin r → Vec n → ℝ), IsSemialgebraic S →
    (∀ i, IsSemialgebraicCylinder (orderedGraphCell S f i)) →
    ∀ i : Fin r ⊕ Fin (r+1), IsSemialgebraicCylinder (orderedCylindricalCell S f i)

theorem orderedSemialgebraicCells : OrderedSemialgebraicCellsTarget :=
  orderedCylindricalCell_semialgebraic

end BfgsVerification
