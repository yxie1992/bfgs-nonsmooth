import BfgsVerification.SemialgebraicPathComponents

/-! The ordinary continuous semialgebraic path relation, with no smoothness
condition included in its definition. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]

structure ContinuousSemialgebraicPath (S : Set (σ → ℝ)) (x y : σ → ℝ) where
  curve : ℝ → σ → ℝ
  continuousOn : ContinuousOn curve (Icc 0 1)
  source : curve 0 = x
  target : curve 1 = y
  mapsTo : MapsTo curve (Icc 0 1) S
  semialgebraic : IsSemialgebraicCurveOn curve (Icc 0 1)

def ContinuousSemialgebraicPathIn (S : Set (σ → ℝ)) (x y : σ → ℝ) : Prop :=
  Nonempty (ContinuousSemialgebraicPath S x y)

def continuousSemialgebraicComponent (S : Set (σ → ℝ)) (x : σ → ℝ) : Set (σ → ℝ) :=
  {y | ContinuousSemialgebraicPathIn S x y}

def ContinuousSemialgebraicPathConnected (S : Set (σ → ℝ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ContinuousSemialgebraicPathIn S x y

theorem SemialgebraicPiecewiseSmoothPathIn.toContinuousSemialgebraicPathIn
    {S : Set (σ → ℝ)} {x y : σ → ℝ}
    (h : SemialgebraicPiecewiseSmoothPathIn S x y) : ContinuousSemialgebraicPathIn S x y := by
  obtain ⟨p⟩ := h
  exact ⟨⟨p.path.curve, p.path.continuousOn, p.path.source, p.path.target,
    p.path.mapsTo, p.semialgebraic⟩⟩

theorem SemialgebraicPiecewiseSmoothConnected.toContinuousSemialgebraicPathConnected
    {S : Set (σ → ℝ)} (h : SemialgebraicPiecewiseSmoothConnected S) :
    ContinuousSemialgebraicPathConnected S :=
  fun _ hx _ hy => (h _ hx _ hy).toContinuousSemialgebraicPathIn

theorem ContinuousSemialgebraicPathIn.mem {S : Set (σ → ℝ)} {x y : σ → ℝ}
    (h : ContinuousSemialgebraicPathIn S x y) : x ∈ S ∧ y ∈ S := by
  obtain ⟨p⟩ := h
  exact ⟨p.source ▸ p.mapsTo (by norm_num), p.target ▸ p.mapsTo (by norm_num)⟩

end RealAlgebraicGeometry
end BfgsVerification
