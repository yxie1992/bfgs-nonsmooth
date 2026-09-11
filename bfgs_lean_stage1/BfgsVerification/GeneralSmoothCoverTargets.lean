import BfgsVerification.SemialgebraicSmoothCover

noncomputable section
open Set
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- The general geometry contract spells out the actual paths, finite
exception sets and exact cover rather than assuming a decomposition predicate. -/
def GeneralSemialgebraicSmoothCoverTarget : Prop :=
  ∀ (n : ℕ) (S : Set (Vec n)), IsSemialgebraic S →
    ∃ C : Finset (Set (Vec n)), (⋃ T ∈ C, T) = S ∧
      ∀ T ∈ C, IsSemialgebraic T ∧
        ∀ x ∈ T, ∀ y ∈ T, ∃ p : ℝ → Vec n,
          ContinuousOn p (Icc 0 1) ∧ p 0 = x ∧ p 1 = y ∧
          (∀ t ∈ Icc 0 1, p t ∈ T) ∧
          ∃ exceptions : Finset ℝ, ∀ t ∈ Ioo 0 1, t ∉ exceptions → ContDiffAt ℝ ∞ p t

theorem generalSemialgebraicSmoothCover : GeneralSemialgebraicSmoothCoverTarget := by
  intro n S hS
  obtain ⟨C,hC,hcover⟩ := semialgebraic_finite_smooth_cover hS
  refine ⟨C,hcover,?_⟩
  intro T hT
  refine ⟨(hC T hT).1,?_⟩
  intro x hx y hy
  obtain ⟨p⟩ := (hC T hT).2 x hx y hy
  exact ⟨p.curve,p.continuousOn,p.source,p.target,p.mapsTo,p.exceptions,p.smoothAt⟩

end RealAlgebraicGeometry
end BfgsVerification
