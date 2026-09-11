import BfgsVerification.SemialgebraicPathCover

noncomputable section
open Set
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Literal semialgebraic witness paths: the graph on the closed parameter
interval is part of the conclusion, together with actual smoothness. -/
def GeneralSemialgebraicPathCoverTarget : Prop :=
  ∀ (n : ℕ) (S : Set (Vec n)), IsSemialgebraic S →
    ∃ C : Finset (Set (Vec n)), (⋃ T ∈ C, T) = S ∧
      ∀ T ∈ C, IsSemialgebraic T ∧
        ∀ x ∈ T, ∀ y ∈ T, ∃ p : ℝ → Vec n,
          ContinuousOn p (Icc 0 1) ∧ p 0 = x ∧ p 1 = y ∧
          (∀ t ∈ Icc 0 1, p t ∈ T) ∧
          IsSemialgebraic {v : Option (Fin n) → ℝ |
            v none ∈ Icc (0 : ℝ) 1 ∧ (fun i => v (some i)) = p (v none)} ∧
          ∃ exceptions : Finset ℝ, ∀ t ∈ Ioo 0 1, t ∉ exceptions → ContDiffAt ℝ ∞ p t

theorem generalSemialgebraicPathCover : GeneralSemialgebraicPathCoverTarget := by
  intro n S hS
  obtain ⟨C,hC,hcover⟩ := semialgebraic_finite_path_cover hS
  refine ⟨C,hcover,?_⟩
  intro T hT
  refine ⟨(hC T hT).1,?_⟩
  intro x hx y hy
  obtain ⟨p⟩ := (hC T hT).2 x hx y hy
  exact ⟨p.path.curve,p.path.continuousOn,p.path.source,p.path.target,p.path.mapsTo,
    p.semialgebraic,p.path.exceptions,p.path.smoothAt⟩

end RealAlgebraicGeometry
end BfgsVerification
