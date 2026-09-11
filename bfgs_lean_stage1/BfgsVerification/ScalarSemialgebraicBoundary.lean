import BfgsVerification.UnivariateCellGeometry
import BfgsVerification.FiniteRootSignatureCover
import BfgsVerification.OrderedRootBranches
import Mathlib.Topology.Instances.Sign

noncomputable section
open Set Filter Polynomial
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry

/-- A semialgebraic subset of the real line has only finitely many points
at which membership fails to supply a neighborhood. -/
theorem univariate_semialgebraic_neighborhood_except_finite {S : Set ℝ}
    (hS : IsSemialgebraic (univariateLift S)) :
    ∃ B : Finset ℝ, ∀ t ∈ S, t ∉ B → S ∈ 𝓝 t := by
  classical
  obtain ⟨f,hf⟩ := hS
  let B := rootBoundary f.univariatePolynomials
  refine ⟨B,?_⟩
  intro t ht htB
  have hsub : cutProfile B t ⊆ B := Finset.filter_subset _ _
  have hopen := rootFreeCell_isOpen hsub
  have htC : t ∈ rootFreeCell B (cutProfile B t) := ⟨htB,rfl⟩
  apply Filter.mem_of_superset (hopen.mem_nhds htC)
  intro u hu
  have he := f.holds_constant_on_profile (Finset.Subset.refl _) htB hu.1 hu.2.symm
  exact (hf (fun _ => u)).mpr (he.mp ((hf (fun _ => t)).mp ht))

/-- The same finite-boundary conclusion in the exact single-coordinate model
used by ordered parameter roots. -/
theorem vec_one_semialgebraic_neighborhood_except_finite {S : Set (Vec 1)}
    (hS : IsSemialgebraic S) :
    ∃ B : Finset ℝ, ∀ t, (fun _ : Fin 1 => t) ∈ S → t ∉ B →
      {u : ℝ | (fun _ : Fin 1 => u) ∈ S} ∈ 𝓝 t := by
  have hs : IsSemialgebraic (univariateLift {t : ℝ | (fun _ : Fin 1 => t) ∈ S}) := by
    simpa only [univariateLift,mem_setOf_eq] using hS.reindex (fun _ : Fin 1 => (() : Unit))
  exact univariate_semialgebraic_neighborhood_except_finite hs

end BfgsVerification.RealAlgebraicGeometry
