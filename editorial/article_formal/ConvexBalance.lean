import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article-only correspondence wrapper for the ordinary convex balance criterion.
The finite slope family admits a common strict descent direction exactly when
its convex hull excludes zero. This is a classical separation statement, not
an additional hypothesis or a claim about realizable BFGS trajectories.
-/

noncomputable section
open scoped InnerProductSpace

namespace ArticleGeometry

/-- Strict common descent is equivalent to exclusion of zero from the convex
hull of a finite nonempty family of Euclidean slopes. -/
theorem finite_slopes_common_descent_iff
    {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n)) :
    (∃ v : EuclideanSpace ℝ (Fin n), ∀ i, ⟪a i, v⟫_ℝ < 0) ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∉ convexHull ℝ (Set.range a) := by
  constructor
  · rintro ⟨v, hv⟩ hzero
    have hull_sub : convexHull ℝ (Set.range a) ⊆
        {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ < 0} := by
      apply convexHull_min
      · rintro x ⟨i, rfl⟩
        simpa only [Set.mem_setOf_eq, real_inner_comm] using hv i
      · exact convex_halfSpace_lt
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) v).toLinearMap.isLinear 0
    have hz := hull_sub hzero
    simp only [Set.mem_setOf_eq, inner_zero_right, lt_self_iff_false] at hz
  · intro hzero
    obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range a))
      (Set.finite_range a).isCompact_convexHull.isClosed hzero
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f, ?_⟩
    intro i
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    exact (hf (a i) (subset_convexHull ℝ _ (Set.mem_range_self i))).trans
      (by simpa only [map_zero] using hu)

end ArticleGeometry

#print axioms ArticleGeometry.finite_slopes_common_descent_iff
