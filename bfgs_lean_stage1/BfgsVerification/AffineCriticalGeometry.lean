import BfgsVerification.AccessibleJumpGeometry
import Mathlib.Geometry.Euclidean.Projection

/-! Module A's canonical equal-rate affine geometry for an arbitrary nonempty
family. This uses actual orthogonal projections and actual affine hulls. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter Set

namespace BfgsVerification
namespace AffineCriticalGeometry
open AccessibleJumpGeometry

def closestAffinePoint {n : ℕ} {α : Type*} (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    EuclideanSpace ℝ (Fin n) := (tangentSpace g).orthogonalProjection (g i)

theorem closestAffinePoint_independent {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i j : α) : closestAffinePoint g i = closestAffinePoint g j := by
  exact congrArg (fun x : tangentSpace g => (x : EuclideanSpace ℝ (Fin n)))
    (common_tangential_projection g i j)

theorem closestAffinePoint_orthogonal {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) : closestAffinePoint g i ∈ (jumpSpace g)ᗮ :=
  ((tangentSpace g).orthogonalProjection (g i)).property

theorem gradient_sub_closest_mem_jump {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i j : α) : g j - closestAffinePoint g i ∈ jumpSpace g := by
  rw [closestAffinePoint_independent g i j]
  have h := (tangentSpace g).sub_orthogonalProjection_mem_orthogonal (g j)
  change g j - closestAffinePoint g j ∈ (jumpSpace g)ᗮᗮ at h
  rwa [Submodule.orthogonal_orthogonal] at h

/-- The actual common tangential projection is in the full affine hull. -/
theorem closestAffinePoint_mem_affineSpan {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    closestAffinePoint g i ∈ affineSpan ℝ (Set.range g) := by
  apply (mem_affineSpan_iff_exists ℝ).mpr
  refine ⟨g i, Set.mem_range_self i, closestAffinePoint g i - g i, ?_, ?_⟩
  · have h := (jumpSpace g).neg_mem (gradient_sub_closest_mem_jump g i i)
    simpa only [neg_sub] using h
  · change closestAffinePoint g i = (closestAffinePoint g i - g i) + g i
    abel

/-- All points of the affine hull have the same pairing with its canonical
minimum-norm vector, including every actual subgradient. -/
theorem affine_pairing_closest {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ affineSpan ℝ (Set.range g)) :
    ⟪z, closestAffinePoint g i⟫_ℝ = ‖closestAffinePoint g i‖^2 := by
  have hd : z-closestAffinePoint g i ∈ jumpSpace g :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hz (closestAffinePoint_mem_affineSpan g i)
  have ho := Submodule.inner_right_of_mem_orthogonal hd (closestAffinePoint_orthogonal g i)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  linarith

/-- Pythagoras gives the exact affine minimum-norm property. -/
theorem affine_norm_sq_decomposition {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ affineSpan ℝ (Set.range g)) :
    ‖z‖^2 = ‖closestAffinePoint g i‖^2 + ‖z-closestAffinePoint g i‖^2 := by
  have h := norm_sub_sq_real z (closestAffinePoint g i)
  rw [affine_pairing_closest g i z hz] at h
  linarith

theorem closestAffinePoint_unique_minimum {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ affineSpan ℝ (Set.range g)) :
    ‖closestAffinePoint g i‖ ≤ ‖z‖ ∧
      (‖z‖ = ‖closestAffinePoint g i‖ ↔ z = closestAffinePoint g i) := by
  have he := affine_norm_sq_decomposition g i z hz
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg ‖z-closestAffinePoint g i‖, norm_nonneg z, norm_nonneg (closestAffinePoint g i)]
  · constructor
    · intro hn
      have hh : ‖z-closestAffinePoint g i‖ = 0 := by rw [hn] at he; nlinarith [norm_nonneg (z-closestAffinePoint g i)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hh)
    · rintro rfl; rfl

theorem closestAffinePoint_zero_iff {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    closestAffinePoint g i = 0 ↔ (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (Set.range g) := by
  have h := tangent_projection_zero_iff_zero_mem_affineSpan g i
  exact (Subtype.ext_iff).symm.trans h

/-- Canonical equal-rate descent at every non-affine-critical family. -/
theorem canonical_equal_rate {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (Set.range g)) :
    ∀ j, ⟪g j, -(‖closestAffinePoint g i‖^2)⁻¹ • closestAffinePoint g i⟫_ℝ = -1 := by
  have ha : closestAffinePoint g i ≠ 0 := fun h => hzero ((closestAffinePoint_zero_iff g i).mp h)
  have hn : ‖closestAffinePoint g i‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  intro j
  rw [inner_smul_right, affine_pairing_closest g i (g j) (mem_affineSpan ℝ (mem_range_self j))]
  rw [neg_mul, inv_mul_cancel₀ hn]

/-- Equal-rate descent conversely excludes affine zero. -/
theorem affine_zero_excluded_of_equal_rate {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, ⟪g i, v⟫_ℝ = -1) :
    (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (Set.range g) := by
  intro hz
  obtain ⟨s, w, hw, he⟩ := (mem_affineSpan_iff_eq_affineCombination ℝ (EuclideanSpace ℝ (Fin n))).mp hz
  rw [Finset.affineCombination_eq_linear_combination s g w hw] at he
  have h := congrArg (fun z => ⟪z, v⟫_ℝ) he
  simp only [inner_zero_left, sum_inner, real_inner_smul_left, hv] at h
  have hsum : (∑ i ∈ s, w i * (-1 : ℝ)) = -1 := by rw [← Finset.sum_mul, hw]; ring
  rw [hsum] at h
  norm_num at h

/-- The source's affine hull is exactly the canonical point plus the jump span. -/
theorem mem_affineSpan_iff_sub_closest_mem {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) (z : EuclideanSpace ℝ (Fin n)) :
    z ∈ affineSpan ℝ (Set.range g) ↔ z - closestAffinePoint g i ∈ jumpSpace g := by
  simpa only [direction_affineSpan, vsub_eq_sub, jumpSpace] using
    ((affineSpan ℝ (Set.range g)).vsub_right_mem_direction_iff_mem
      (closestAffinePoint_mem_affineSpan g i) z).symm

/-- The norm is the actual distance to the affine hull, not a selected surrogate. -/
theorem infDist_affineSpan_eq_norm_closest {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (affineSpan ℝ (Set.range g) : Set _) =
      ‖closestAffinePoint g i‖ := by
  apply le_antisymm
  · simpa only [dist_zero_left] using Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ (Fin n)))
      (closestAffinePoint_mem_affineSpan g i)
  · apply (Metric.le_infDist ⟨closestAffinePoint g i, closestAffinePoint_mem_affineSpan g i⟩).mpr
    intro z hz
    simpa only [dist_zero_left] using (closestAffinePoint_unique_minimum g i z hz).1

/-- The canonical vector agrees with the library's actual affine orthogonal
projection of zero. The family witness supplies nonemptiness. -/
theorem closest_eq_affine_orthogonalProjection {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    letI : Nonempty (affineSpan ℝ (Set.range g)) :=
      ⟨⟨g i, mem_affineSpan ℝ (mem_range_self i)⟩⟩
    closestAffinePoint g i = EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range g)) 0 := by
  dsimp only
  letI : Nonempty (affineSpan ℝ (Set.range g)) :=
    ⟨⟨g i, mem_affineSpan ℝ (mem_range_self i)⟩⟩
  have hdist := EuclideanGeometry.dist_orthogonalProjection_eq_infDist
    (affineSpan ℝ (Set.range g)) (0 : EuclideanSpace ℝ (Fin n))
  rw [dist_zero_left, infDist_affineSpan_eq_norm_closest g i] at hdist
  exact ((closestAffinePoint_unique_minimum g i _ (EuclideanGeometry.orthogonalProjection_mem _)).2.mp hdist).symm

theorem equal_rate_exists_iff {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    (∃ v : EuclideanSpace ℝ (Fin n), ∀ j, ⟪g j, v⟫_ℝ = -1) ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (Set.range g) := by
  constructor
  · rintro ⟨v, hv⟩
    exact affine_zero_excluded_of_equal_rate g v hv
  · intro h
    exact ⟨_, canonical_equal_rate g i h⟩

theorem affine_pairing_of_constant {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : ∀ i, ⟪g i, a⟫_ℝ = c) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ affineSpan ℝ (Set.range g)) : ⟪z, a⟫_ℝ = c := by
  obtain ⟨s, w, hw, he⟩ := (mem_affineSpan_iff_eq_affineCombination ℝ (EuclideanSpace ℝ (Fin n))).mp hz
  rw [Finset.affineCombination_eq_linear_combination s g w hw] at he
  rw [he, sum_inner]
  simp only [real_inner_smul_left, hc]
  rw [← Finset.sum_mul, hw, one_mul]

/-- A concrete affine member with the constant minimum-norm pairing is the
actual closest affine point. Useful for exact rank-loss calculations. -/
theorem eq_closest_of_pairings {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) (a : EuclideanSpace ℝ (Fin n))
    (ha : a ∈ affineSpan ℝ (Set.range g)) (hg : ∀ j, ⟪g j, a⟫_ℝ = ‖a‖^2) :
    a = closestAffinePoint g i := by
  have h1 := affine_pairing_of_constant g a (‖a‖^2) hg _ (closestAffinePoint_mem_affineSpan g i)
  have h2 := affine_pairing_closest g i a ha
  rw [real_inner_comm] at h1
  have hn : ‖a‖ = ‖closestAffinePoint g i‖ := by
    nlinarith [norm_nonneg a, norm_nonneg (closestAffinePoint g i)]
  exact (closestAffinePoint_unique_minimum g i a ha).2.mp hn

end AffineCriticalGeometry
end BfgsVerification
