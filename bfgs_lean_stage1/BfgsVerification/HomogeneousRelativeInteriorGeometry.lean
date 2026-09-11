import BfgsVerification.HomogeneousPlanarEscape
import BfgsVerification.AffineImageLifting

/-! Relative interior is taken in the actual span of the finite slopes, exactly
as in H.8. No coercivity constant or projected-run convergence is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- Zero belongs to the interior of the convex hull in the slope-span subspace.
This is relative interior in S=span(A), with its inherited topology. -/
def RelativeInteriorZero {n : ℕ} (A : Finset (Vec n)) : Prop :=
  (0 : Submodule.span ℝ (A : Set (Vec n))) ∈ interior
    {v : Submodule.span ℝ (A : Set (Vec n)) | (v : Vec n) ∈ convexHull ℝ (A : Set (Vec n))}

theorem dot_convexHull_le_finiteMaxLinear {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (x y : Vec n) (hy : y ∈ convexHull ℝ (A : Set (Vec n))) :
    dot y x ≤ finiteMaxLinear A hA x := by
  have hsub : convexHull ℝ (A : Set (Vec n)) ⊆
      {v | (gradientFunctional x) v ≤ finiteMaxLinear A hA x} := by
    apply convexHull_min
    · intro a ha
      change (gradientFunctional x) a ≤ _
      rw [gradientFunctional_apply]
      exact (show dot x a = dot a x from dotProduct_comm _ _).trans_le
        (slope_le_finiteMaxLinear A hA ha x)
    · exact (convex_Iic (finiteMaxLinear A hA x)).linear_preimage (gradientFunctional x).toLinearMap
  have h := hsub hy
  change (gradientFunctional x) y ≤ finiteMaxLinear A hA x at h
  rw [gradientFunctional_apply] at h
  exact (show dot y x = dot x y from dotProduct_comm _ _).trans_le h

theorem relativeInteriorZero_nonneg {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (hri : RelativeInteriorZero A) (x : Vec n) : 0 ≤ finiteMaxLinear A hA x := by
  have hz := interior_subset (s :=
    {v : Submodule.span ℝ (A : Set (Vec n)) | (v : Vec n) ∈ convexHull ℝ (A : Set (Vec n))}) hri
  have h0 : (0 : Vec n) ∈ convexHull ℝ (A : Set (Vec n)) := hz
  simpa only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using
    dot_convexHull_le_finiteMaxLinear A hA x 0 h0

/-- Relative interior gives strict positivity on every nonzero vector of the
actual slope span. The small ball is derived from the interior hypothesis. -/
theorem relativeInteriorZero_positive_on_span {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (hri : RelativeInteriorZero A) (x : Vec n)
    (hxS : x ∈ Submodule.span ℝ (A : Set (Vec n))) (hx : x ≠ 0) :
    0 < finiteMaxLinear A hA x := by
  let S := Submodule.span ℝ (A : Set (Vec n))
  let xs : S := ⟨x, hxS⟩
  have hxs : xs ≠ 0 := by
    intro he
    exact hx (congrArg (fun v : S => (v : Vec n)) he)
  have hnx : 0 < ‖xs‖ := norm_pos_iff.mpr hxs
  have hn : {v : S | (v : Vec n) ∈ convexHull ℝ (A : Set (Vec n))} ∈ 𝓝 (0 : S) :=
    mem_interior_iff_mem_nhds.mp hri
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  let c := ε / (2*‖xs‖)
  have hc : 0 < c := div_pos hε (mul_pos (by norm_num) hnx)
  have hnorm : ‖c • xs‖ = ε/2 := by
    change ‖c • x‖ = ε/2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    change c * ‖xs‖ = ε/2
    dsimp only [c]
    field_simp
    ring
  have hmem : c • xs ∈ Metric.ball (0 : S) ε := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    linarith
  have hy : ((c • xs : S) : Vec n) ∈ convexHull ℝ (A : Set (Vec n)) := hball hmem
  have hbound := dot_convexHull_le_finiteMaxLinear A hA x ((c • xs : S) : Vec n) hy
  have hp : 0 < dot x x := by
    simpa only [metricEnergy, Matrix.one_mulVec] using metricEnergy_pos (H := (1 : Mat n)) Matrix.PosDef.one hx
  have he : dot ((c • xs : S) : Vec n) x = c * dot x x := by
    change dot (c • x) x = _
    simp [dot, Finset.mul_sum, mul_assoc]
  rw [he] at hbound
  exact (mul_pos hc hp).trans_le hbound

theorem orthonormal_transpose_fullRowRank {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) : AffineProjection.FullRowRank Uᵀ := by
  intro x y hxy
  have h := congrArg Uᵀ.mulVec hxy
  simpa only [Matrix.transpose_transpose, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using h

theorem orthonormal_projection_on_range {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (x : Vec n) (hx : ∃ z, U.mulVec z = x) :
    U.mulVec (Uᵀ.mulVec x) = x := by
  obtain ⟨z, rfl⟩ := hx
  have hm : Uᵀ.mulVec (U.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [hm]

/-- The finite maximum globally factors through the slope-span projection.
This uses membership of every original slope, not merely tail gradients. -/
theorem finiteMaxLinear_projection_eq {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hAsub : ∀ a ∈ A, ∃ z, U.mulVec z = a) (x : Vec n) :
    finiteMaxLinear A hA (U.mulVec (Uᵀ.mulVec x)) = finiteMaxLinear A hA x := by
  have hall (a : Vec n) (ha : a ∈ A) : dot a (U.mulVec (Uᵀ.mulVec x)) = dot a x := by
    calc
      dot a (U.mulVec (Uᵀ.mulVec x)) = dot (Uᵀ.mulVec a) (Uᵀ.mulVec x) :=
        (AffineProjection.dot_transpose_mulVec U a _).symm
      _ = dot (U.mulVec (Uᵀ.mulVec a)) x := by
        simpa only [Matrix.transpose_transpose] using
          (AffineProjection.dot_transpose_mulVec Uᵀ (Uᵀ.mulVec a) x).symm
      _ = dot a x := by rw [orthonormal_projection_on_range U hU a (hAsub a ha)]
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := finiteMaxLinear_active A hA (U.mulVec (Uᵀ.mulVec x))
    rw [he, hall a ha]
    exact slope_le_finiteMaxLinear A hA ha x
  · obtain ⟨a, ha, he⟩ := finiteMaxLinear_active A hA x
    rw [he, ← hall a ha]
    exact slope_le_finiteMaxLinear A hA ha _

theorem finiteMaxLinear_comp_convex {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (U : Matrix (Fin n) (Fin r) ℝ) :
    ConvexOn ℝ univ (fun z => finiteMaxLinear A hA (U.mulVec z)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [Matrix.mulVec_add, Matrix.mulVec_smul] using
    (finiteMaxLinear_convex A hA).2 (mem_univ (U.mulVec x)) (mem_univ (U.mulVec y)) ha hb hab

end Homogeneous
namespace AdmissibleBFGSRun
open Homogeneous AffineProjection

/-- H.8 for an orthonormal coordinate matrix of the actual full slope span.
The projected coordinate limit is derived from relative interior and H.A;
no iterate, matrix or accepted-length bound is assumed. -/
theorem maxLinear_relativeInterior_convergence {n r : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hri : RelativeInteriorZero A) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hspan : ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x) :
    Tendsto (fun k => Uᵀ.mulVec (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 (fiberPoint Uᵀ (R.H 0) (R.x 0) 0)) := by
  have hAsub (a : Vec n) (ha : a ∈ A) : ∃ z, U.mulVec z = a :=
    (hspan a).mp (Submodule.subset_span ha)
  have hRank := orthonormal_transpose_fullRowRank U hU
  let Fbar : Vec r → ℝ := fun z => finiteMaxLinear A hA (U.mulVec z)
  have hFzero : Fbar 0 = 0 := by
    dsimp only [Fbar]
    rw [Matrix.mulVec_zero, value_zero (finiteMaxLinear_homogeneous A hA)]
  have hmin : ∀ z, Fbar 0 ≤ Fbar z := by
    intro z
    rw [hFzero]
    exact relativeInteriorZero_nonneg A hA hri _
  have huniq : ∀ z, Fbar z = Fbar 0 → z = 0 := by
    intro z he
    by_contra hz
    have hUz : U.mulVec z ≠ 0 := by
      intro hu
      apply hz
      apply hRank
      simpa only [Matrix.transpose_transpose, Matrix.mulVec_zero] using hu
    have hp := relativeInteriorZero_positive_on_span A hA hri (U.mulVec z)
      ((hspan _).mpr ⟨z, rfl⟩) hUz
    change 0 < Fbar z at hp
    rw [he, hFzero] at hp
    exact lt_irrefl 0 hp
  have hv := R.homogeneous_value_zero_of_lower_bound (finiteMaxLinear_homogeneous A hA) 0
    (fun k => relativeInteriorZero_nonneg A hA hri (R.x k))
  have hvbar : Tendsto (fun k => Fbar (Uᵀ.mulVec (R.x k))) atTop (𝓝 (Fbar 0)) := by
    simpa only [Fbar, finiteMaxLinear_projection_eq A hA U hU hAsub, hFzero] using hv
  have hxbar := Localization.tendsto_unique_minimizer_of_values
    (finiteMaxLinear_comp_convex A hA U) 0 hmin huniq hvbar
  refine ⟨hxbar, ?_⟩
  have hg (k : ℕ) : (Uᵀ)ᵀ.mulVec (Uᵀ.mulVec (R.g k)) = R.g k := by
    rw [Matrix.transpose_transpose]
    exact orthonormal_projection_on_range U hU _ (hAsub _ (R.maxLinear_gradient_mem A hA k))
  exact R.affine_limit_lift Uᵀ hRank (fun k => Uᵀ.mulVec (R.g k)) hg 0 hxbar

end AdmissibleBFGSRun
end BfgsVerification

