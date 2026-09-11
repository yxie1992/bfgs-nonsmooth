import BfgsVerification.HomogeneousPlanarFiniteValue
import BfgsVerification.HomogeneousRelativeInteriorBounds

/-! The actual finite maximum descends through full slope-span coordinates.
Only the restricted recurrent objective is projected in the tail application. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

def projectedSlopes {n r : ℕ} (A : Finset (Vec n)) (U : Matrix (Fin n) (Fin r) ℝ) : Finset (Vec r) :=
  A.image Uᵀ.mulVec

theorem projectedSlopes_nonempty {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (U : Matrix (Fin n) (Fin r) ℝ) : (projectedSlopes A U).Nonempty := hA.image _

theorem finiteMaxLinear_projected_value {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (U : Matrix (Fin n) (Fin r) ℝ) (z : Vec r) :
    finiteMaxLinear (projectedSlopes A U) (projectedSlopes_nonempty A hA U) z =
      finiteMaxLinear A hA (U.mulVec z) := by
  apply le_antisymm
  · obtain ⟨b, hb, he⟩ := finiteMaxLinear_active (projectedSlopes A U) (projectedSlopes_nonempty A hA U) z
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    rw [he, AffineProjection.dot_transpose_mulVec]
    exact slope_le_finiteMaxLinear A hA ha _
  · obtain ⟨a, ha, he⟩ := finiteMaxLinear_active A hA (U.mulVec z)
    rw [he, ← AffineProjection.dot_transpose_mulVec]
    exact slope_le_finiteMaxLinear _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩) z

theorem finiteMaxLinear_projected_factorization {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ*U = 1)
    (hAsub : ∀ a ∈ A, ∃ z, U.mulVec z = a) :
    finiteMaxLinear A hA = (fun x =>
      finiteMaxLinear (projectedSlopes A U) (projectedSlopes_nonempty A hA U) (Uᵀ.mulVec x)) := by
  funext x
  rw [finiteMaxLinear_projected_value, finiteMaxLinear_projection_eq A hA U hU hAsub]

/-- Orthonormal coordinates with their exact dimension, so the recurrent
finrank hypothesis determines the dimension of the actual projected run. -/
theorem exists_slope_span_coordinates_exact {n : ℕ} (A : Finset (Vec n)) :
    ∃ (r : ℕ) (U : Matrix (Fin n) (Fin r) ℝ),
      r = Module.finrank ℝ (Submodule.span ℝ (A : Set (Vec n))) ∧ Uᵀ * U = 1 ∧
      ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x := by
  let S := Submodule.span ℝ (A : Set (Vec n))
  let e := (WithLp.linearEquiv 2 ℝ (Vec n)).symm
  let SE := S.map e.toLinearMap
  obtain ⟨U, hU, hspan⟩ := FrameNorms.orthonormal_matrix_for_subspace SE
  refine ⟨Module.finrank ℝ SE, U, LinearEquiv.finrank_map_eq e S, hU, ?_⟩
  intro x
  have hm : euclideanVector x ∈ SE ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, he⟩
      have hxy : y = x := e.injective he
      simpa only [hxy] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact hm.symm.trans (hspan (euclideanVector x))

end Homogeneous
namespace AdmissibleBFGSRun
open Homogeneous AffineProjection HomogeneousBlock

/-- Change only the written expression of an equal objective; all actual run
fields remain definitionally equal. -/
def congrObjective {n : ℕ} {F G : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (hFG : F = G) :
    AdmissibleBFGSRun n G where
  convex := by simpa only [← hFG] using R.convex
  x := R.x
  H := R.H
  g := R.g
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := R.initial_posDef
  alpha_pos := R.alpha_pos
  gradient_nonzero := R.gradient_nonzero
  hasGradient k := by simpa only [← hFG] using R.hasGradient k
  step := R.step
  update := R.update
  armijo k := by simpa only [← hFG] using R.armijo k
  weak_wolfe := R.weak_wolfe

/-- The planar theorem and the actual fixed-line theorem cover every nonzero
run dimension at most two; dimension zero is excluded by nonzero gradients. -/
theorem maxLinear_dimension_le_two_zero_branch {r : ℕ} (A : Finset (Vec r)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun r (finiteMaxLinear A hA)) (hr : r ≤ 2)
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    ∃ xstar : Vec r, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  have hrpos := R.dimension_pos
  have hcases : r = 1 ∨ r = 2 := by omega
  rcases hcases with rfl | rfl
  · let a : Vec 1 := fun _ => 1
    have ha : a ≠ 0 := by intro h; have h0 := congrFun h 0; norm_num [a] at h0
    have hg (k : ℕ) : ∃ c : ℝ, R.g k = c • a := by
      refine ⟨R.g k 0, ?_⟩
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [hi, a]
    have hx := R.maxLinear_fixed_line_convergence A hA a ha hg hv
    exact ⟨_, hx, tendsto_nhds_unique ((convex_continuous R.convex).tendsto _ |>.comp hx) hv⟩
  · exact R.maxLinear_planar_zero_branch_has_limit A hA hv

/-- H.7.4 after genuine projection to a full slope span of dimension at most
two. Every projected derivative and full-BFGS update is obtained from the
actual objective; no projected recurrence or convergence is assumed. -/
theorem maxLinear_span_coordinates_le_two_convergence {n r : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ*U = 1) (hr : r ≤ 2)
    (hAsub : ∀ a ∈ A, ∃ z, U.mulVec z = a)
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  let B := projectedSlopes A U
  have hB : B.Nonempty := projectedSlopes_nonempty A hA U
  have he := finiteMaxLinear_projected_factorization A hA U hU hAsub
  let Q := R.congrObjective he
  let P := projectRun Uᵀ (orthonormal_transpose_fullRowRank U hU) (finiteMaxLinear B hB) Q
  have hvP : Tendsto (fun k => finiteMaxLinear B hB (P.x k)) atTop (𝓝 0) := by
    have hv0 : Tendsto (fun k => finiteMaxLinear B hB (Uᵀ.mulVec (R.x k))) atTop (𝓝 0) := by
      simpa only [he] using hv
    exact hv0
  obtain ⟨zstar, hz, _⟩ := P.maxLinear_dimension_le_two_zero_branch B hB hr hvP
  have hg (k : ℕ) : (Uᵀ)ᵀ.mulVec (Uᵀ.mulVec (R.g k)) = R.g k := by
    rw [Matrix.transpose_transpose]
    exact orthonormal_projection_on_range U hU _ (hAsub _ (R.maxLinear_gradient_mem A hA k))
  have hx := R.affine_limit_lift Uᵀ (orthonormal_transpose_fullRowRank U hU)
    (fun k => Uᵀ.mulVec (R.g k)) hg zstar hz
  exact ⟨_, hx, tendsto_nhds_unique ((convex_continuous R.convex).tendsto _ |>.comp hx) hv⟩

end AdmissibleBFGSRun
end BfgsVerification
