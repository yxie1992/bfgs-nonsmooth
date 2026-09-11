import BfgsVerification.HomogeneousLowRankProjection

/-! H.7.1's projected matrix run and line-search scalars use only gradient
membership, even when the original objective does not globally factor through
the subspace. An objective factorization is neither stated nor assumed here. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace FullBFGSRun
open AffineProjection

variable {n r : ℕ} (R : FullBFGSRun n) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (gbar : ℕ → Vec r) (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g k)

include hg

theorem subspace_step (k : ℕ) :
    A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) =
      bfgsStep (compress A (R.H k)) (gbar k) (R.α k) := by
  rw [← hg k]
  exact project_step A _ _ _

theorem subspace_curvature (k : ℕ) :
    dot (gbar (k+1)-gbar k) (bfgsStep (compress A (R.H k)) (gbar k) (R.α k)) =
      dot (R.g (k+1)-R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) := by
  rw [← R.subspace_step A gbar hg k, ← dot_transpose_mulVec, Matrix.mulVec_sub, hg, hg]

def projectSubspace : FullBFGSRun r where
  H k := compress A (R.H k)
  g := gbar
  α := R.α
  positive_definite k := compress_posDef A hA (R.positive_definite k)
  alpha_pos := R.alpha_pos
  energy_pos k := by
    rw [← project_energy, hg]
    exact R.energy_pos k
  curvature_pos k := by
    rw [R.subspace_curvature A gbar hg]
    exact R.curvature_pos k
  update k := by
    rw [R.update]
    have hy : R.g (k+1)-R.g k = Aᵀ.mulVec (gbar (k+1)-gbar k) := by
      rw [Matrix.mulVec_sub, hg, hg]
    rw [hy, inverseBFGS_compress, R.subspace_step A gbar hg]

@[simp] theorem projectSubspace_q (k : ℕ) : (R.projectSubspace A hA gbar hg).q k = R.q k := by
  change metricEnergy (compress A (R.H k)) (gbar k) = R.q k
  rw [← project_energy, hg]
  rfl

@[simp] theorem projectSubspace_d (k : ℕ) : (R.projectSubspace A hA gbar hg).d k = R.d k := by
  simp only [FullBFGSRun.d, projectSubspace_q]
  rfl

end FullBFGSRun
namespace AdmissibleBFGSRun
open AffineProjection

/-- Source H.7.1's actual projected step and both line-search inequalities.
Original accepted values are retained exactly, with no global factorization
premise for the original objective. The compressed inverse matrix is SPD. -/
theorem projected_subspace_accepted_identities {n r : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (gbar : ℕ → Vec r) (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g k) (k : ℕ) :
    (compress A (R.H k)).PosDef ∧
    A.mulVec (R.x (k+1)) = A.mulVec (R.x k) + bfgsStep (compress A (R.H k)) (gbar k) (R.α k) ∧
    F (R.x (k+1)) ≤ F (R.x k) + R.c₁ * dot (gbar k) (bfgsStep (compress A (R.H k)) (gbar k) (R.α k)) ∧
    R.c₂ * dot (gbar k) (bfgsStep (compress A (R.H k)) (gbar k) (R.α k)) ≤
      dot (gbar (k+1)) (bfgsStep (compress A (R.H k)) (gbar k) (R.α k)) := by
  have hs := R.toFullBFGSRun.subspace_step A gbar hg k
  change A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) =
    bfgsStep (compress A (R.H k)) (gbar k) (R.α k) at hs
  refine ⟨compress_posDef A hA (R.positive_definite k), ?_, ?_, ?_⟩
  · rw [R.step, Matrix.mulVec_add, hs]
  · have h := R.armijo k
    rw [← hg k, dot_transpose_mulVec] at h
    simpa only [project_step] using h
  · have h := R.weak_wolfe k
    rw [← hg k, ← hg (k+1), dot_transpose_mulVec, dot_transpose_mulVec] at h
    simpa only [project_step] using h

end AdmissibleBFGSRun
end BfgsVerification
