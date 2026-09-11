import BfgsVerification.PlanarQuadraticConvergence
import BfgsVerification.NormalSpikeObjective
import BfgsVerification.HessianUpdate

noncomputable section
open scoped Topology
open Filter Matrix
namespace BfgsVerification
namespace EReconstruction
open BfgsVerification

theorem eventually_below_tolerance (f : ℕ → ℝ)
    (hf : Tendsto f atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ k ≥ N, f k < ε := by
  have h : ∀ᶠ k in atTop, f k < ε := hf.eventually (gt_mem_nhds hε)
  exact eventually_atTop.1 h

theorem planar_eventual_printed_tolerance
    (R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective)
    (hstart : PlanarQuadraticExample.objective (R.x 0) < 1/100) :
    ∃ N, ∀ k ≥ N, PlanarQuadraticExample.objective (R.x k) < (10 : ℝ)^(-45 : ℤ) := by
  exact eventually_below_tolerance _
    (PlanarQuadraticExample.fullBFGS_explicit_basin R hstart).1 (zpow_pos (by norm_num) _)

theorem spike_eventual_printed_tolerance {n : ℕ} (a : Vec n) (ha : sqNorm a = 1)
    (R : AdmissibleBFGSRun n (NormalSpike.objective a)) :
    ∃ N, ∀ k ≥ N, NormalSpike.objective a (R.x k) < (10 : ℝ)^(-28 : ℤ) := by
  exact eventually_below_tolerance _
    (NormalSpike.objective_fullBFGS_convergence a ha R).1 (zpow_pos (by norm_num) _)

theorem inverse_update_secant {n : ℕ} (H : Mat n) (s y : Vec n)
    (ht : dot y s ≠ 0) : (inverseBFGS H s y).mulVec y = s := by
  have hsy : dot s y = dot y s := by simp [dot, mul_comm]
  have hz : ((1 : Mat n) - (dot y s)⁻¹ • outer y s).mulVec y = 0 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, hsy,
      smul_smul, ht]
  simp only [inverseBFGS, Matrix.add_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, hsy, smul_smul, inv_mul_cancel₀ ht, one_smul]
  suffices ((1 - (dot y s)⁻¹ • outer s y) * H * (1 - (dot y s)⁻¹ • outer y s)).mulVec y = 0 by simp [this]
  rw [← Matrix.mulVec_mulVec, hz]
  simp

theorem hessian_update_secant {n : ℕ} {H : Mat n} (hH : H.PosDef)
    (s y : Vec n) (ht : 0 < dot y s) :
    ((inverseBFGS H s y)⁻¹).mulVec s = y := by
  simpa only [inverse_update_secant H s y ht.ne'] using
    inverse_mul_mulVec (inverseBFGS_posDef hH s y ht) y

end EReconstruction
end BfgsVerification

namespace BfgsVerification
namespace EReconstruction
open BfgsVerification

/-- Exact theorem counterparts for the source secant checks and two printed
positive tolerances. This makes no assertion about numerical runs or their cost. -/
def ReconstructedFactsTarget : Prop :=
  (∀ (n : ℕ) (H : Mat n) (s y : Vec n), dot y s ≠ 0 →
    (inverseBFGS H s y).mulVec y = s) ∧
  (∀ (n : ℕ) (H : Mat n), H.PosDef → ∀ (s y : Vec n), 0 < dot y s →
    ((inverseBFGS H s y)⁻¹).mulVec s = y) ∧
  (∀ (R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective),
    PlanarQuadraticExample.objective (R.x 0) < 1/100 →
    ∃ N, ∀ k ≥ N, PlanarQuadraticExample.objective (R.x k) < (10 : ℝ)^(-45 : ℤ)) ∧
  (∀ (n : ℕ) (a : Vec n), sqNorm a = 1 →
    ∀ (R : AdmissibleBFGSRun n (NormalSpike.objective a)),
    ∃ N, ∀ k ≥ N, NormalSpike.objective a (R.x k) < (10 : ℝ)^(-28 : ℤ))

theorem reconstructedFacts : ReconstructedFactsTarget :=
  ⟨fun _ H s y ht => inverse_update_secant H s y ht,
   fun _ _ hH s y ht => hessian_update_secant hH s y ht,
   planar_eventual_printed_tolerance,
   fun _ a ha R => spike_eventual_printed_tolerance a ha R⟩

end EReconstruction
end BfgsVerification
