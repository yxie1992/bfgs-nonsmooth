import BfgsVerification.HomogeneousPlanarAlgebra
import BfgsVerification.FrameNorms

/-! Actual homogeneous endpoint pairings and the finite-max planar H.C branch.
Every accepted slope and endpoint identity is derived from the objective run. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Strict-curvature accepted transitions cannot leave the gradient unchanged. -/
theorem gradient_transition_ne (k : ℕ) : R.g k ≠ R.g (k + 1) := by
  intro he
  have ht := R.curvature_pos k
  rw [← he, sub_self] at ht
  simp [dot] at ht

theorem homogeneous_old_endpoint_pairing (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    dot (R.g k) (R.x (k + 1)) = F (R.x k) - R.d k := by
  rw [R.step]
  change R.g k ⬝ᵥ (R.x k + bfgsStep (R.H k) (R.g k) (R.α k)) = _
  rw [dotProduct_add]
  change dot (R.g k) (R.x k) + dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) = _
  rw [R.homogeneous_euler hF k, R.dot_step_eq_neg_d]
  ring

/-- H.7.3's two actual endpoint pairings vanish on the zero-value branch. -/
theorem homogeneous_endpoint_pairings_tendsto_zero (hF : Homogeneous.PositiveDegreeOne F)
    (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0)) :
    Tendsto (fun k => dot (R.g k) (R.x (k + 1))) atTop (𝓝 0) ∧
      Tendsto (fun k => dot (R.g (k + 1)) (R.x (k + 1))) atTop (𝓝 0) := by
  have hd := (R.summable_predicted_decreases_of_value_limit 0 hv).tendsto_atTop_zero
  constructor
  · simpa only [R.homogeneous_old_endpoint_pairing hF, sub_zero] using hv.sub hd
  · simpa only [R.homogeneous_euler hF] using hv.comp (tendsto_add_atTop_nat 1)

/-- Endpoints of any sequence of independent accepted transitions converge to
zero, with no bounded-run assumption and no bound on intervals between them. -/
theorem maxLinear_independent_anchors_tendsto_zero (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA))
    (hv : Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0))
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (hind : ∀ k, HomogeneousPlanar.pairDet (R.g (j k)) (R.g (j k + 1)) ≠ 0) :
    Tendsto (fun k => R.x (j k + 1)) atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := R.homogeneous_endpoint_pairings_tendsto_zero
    (Homogeneous.finiteMaxLinear_homogeneous A hA) hv
  exact HomogeneousPlanar.endpoints_tendsto_zero A
    (fun k => R.g (j k)) (fun k => R.g (j k + 1)) (fun k => R.x (j k + 1))
    (fun k => R.maxLinear_gradient_mem A hA (j k))
    (fun k => R.maxLinear_gradient_mem A hA (j k + 1)) hind (h1.comp hj) (h2.comp hj)

/-- On the positive branch, a negative objective direction forces every planar
accepted transition to be independent. Actual finite-max gradients are derived. -/
theorem maxLinear_planar_transition_independent (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA))
    (w : Vec 2) (hw : Homogeneous.finiteMaxLinear A hA w < 0)
    (hv : ∀ k, 0 < Homogeneous.finiteMaxLinear A hA (R.x k)) (k : ℕ) :
    HomogeneousPlanar.pairDet (R.g k) (R.g (k + 1)) ≠ 0 := by
  let hh := Homogeneous.finiteMaxLinear_homogeneous A hA
  apply HomogeneousPlanar.pairDet_ne_zero_of_supports (R.g k) (R.g (k + 1))
    (R.x k) (R.x (k + 1)) w
  · simpa only [R.homogeneous_euler hh] using hv k
  · simpa only [R.homogeneous_euler hh] using hv (k + 1)
  · simpa only [R.homogeneous_euler hh] using R.homogeneous_support hh (k + 1) (R.x k)
  · simpa only [R.homogeneous_euler hh] using R.homogeneous_support hh k (R.x (k + 1))
  · exact (R.homogeneous_support hh k w).trans_lt hw
  · exact (R.homogeneous_support hh (k + 1) w).trans_lt hw
  · exact R.gradient_transition_ne k

/-- The noncompact, globally unbounded-below planar zero-value branch converges
in points to zero. A single negative direction is equivalent to unboundedness
below for the proved positively homogeneous finite maximum. -/
theorem maxLinear_planar_zero_branch_iterates (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA))
    (w : Vec 2) (hw : Homogeneous.finiteMaxLinear A hA w < 0)
    (hv : Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    Tendsto R.x atTop (𝓝 0) := by
  have hp := R.homogeneous_finite_branch_positive (Homogeneous.finiteMaxLinear_homogeneous A hA) 0 hv
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact R.maxLinear_independent_anchors_tendsto_zero A hA hv id tendsto_id
    (R.maxLinear_planar_transition_independent A hA w hw hp)

end AdmissibleBFGSRun
end BfgsVerification
