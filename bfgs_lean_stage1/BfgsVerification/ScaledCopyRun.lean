import BfgsVerification.TranslatedSearch
import BfgsVerification.LScalarTargets

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.ScaledCopy
open LScalarGeometric DeterministicLineSearch

variable {n : ℕ} {Q F : Vec n → ℝ}

/-- Exact objective identities on one fixed open physical chart at every scale.
No orbit or search behavior is included in these geometric data. -/
structure Data (Q F : Vec n → ℝ) (c : Vec n) (C : ℝ) (U : Set (Vec n)) : Prop where
  convex : ConvexOn ℝ univ F
  open_domain : IsOpen U
  model : ∀m : ℕ,∀y∈U,F (scale m • c+scale m • y)=(scale m)^2*(C+Q y)

namespace Data
variable {c : Vec n} {C : ℝ} {U : Set (Vec n)}

theorem model_offset (D : Data Q F c C U) (m : ℕ) (y : Vec n) (hy : y∈U) :
    F (scale m • c+scale m • y)=(scale m)^2*C+(scale m)^2*Q y := by
  rw [D.model m y hy]
  ring

def transferData (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m : ℕ) :
    TranslatedRun.Data R F (scale m • c) (scale m) ((scale m)^2*C) :=
  TranslatedRun.data_of_local_model D.open_domain (scale_pos m).ne' D.convex hx (D.model_offset m)

def run (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m : ℕ) :
    AdmissibleBFGSRun n F := TranslatedRun.run (D.transferData R hx m) (scale_pos m).ne'

theorem run_x (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m k : ℕ) :
    (D.run R hx m).x k=scale m • c+scale m • R.x k := rfl

theorem run_H (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m k : ℕ) :
    (D.run R hx m).H k=R.H k := rfl

theorem run_g (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m k : ℕ) :
    (D.run R hx m).g k=scale m • R.g k := rfl

theorem run_alpha (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m k : ℕ) :
    (D.run R hx m).α k=R.α k := rfl

theorem run_value (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) (m k : ℕ) :
    F ((D.run R hx m).x k)=(scale m)^2*(C+Q (R.x k)) := D.model m _ (hx k)

theorem run_tendsto (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (ht : Tendsto R.x atTop (𝓝 0)) (m : ℕ) :
    Tendsto (D.run R hx m).x atTop (𝓝 (scale m • c)) := by
  simpa only [smul_zero,add_zero] using TranslatedRun.point_tendsto R ht (scale m • c) (scale m)

theorem run_values_tendsto (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (ht : Tendsto (fun k => Q (R.x k)) atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun k => F ((D.run R hx m).x k)) atTop (𝓝 ((scale m)^2*C)) := by
  simpa only [mul_zero,add_zero] using TranslatedRun.value_tendsto (D.transferData R hx m) ht

theorem run_values_above_limit (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (hp : ∀k,0<Q (R.x k)) (m k : ℕ) : (scale m)^2*C<F ((D.run R hx m).x k) := by
  rw [D.run_value R hx m k]
  nlinarith [mul_pos (sq_pos_of_pos (scale_pos m)) (hp k)]

theorem starts_tendsto_zero (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U) :
    Tendsto (fun m => (D.run R hx m).x 0) atTop (𝓝 (0 : Vec n)) := by
  simp_rw [D.run_x R hx]
  simpa only [zero_smul,zero_add] using
    (LScalar.scale_tendsto_zero.smul_const c).add (LScalar.scale_tendsto_zero.smul_const (R.x 0))

theorem search_transfer (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (fuel : ℕ) (hq : ∀k,∀a∈(fromMetric Q (R.x k) (R.H k) R.c₁ R.c₂ fuel).2,
      R.x k+a • bfgsStep (R.H k) (R.g k) 1∈U ∧
      DifferentiableAt ℝ Q (R.x k+a • bfgsStep (R.H k) (R.g k) 1)) (m k : ℕ) :
    fromMetric F ((D.run R hx m).x k) ((D.run R hx m).H k) R.c₁ R.c₂ fuel=
      fromMetric Q (R.x k) (R.H k) R.c₁ R.c₂ fuel :=
  TranslatedRun.local_model_search D.open_domain (scale_pos m).ne' (hx k) (R.hasGradient k) fuel
    (D.model_offset m) (hq k)

theorem query_identity (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (m k : ℕ) (a : ℝ) :
    (D.run R hx m).x k+a • bfgsStep ((D.run R hx m).H k) ((D.run R hx m).g k) 1=
      scale m • c+scale m • (R.x k+a • bfgsStep (R.H k) (R.g k) 1) := by
  rw [D.run_x,D.run_H,D.run_g,bfgsStep_scale_gradient,TranslatedRun.translated_trial]

end Data
end BfgsVerification.ScaledCopy
