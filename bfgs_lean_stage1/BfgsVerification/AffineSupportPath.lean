import BfgsVerification.AffineCriticalObjective
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The ordinary calculus in Module A's affine-critical path argument.
These declarations use actual global supporting vectors and actual derivatives
of a path and its objective composition. They do not assume differentiability
of the objective at the path point, or assert semialgebraic path existence. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Set Filter

namespace BfgsVerification
namespace AffineSupportPath
open AffineCriticalObjective ConvexSubdifferential AffineCriticalGeometry

/-- Every actual support has the same pairing with the derivative of a path
whenever the objective composition has a two-sided derivative. -/
theorem supporting_path_derivative_eq {n : ℕ} {F : Vec n → ℝ}
    {p : ℝ → Vec n} {t a : ℝ} {v g : Vec n}
    (hg : Homogeneous.Supports F (p t) g)
    (hp : HasDerivAt p v t) (hFp : HasDerivAt (F ∘ p) a t) :
    dot g v = a := by
  have hlin : HasDerivAt (fun u => dot g (p u - p t)) (dot g v) t := by
    simpa only [Function.comp_def, gradientFunctional_apply] using
      (gradientFunctional g).hasFDerivAt.comp_hasDerivAt t (hp.sub_const (p t))
  have hm : IsLocalMin (fun u => F (p u) - dot g (p u - p t)) t := by
    apply Eventually.of_forall
    intro u
    have hs := hg (p u)
    have hz : dot g 0 = 0 := by simp [dot]
    simp only [sub_self, hz, sub_zero]
    linarith
  have he := hm.hasDerivAt_eq_zero (hFp.sub hlin)
  linarith

/-- Affine zero forces the actual derivative of the objective composition to
vanish. No subgradient selection is made and no objective derivative is assumed. -/
theorem derivative_zero_of_affineCritical {n : ℕ} {F : Vec n → ℝ}
    {p : ℝ → Vec n} {t a : ℝ} {v : Vec n}
    (hc : IsAffineCritical F (p t))
    (hp : HasDerivAt p v t) (hFp : HasDerivAt (F ∘ p) a t) : a = 0 := by
  have h := affine_pairing_of_constant (subgradientFamily F (p t))
    (euclideanVector v) a (fun g => by
      change ⟪euclideanVector g.val, euclideanVector v⟫_ℝ = a
      rw [euclidean_pairing_eq_dot]
      exact supporting_path_derivative_eq g.property hp hFp) 0 hc
  simpa only [inner_zero_left] using h.symm

theorem hasDerivAt_zero_of_affineCritical {n : ℕ} {F : Vec n → ℝ}
    {p : ℝ → Vec n} {t : ℝ}
    (hc : IsAffineCritical F (p t)) (hp : DifferentiableAt ℝ p t)
    (hFp : DifferentiableAt ℝ (F ∘ p) t) : HasDerivAt (F ∘ p) 0 t := by
  have he := derivative_zero_of_affineCritical hc hp.hasDerivAt hFp.hasDerivAt
  exact he ▸ hFp.hasDerivAt

end AffineSupportPath
end BfgsVerification
