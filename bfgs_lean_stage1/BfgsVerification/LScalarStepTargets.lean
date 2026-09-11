import BfgsVerification.LScalarStepLocal
import BfgsVerification.LScalarStepRamp

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
open LScalarGeometric

def LScalarStepDefinitionTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  (∀ x, LScalarStep.primitive b x = ∫ t in (0 : ℝ)..x, LScalarStep.ramp b t) ∧
  LScalarStep.phi b 0 = 0 ∧ (∀ x, x < 0 → LScalarStep.phi b x = -x) ∧
  (∀ x, b ≤ x → LScalarStep.phi b x = 1+x-b) ∧
  ∀ n : ℕ, ∀ x : ℝ, b*theta*scale n ≤ x → x ≤ b*scale n →
    LScalarStep.phi b x = (theta*scale n)^2+b*(scale n)^2*(1-theta)*
      (theta*coordinate b (scale n) x+(1-theta)*LScalarStep.primitive b (coordinate b (scale n) x))

theorem lScalarStepDefinition : LScalarStepDefinitionTarget := by
  intro b hl hr
  refine ⟨LScalarStep.primitive_eq_integral hl hr, LScalarStep.phi_zero hl hr,
    fun x hx => LScalarStep.phi_eq_negative hl hr hx.le,
    fun x hx => LScalarStep.phi_eq_outer hl hr hx, ?_⟩
  intro n x hlo hhi
  have hx : 0 ≤ x := (mul_pos (mul_pos (by linarith : 0 < b) theta_pos) (scale_pos n)).le.trans hlo
  rw [LScalarStep.phi_eq_positive hx]
  simpa only [pow_one] using LScalarStep.positivePart_interval hl hr n hlo hhi

def LScalarStepGeometryTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  ConvexOn ℝ univ (LScalarStep.phi b) ∧ Continuous (LScalarStep.phi b) ∧
  (∀ x, 0 ≤ LScalarStep.phi b x) ∧ Tendsto (LScalarStep.phi b) (cocompact ℝ) atTop ∧
  ((∀ x, LScalarStep.phi b 0 ≤ LScalarStep.phi b x) ∧
    (∀ x, LScalarStep.phi b x = LScalarStep.phi b 0 → x = 0)) ∧
  ∀ x, IsGreatest (range (fun i => LScalarStep.affineFamily b i x)) (LScalarStep.phi b x)

theorem lScalarStepGeometry : LScalarStepGeometryTarget := by
  intro b hl hr
  exact ⟨LScalarStep.phi_convex hl hr, LScalarStep.phi_continuous hl hr,
    LScalarStep.phi_nonnegative b, LScalarStep.phi_coercive hl hr,
    LScalarStep.phi_unique_minimizer hl hr, LScalarStep.phi_countable_max hl hr⟩

def LScalarStepNodeTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 → ∀ n : ℕ,
  LScalarStep.phi b (b*scale n) = (scale n)^2 ∧
  HasDerivAt (LScalarStep.phi b) (scale n) (b*scale n) ∧
  ∀ h : ℝ, |h| ≤ scale n/2 → LScalarStep.phi b (b*scale n+h) = (scale n)^2+scale n*h

theorem lScalarStepNodes : LScalarStepNodeTarget := by
  intro b hl hr n
  exact ⟨LScalarStep.phi_node hl hr n,LScalarStep.phi_node_hasDerivAt hl hr n,
    fun h hh => LScalarStep.phi_plateau hl hr n hh⟩

def LScalarStepLocalTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  (∀ x : ℝ, x ≠ 0 → LScalarStep.BinaryAffineGerm (LScalarStep.phi b) x) ∧
  ¬DifferentiableAt ℝ (LScalarStep.phi b) 0 ∧
  ∀ x : ℝ, DifferentiableAt ℝ (LScalarStep.phi b) x →
    LScalarStep.AffineGerm (LScalarStep.phi b) x ∧
    HasDerivAt (deriv (LScalarStep.phi b)) 0 x ∧
    ∀ N : WithTop ℕ∞, ContDiffAt ℝ N (LScalarStep.phi b) x

theorem lScalarStepLocal : LScalarStepLocalTarget := by
  intro b hl hr
  refine ⟨fun x hx => LScalarStep.phi_binary_affine_of_ne_zero hl hr hx,
    LScalarStep.phi_not_differentiable_zero hl hr, ?_⟩
  intro x hd
  exact ⟨LScalarStep.phi_affine_at_differentiable hl hr hd,
    LScalarStep.phi_second_zero_at_differentiable hl hr hd,
    LScalarStep.phi_contDiffAt_differentiable hl hr hd⟩

end BfgsVerification
