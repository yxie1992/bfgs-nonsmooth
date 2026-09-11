import BfgsVerification.LScalarSmallBounds

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
open LScalarGeometric

def LScalarRampTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  LScalarRamp.epsilon < LScalarRamp.center b ∧ LScalarRamp.center b < 1-LScalarRamp.epsilon ∧
  (∫ x in (0 : ℝ)..1, LScalarRamp.ramp b x) = 1-LScalarRamp.center b ∧
  (∀ x, LScalarRamp.primitive b x = ∫ t in (0 : ℝ)..x, LScalarRamp.ramp b t) ∧
  (∀ x, HasDerivAt (LScalarRamp.ramp b) (LScalarRamp.rampDerivative b x) x ∧
    0 ≤ LScalarRamp.rampDerivative b x ∧ LScalarRamp.rampDerivative b x ≤ 768) ∧
  1/2 < LScalarRamp.lowerLength b ∧ 1/2 < LScalarRamp.upperLength b

theorem lScalarRamp : LScalarRampTarget := by
  intro b hl hr
  exact ⟨(LScalarRamp.center_bounds hl hr).1, (LScalarRamp.center_bounds hl hr).2,
    LScalarRamp.integral_ramp hl hr, LScalarRamp.primitive_eq_integral hl hr,
    fun x => ⟨LScalarRamp.ramp_hasDerivAt b x, LScalarRamp.rampDerivative_bounds b x⟩,
    LScalarRamp.plateau_lengths hl hr⟩

def LScalarDefinitionTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  LScalar.phi b 0 = 0 ∧ (∀ x, x < 0 → LScalar.phi b x = x^2/2) ∧
  (∀ x, b ≤ x → LScalar.phi b x = 1+x-b) ∧
  ∀ n : ℕ, ∀ x : ℝ, b*theta*scale n ≤ x → x ≤ b*scale n →
    LScalar.phi b x = (theta*scale n)^2+b*(scale n)^2*(1-theta)*
      (theta*coordinate b (scale n) x+(1-theta)*LScalarRamp.primitive b (coordinate b (scale n) x))

theorem lScalarDefinition : LScalarDefinitionTarget := by
  intro b hl hr
  exact ⟨LScalar.phi_zero hl hr, fun x hx => LScalar.phi_eq_negative hl hr hx.le,
    fun x hx => LScalar.phi_eq_outer hl hr hx, fun n x => LScalar.phi_interval hl hr n⟩

def LScalarRegularityTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  ConvexOn ℝ univ (LScalar.phi b) ∧ (∀ x, 0 ≤ LScalar.phi b x) ∧
  Tendsto (LScalar.phi b) (cocompact ℝ) atTop ∧
  ((∀ x, LScalar.phi b 0 ≤ LScalar.phi b x) ∧
    (∀ x, LScalar.phi b x = LScalar.phi b 0 → x = 0)) ∧
  ContDiff ℝ 1 (LScalar.phi b) ∧
  (∃ K : NNReal, LipschitzWith K (deriv (LScalar.phi b))) ∧
  (∀ x, 0 < x → ContDiffAt ℝ 2 (LScalar.phi b) x) ∧
  (∀ x, x < 0 → ContDiffAt ℝ 2 (LScalar.phi b) x) ∧
  ¬DifferentiableAt ℝ (deriv (LScalar.phi b)) 0 ∧
  ∀ x a : ℝ, HasDerivAt (deriv (LScalar.phi b)) a x → 0 ≤ a ∧ a ≤ max 1 (768/b)

theorem lScalarRegularity : LScalarRegularityTarget := by
  intro b hl hr
  exact ⟨LScalar.phi_convex hl hr, LScalar.phi_nonnegative hl hr, LScalar.phi_coercive hl hr,
    LScalar.phi_unique_minimizer hl hr, LScalar.phi_contDiff hl hr,
    ⟨_,LScalar.phi_derivative_lipschitz hl hr⟩,
    fun x hx => LScalar.phi_contDiffAt_pos hl hr hx,
    fun x hx => LScalar.phi_contDiffAt_neg hl hr hx,
    LScalar.phi_not_twice_differentiable_zero hl hr,
    fun x a ha => LScalar.phi_second_derivative_bounds hl hr ha⟩

def LScalarNodeTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 → ∀ n : ℕ,
  LScalar.phi b (b*scale n) = (scale n)^2 ∧
  HasDerivAt (LScalar.phi b) (scale n) (b*scale n) ∧
  HasDerivAt (deriv (LScalar.phi b)) 0 (b*scale n) ∧
  ∀ h : ℝ, |h| ≤ scale n/2 → LScalar.phi b (b*scale n+h) = (scale n)^2+scale n*h

theorem lScalarNodes : LScalarNodeTarget := by
  intro b hl hr n
  exact ⟨LScalar.phi_node hl hr n, LScalar.phi_node_hasDerivAt hl hr n,
    LScalar.phi_node_second_hasDerivAt hl hr n, fun h hh => LScalar.phi_plateau hl hr n hh⟩

def LScalarPeaksTarget : Prop := ∀ b : ℝ, 17/10 ≤ b → b ≤ 34 →
  Tendsto (LScalar.peak b) atTop (𝓝 0) ∧
  (∀ n, 0 < LScalar.peak b n ∧ HasDerivAt (deriv (LScalar.phi b)) (768/b) (LScalar.peak b n)) ∧
  (0 < 768/b ∧ ¬Tendsto (fun n => deriv (deriv (LScalar.phi b)) (LScalar.peak b n)) atTop (𝓝 0)) ∧
  ∀ n, deriv (LScalar.phi b) (b*scale n)/(b*scale n) = 1/b ∧
    deriv (LScalar.phi b) ((b+1/4)*scale n)/((b+1/4)*scale n) = 1/(b+1/4)

theorem lScalarPeaks : LScalarPeaksTarget := by
  intro b hl hr
  exact ⟨LScalar.peak_tendsto_zero b,
    fun n => ⟨LScalar.peak_positive hl hr n,LScalar.phi_peak_second_hasDerivAt hl hr n⟩,
    ⟨(LScalar.peak_curvature_nonvanishing hl hr).1,(LScalar.peak_curvature_nonvanishing hl hr).2.2⟩,
    fun n => ⟨LScalar.derivative_ratio_on_nodes hl hr n,LScalar.derivative_ratio_on_shifted_nodes hl hr n⟩⟩

end BfgsVerification
