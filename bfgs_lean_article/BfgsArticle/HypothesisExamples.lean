import BfgsVerification.QuadraticGaugeConvex
import BfgsVerification.CertificateGeometry
import BfgsVerification.TransportedCertificateVariants
import BfgsVerification.FrameNorms
import BfgsVerification.OptimizerInterceptExamples

/-!
# Joint hypothesis checks and initialization examples

The quadratic calibration and the mixed ridge have explicit band certificates
and actual infinite full-BFGS runs. The max-linear gauge has all the homogeneous
objective hypotheses but a differentiable identity-metric start with no
differentiable weak-Wolfe first step.

`Vec n` has the finite-Pi topology. Euclidean quadratic quantities are expressed
with `sqNorm`, and `Quadratic.objective_euclidean` makes that convention explicit.
The library's `BandCertificate` stores a real `C`; the parameter and joint
witness theorems additionally assert `0 ≤ C`, as required in the article.
-/

noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology

namespace BfgsVerification.HypothesisExamples

namespace Quadratic

variable {n : ℕ}

def objective (x : Vec n) : ℝ := sqNorm x / 2

theorem dot_self (x : Vec n) : dot x x = sqNorm x := by
  simp only [dot, sqNorm, pow_two]

theorem identity_energy (x : Vec n) : metricEnergy (1 : Mat n) x = sqNorm x := by
  simp only [metricEnergy, Matrix.one_mulVec, dot_self]

theorem objective_euclidean (x : Vec n) :
    objective x = ‖euclideanVector x‖ ^ 2 / 2 := by
  rw [FrameNorms.euclidean_norm_sq]
  rfl

theorem objective_convex : ConvexOn ℝ univ (@objective n) := by
  simpa only [objective, identity_energy] using
    QuadraticGauge.quadratic_convex (1 : Mat n) Matrix.PosSemidef.one

theorem objective_hasGradient (x : Vec n) :
    HasFDerivAt objective (gradientFunctional x) x := by
  simpa only [objective, identity_energy, Matrix.one_mulVec] using
    QuadraticGauge.quadratic_hasGradient (1 : Mat n)
      (by simp [Matrix.IsSymm]) x

theorem gradient_eq {x g : Vec n}
    (hg : HasFDerivAt objective (gradientFunctional g) x) : g = x :=
  AffineProjection.gradientFunctional_injective (hg.unique (objective_hasGradient x))

theorem objective_zero : objective (0 : Vec n) = 0 := by simp [objective, sqNorm]

theorem objective_nonneg (x : Vec n) : 0 ≤ objective x :=
  div_nonneg (sqNorm_nonneg x) (by norm_num)

theorem objective_eq_zero_iff (x : Vec n) : objective x = 0 ↔ x = 0 := by
  simp only [objective, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
  exact CertificateGeometry.sqNorm_eq_zero_iff x

theorem objective_pos {x : Vec n} (hx : x ≠ 0) : 0 < objective x :=
  lt_of_le_of_ne (objective_nonneg x) (fun h => hx ((objective_eq_zero_iff x).mp h.symm))

theorem objective_minimum : IsLeast (Set.range (@objective n)) 0 :=
  ⟨⟨0, objective_zero⟩, by rintro _ ⟨x, rfl⟩; exact objective_nonneg x⟩

theorem sublevel_compact (b : ℝ) : IsCompact {x : Vec n | objective x ≤ b} :=
  Localization.sublevel_compact objective_convex 0
    (fun x => by rw [objective_zero]; exact objective_nonneg x)
    (fun x hx => (objective_eq_zero_iff x).mp (hx.trans objective_zero)) b

/-- The constant identity certificate works for every positive band and every pair of constants. -/
def certificate (K : Set (Vec n)) (c₁ c₂ η : ℝ) (hη : 0 < η) :
    TransportedCertificate.BandCertificate objective K 0 c₁ c₂ η where
  W := fun _ => 1
  m := 2 * η
  C := 1
  L := 0
  δ := 1
  m_pos := by positivity
  L_nonneg := le_rfl
  delta_pos := one_pos
  positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
  visibility := fun x hx g hg => by
    rw [gradient_eq hg, identity_energy]
    have hb := hx.2
    change 0 + η ≤ sqNorm x / 2 at hb
    linarith
  secant := fun x z g h _ _ hp _ => by
    rw [gradient_eq hp.gradient_x, gradient_eq hp.gradient_z, identity_energy]
    simp only [TransportedCertificate.pairCurvature, TransportedCertificate.pairStep,
      one_mul, dot_self, le_refl]
  transport := fun _ _ _ _ _ _ _ _ => by
    simpa using (Matrix.PosSemidef.zero : (0 : Mat n).PosSemidef)

theorem certificate_parameters (K : Set (Vec n)) (c₁ c₂ η : ℝ) (hη : 0 < η) :
    let B := certificate K c₁ c₂ η hη
    B.W = (fun _ => 1) ∧ B.m = 2 * η ∧ B.C = 1 ∧ B.L = 0 ∧ B.δ = 1 ∧
      0 ≤ B.C ∧ ∀ x, (B.W x).PosDef ∧ (B.W x).rank = n := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, zero_le_one,
    fun _ => ⟨Matrix.PosDef.one, ?_⟩⟩
  simp [certificate]

/-- Secant control and projected transport are equalities for all endpoint pairs. -/
theorem exact_field_equalities (x z : Vec n) :
    metricEnergy (1 : Mat n) (z - x) =
        TransportedCertificate.pairCurvature x z x z ∧
      TransportedCertificate.stepProjector (z - x) * (1 : Mat n) *
          TransportedCertificate.stepProjector (z - x) =
        (1 + 0 * TransportedCertificate.pairDecrease x z x) •
          (TransportedCertificate.stepProjector (z - x) * (1 : Mat n) *
            TransportedCertificate.stepProjector (z - x)) := by
  constructor
  · simp [identity_energy, TransportedCertificate.pairCurvature,
      TransportedCertificate.pairStep, dot_self]
  · simp

/-- The full inverse-BFGS update, with a matching identity secant, fixes the identity. -/
theorem inverseBFGS_identity (s : Vec n) : inverseBFGS (1 : Mat n) s s = 1 := by
  unfold inverseBFGS
  dsimp only
  rw [dot_self, Matrix.mul_one]
  change TransportedCertificate.stepProjector s * TransportedCertificate.stepProjector s +
    (sqNorm s)⁻¹ • outer s s = 1
  rw [TransportedCertificate.mul_stepProjector _ s
    (TransportedCertificate.stepProjector_mulVec_self s)]
  simp [TransportedCertificate.stepProjector]

def point (x₀ : Vec n) (k : ℕ) : Vec n := ((1 / 2 : ℝ) ^ k) • x₀

theorem point_succ (x₀ : Vec n) (k : ℕ) :
    point x₀ (k + 1) = (1 / 2 : ℝ) • point x₀ k := by
  simp only [point, pow_succ, smul_smul]
  congr 1
  ring

theorem point_ne_zero {x₀ : Vec n} (hx₀ : x₀ ≠ 0) (k : ℕ) : point x₀ k ≠ 0 :=
  smul_ne_zero (pow_ne_zero k (by norm_num)) hx₀

theorem step_eq (x₀ : Vec n) (k : ℕ) :
    bfgsStep (1 : Mat n) (point x₀ k) (1 / 2) = point x₀ (k + 1) - point x₀ k := by
  rw [point_succ]
  ext i
  simp [bfgsStep]
  ring

theorem objective_smul (a : ℝ) (x : Vec n) : objective (a • x) = a ^ 2 * objective x := by
  rw [objective, CertificateGeometry.sqNorm_smul]
  unfold objective
  ring

theorem objective_half (x : Vec n) : objective ((1 / 2 : ℝ) • x) = (1 / 4) * objective x := by
  rw [objective_smul]
  norm_num

theorem old_pairing (x : Vec n) :
    dot x (bfgsStep (1 : Mat n) x (1 / 2)) = -(1 / 2) * sqNorm x := by
  rw [bfgsStep, Matrix.one_mulVec, dot_smul_right, dot_self]

theorem dot_smul_first (a : ℝ) (x y : Vec n) : dot (a • x) y = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- An infinite actual-gradient full-BFGS run for every nonzero initial vector. -/
def run (x₀ : Vec n) (hx₀ : x₀ ≠ 0) : AdmissibleBFGSRun n objective where
  convex := objective_convex
  x := point x₀
  H := fun _ => 1
  g := point x₀
  α := fun _ => 1 / 2
  c₁ := 1 / 4
  c₂ := 1 / 2
  c₁_pos := by norm_num
  c₁_lt_c₂ := by norm_num
  c₂_lt_one := by norm_num
  initial_posDef := Matrix.PosDef.one
  alpha_pos := fun _ => by norm_num
  gradient_nonzero := point_ne_zero hx₀
  hasGradient := fun k => objective_hasGradient (point x₀ k)
  step := fun k => by rw [step_eq]; abel
  update := fun k => by rw [step_eq, inverseBFGS_identity]
  armijo := fun k => by
    rw [point_succ, objective_half, old_pairing]
    unfold objective
    nlinarith [sqNorm_nonneg (point x₀ k)]
  weak_wolfe := fun k => by rw [point_succ, dot_smul_first]

theorem run_values (x₀ : Vec n) (hx₀ : x₀ ≠ 0) (k : ℕ) :
    objective ((run x₀ hx₀).x k) = ((1 / 2 : ℝ) ^ k) ^ 2 * objective x₀ :=
  objective_smul _ _

theorem run_scalars (x₀ : Vec n) (hx₀ : x₀ ≠ 0) (k : ℕ) :
    let R := run x₀ hx₀
    R.q k = sqNorm (R.x k) ∧ R.d k = (1 / 2) * R.q k ∧
      objective (R.x k) - objective (R.x (k + 1)) = (3 / 8) * R.q k ∧
      R.curvature k = (1 / 4) * R.q k := by
  have hq : (run x₀ hx₀).q k = sqNorm (point x₀ k) := identity_energy _
  refine ⟨hq, rfl, ?_, ?_⟩
  · change objective (point x₀ k) - objective (point x₀ (k + 1)) = _
    rw [point_succ, objective_half, hq]
    unfold objective
    ring
  · change dot (point x₀ (k + 1) - point x₀ k)
      (bfgsStep (1 : Mat n) (point x₀ k) (1 / 2)) = _
    rw [← step_eq, hq, bfgsStep, Matrix.one_mulVec,
      dot_smul_first, dot_smul_right, dot_self]
    ring

theorem run_weak_wolfe_eq (x₀ : Vec n) (hx₀ : x₀ ≠ 0) (k : ℕ) :
    let R := run x₀ hx₀
    dot (R.g (k + 1)) (R.displacement k) =
      R.c₂ * dot (R.g k) (R.displacement k) := by
  change dot (point x₀ (k + 1)) (bfgsStep (1 : Mat n) (point x₀ k) (1 / 2)) =
    (1 / 2) * dot (point x₀ k) (bfgsStep (1 : Mat n) (point x₀ k) (1 / 2))
  rw [point_succ, dot_smul_first]

/-- Direct geometric convergence, independent of the certificate convergence theorem. -/
theorem run_limits (x₀ : Vec n) (hx₀ : x₀ ≠ 0) :
    Tendsto (fun k => objective ((run x₀ hx₀).x k)) atTop (𝓝 0) ∧
      Tendsto (run x₀ hx₀).x atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  constructor
  · simp_rw [run_values]
    simpa using (ht.pow 2).mul_const (objective x₀)
  · change Tendsto (fun k => ((1 / 2 : ℝ) ^ k) • x₀) atTop (𝓝 0)
    simpa only [zero_smul] using ht.smul_const x₀

/-- Convexity, a unique attained minimum, compact positive sublevel, all exact
full-rank certificates, initialization, actual run and convergence hold jointly. -/
theorem joint_witness (x₀ : Vec n) (hx₀ : x₀ ≠ 0) :
    ConvexOn ℝ univ (@objective n) ∧
      (∀ x : Vec n, objective x = 0 ↔ x = 0) ∧
      ∃ (R : AdmissibleBFGSRun n objective) (b : ℝ),
        R.x 0 = x₀ ∧ R.H = (fun _ => 1) ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
        (∀ k, R.x k = ((1 / 2 : ℝ) ^ k) • x₀ ∧ R.g k = R.x k ∧ R.α k = 1 / 2) ∧
        b = objective x₀ ∧ 0 < b ∧ IsCompact {x : Vec n | objective x ≤ b} ∧
        IsLeast (Set.range (@objective n)) 0 ∧ objective (R.x 0) ≤ b ∧
        (∀ k, objective (R.x k) ≤ b) ∧
        (∀ η : ℝ, 0 < η →
          ∃ B : TransportedCertificate.BandCertificate (@objective n) {x | objective x ≤ b}
              0 R.c₁ R.c₂ η,
            B.W = (fun _ => 1) ∧ B.m = 2 * η ∧ B.C = 1 ∧ B.L = 0 ∧ B.δ = 1 ∧
              0 ≤ B.C ∧ ∀ x, (B.W x).PosDef ∧ (B.W x).rank = n) ∧
        Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0) := by
  let R := run x₀ hx₀
  have hstart : R.x 0 = x₀ := by simp [R, run, point]
  refine ⟨objective_convex, objective_eq_zero_iff, R, objective x₀,
    hstart, rfl, rfl, rfl, fun k => ⟨rfl, rfl, rfl⟩, rfl,
    objective_pos hx₀, sublevel_compact _, objective_minimum, by rw [hstart],
    fun k => ?_, fun η hη => ?_, (run_limits x₀ hx₀).1, (run_limits x₀ hx₀).2⟩
  · simpa only [hstart] using R.objective_le_initial k
  · exact ⟨certificate _ _ _ η hη, certificate_parameters _ _ _ η hη⟩

/-- The planar projected identity field is nonzero; this is a genuine higher-rank example. -/
theorem planar_projection :
    TransportedCertificate.stepProjector (![1, 0] : Vec 2) * (1 : Mat 2) *
        TransportedCertificate.stepProjector ![1, 0] = Matrix.diagonal ![0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [TransportedCertificate.stepProjector, sqNorm, outer, Fin.sum_univ_two,
      Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem planar_run_nonempty : Nonempty (AdmissibleBFGSRun 2 objective) := by
  refine ⟨run ![1, 1] ?_⟩
  intro h
  have h0 := congrFun h 0
  norm_num at h0

end Quadratic

namespace Mixed

/-- The literal nonsmooth mixed ridge. -/
abbrev objective : Vec 2 → ℝ := UnexcitedMetric.objective

theorem objective_formula (x : Vec 2) : objective x = (x 0) ^ 2 + |x 1| := rfl

theorem objective_convex : ConvexOn ℝ univ objective := UnexcitedMetric.objective_convex

theorem objective_zero : objective 0 = 0 := by simp [objective, UnexcitedMetric.objective]

theorem objective_nonneg (x : Vec 2) : 0 ≤ objective x := UnexcitedMetric.objective_nonneg x

theorem objective_eq_zero_iff (x : Vec 2) : objective x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact UnexcitedMetric.unique_minimum (hx.trans objective_zero.symm)
  · rintro rfl
    exact objective_zero

theorem objective_minimum : IsLeast (Set.range objective) 0 :=
  ⟨⟨0, objective_zero⟩, by rintro _ ⟨x, rfl⟩; exact objective_nonneg x⟩

theorem sublevel_compact (b : ℝ) : IsCompact {x : Vec 2 | objective x ≤ b} :=
  Localization.sublevel_compact objective_convex 0
    (fun x => by rw [objective_zero]; exact objective_nonneg x)
    (fun x hx => (objective_eq_zero_iff x).mp (hx.trans objective_zero)) b

/-- The positive-side supporting slope equals every actual full-space gradient. -/
theorem gradient_eq_of_nonneg {x g : Vec 2} (hx : 0 ≤ x 1)
    (hg : HasFDerivAt objective (gradientFunctional g) x) : g = ![2 * x 0, 1] := by
  symm
  apply supporting_vector_eq_gradient _ hg
  intro z
  simp only [objective, UnexcitedMetric.objective, dot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, one_mul,
    abs_of_nonneg hx]
  nlinarith [sq_nonneg (z 0 - x 0), le_abs_self (z 1)]

/-- The negative-side supporting slope equals every actual full-space gradient. -/
theorem gradient_eq_of_nonpos {x g : Vec 2} (hx : x 1 ≤ 0)
    (hg : HasFDerivAt objective (gradientFunctional g) x) : g = ![2 * x 0, -1] := by
  symm
  apply supporting_vector_eq_gradient _ hg
  intro z
  simp only [objective, UnexcitedMetric.objective, dot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, neg_one_mul,
    abs_of_nonpos hx]
  nlinarith [sq_nonneg (z 0 - x 0), neg_le_abs (z 1)]

theorem differentiable_coordinate_ne_zero {x : Vec 2}
    (hx : DifferentiableAt ℝ objective x) : x 1 ≠ 0 := by
  intro hzero
  have hg := hasFDerivAt_coordinateGradient hx
  have hp := gradient_eq_of_nonneg (le_of_eq hzero.symm) hg
  have hn := gradient_eq_of_nonpos (le_of_eq hzero) hg
  have hh := congrFun (hp.symm.trans hn) 1
  norm_num at hh

theorem radial_pairing {x g : Vec 2}
    (hg : HasFDerivAt objective (gradientFunctional g) x) :
    dot g x = 2 * (x 0) ^ 2 + |x 1| :=
  InterceptExamples.quadratic_absolute_radial_pairing hg

private theorem same_sign_bound (A a b : ℝ) (ha : a ^ 2 ≤ b) :
    (2 * A * a) ^ 2 ≤ 2 * b * (2 * A ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg A)]

/-- A division-free weighted Cauchy--Schwarz estimate for a sign-changing pair. -/
theorem opposite_sign_bound (A a v w b : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hb : a ^ 2 + w ≤ b) :
    (2 * A * a + 2 * w) ^ 2 ≤ 2 * b * (2 * A ^ 2 + 2 * (v + w)) := by
  have hcs : (A * a + w) ^ 2 ≤ (a ^ 2 + w) * (A ^ 2 + v + w) := by
    nlinarith [mul_nonneg hw (sq_nonneg (A - a)),
      mul_nonneg hv (sq_nonneg a), mul_nonneg hv hw]
  have hmul := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ A ^ 2 + v + w by positivity)
  nlinarith only [hcs, hmul]

/-- The sharp radial secant bound holds at all differentiable endpoint pairs
with the second endpoint in the sublevel; eligibility and smallness are unnecessary. -/
theorem secant_bound {b : ℝ} {x z g h : Vec 2} (hz : objective z ≤ b)
    (hg : HasFDerivAt objective (gradientFunctional g) x)
    (hh : HasFDerivAt objective (gradientFunctional h) z) :
    (dot (h - g) z) ^ 2 ≤ 2 * b * TransportedCertificate.pairCurvature x z g h := by
  rcases le_total 0 (x 1) with hx | hx <;> rcases le_total 0 (z 1) with hw | hw
  · rw [gradient_eq_of_nonneg hx hg, gradient_eq_of_nonneg hw hh]
    have hb : (z 0) ^ 2 ≤ b := by
      have hz' := hz
      rw [objective_formula, abs_of_nonneg hw] at hz'
      linarith
    convert same_sign_bound (z 0 - x 0) (z 0) b hb using 1 <;>
      simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, TransportedCertificate.pairCurvature,
        TransportedCertificate.pairStep] <;> ring
  · rw [gradient_eq_of_nonneg hx hg, gradient_eq_of_nonpos hw hh]
    have hb : (z 0) ^ 2 + -z 1 ≤ b := by
      simpa only [objective_formula, abs_of_nonpos hw] using hz
    convert opposite_sign_bound (z 0 - x 0) (z 0) (x 1) (-z 1) b hx
      (neg_nonneg.mpr hw) hb using 1 <;>
      simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, TransportedCertificate.pairCurvature,
        TransportedCertificate.pairStep] <;> ring
  · rw [gradient_eq_of_nonpos hx hg, gradient_eq_of_nonneg hw hh]
    have hb : (z 0) ^ 2 + z 1 ≤ b := by
      simpa only [objective_formula, abs_of_nonneg hw] using hz
    convert opposite_sign_bound (z 0 - x 0) (z 0) (-x 1) (z 1) b
      (neg_nonneg.mpr hx) hw hb using 1 <;>
      simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, TransportedCertificate.pairCurvature,
        TransportedCertificate.pairStep] <;> ring
  · rw [gradient_eq_of_nonpos hx hg, gradient_eq_of_nonpos hw hh]
    have hb : (z 0) ^ 2 ≤ b := by
      have hz' := hz
      rw [objective_formula, abs_of_nonpos hw] at hz'
      linarith
    convert same_sign_bound (z 0 - x 0) (z 0) b hb using 1 <;>
      simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, TransportedCertificate.pairCurvature,
        TransportedCertificate.pairStep] <;> ring

/-- The radial field has exactly equal projected transports for every endpoint pair. -/
theorem projected_transport (x z : Vec 2) :
    TransportedCertificate.stepProjector (z - x) * outer z z *
        TransportedCertificate.stepProjector (z - x) =
      TransportedCertificate.stepProjector (z - x) * outer x x *
        TransportedCertificate.stepProjector (z - x) := by
  have hp : (TransportedCertificate.stepProjector (z - x)).mulVec z =
      (TransportedCertificate.stepProjector (z - x)).mulVec x := by
    have hz : z = x + (z - x) := by abel
    calc
      _ = (TransportedCertificate.stepProjector (z - x)).mulVec (x + (z - x)) :=
        congrArg (TransportedCertificate.stepProjector (z - x)).mulVec hz
      _ = _ := by
        rw [Matrix.mulVec_add, TransportedCertificate.stepProjector_mulVec_self, add_zero]
  rw [TransportedCertificate.projected_outer, TransportedCertificate.projected_outer, hp]

/-- Exact radial certificates on every positive sublevel and positive band. -/
def certificate (b c₁ c₂ η : ℝ) (hη : 0 < η) :
    TransportedCertificate.BandCertificate objective {x | objective x ≤ b} 0 c₁ c₂ η :=
  TransportedCertificate.rankOneCertificate (fun x => x) (η ^ 2) (2 * b) 0 1
    (sq_pos_of_pos hη) le_rfl zero_lt_one
    (by
      intro x hx g hg
      rw [radial_pairing hg]
      have hηx := hx.2
      rw [objective_formula] at hηx
      nlinarith [sq_nonneg (x 0), abs_nonneg (x 1)])
    (fun _ _ _ _ _ hz hp _ => secant_bound hz.1 hp.gradient_x hp.gradient_z)
    (by
      intro x z g h _ _ _ _
      refine ⟨1, 1, ?_, ?_⟩
      · simp only [one_smul, TransportedCertificate.pairStep]
        abel
      · simp)

theorem certificate_parameters {b : ℝ} (hb : 0 < b) (c₁ c₂ η : ℝ) (hη : 0 < η) :
    let B := certificate b c₁ c₂ η hη
    B.W = (fun x => outer x x) ∧ B.m = η ^ 2 ∧ B.C = 2 * b ∧
      B.L = 0 ∧ B.δ = 1 ∧ 0 ≤ B.C :=
  ⟨rfl, rfl, rfl, rfl, rfl, mul_nonneg (by norm_num) hb.le⟩

/-- Identity-initialized, kink-crossing infinite full-BFGS history. -/
def run : AdmissibleBFGSRun 2 objective :=
  UnexcitedMetric.run 1 (2 / 3) (1 / 2) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem run_points (k : ℕ) : run.x k = ![0, (2 / 3) * (-1 / 2 : ℝ) ^ k] := by
  change UnexcitedMetric.point (UnexcitedMetric.sign k)
    (UnexcitedMetric.radius (1 / 2) (2 / 3) k) = _
  rw [UnexcitedMetric.literal_point_formula]
  ext i
  fin_cases i <;> simp
  ring

theorem run_gradients (k : ℕ) : run.g k = ![0, (-1 : ℝ) ^ k] := rfl

theorem run_matrices (k : ℕ) : run.H k = Matrix.diagonal ![1, (1 / 2 : ℝ) ^ k] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [run, UnexcitedMetric.run, UnexcitedMetric.diagonal, UnexcitedMetric.radius,
      Matrix.diagonal_apply]
  ring

theorem run_initial : run.x 0 = ![0, 2 / 3] ∧ run.H 0 = 1 := by
  constructor
  · simpa using run_points 0
  · rw [run_matrices]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem run_constants : run.c₁ = 1 / 4 ∧ run.c₂ = 1 / 2 ∧ ∀ k, run.α k = 1 := by
  refine ⟨rfl, rfl, fun _ => ?_⟩
  norm_num [run, UnexcitedMetric.run]

theorem run_values (k : ℕ) : objective (run.x k) = (2 / 3) * (1 / 2 : ℝ) ^ k := by
  change UnexcitedMetric.objective (UnexcitedMetric.point (UnexcitedMetric.sign k)
    (UnexcitedMetric.radius (1 / 2) (2 / 3) k)) = _
  rw [UnexcitedMetric.point_value (UnexcitedMetric.sign_sq k)
    (UnexcitedMetric.radius_pos (by norm_num) (by norm_num) k).le]
  unfold UnexcitedMetric.radius
  ring

/-- Predicted decrease, actual decrease, and curvature of the displayed history. -/
theorem run_scalars (k : ℕ) :
    run.d k = (1 / 2 : ℝ) ^ k ∧
      objective (run.x k) - objective (run.x (k + 1)) = (1 / 3) * (1 / 2 : ℝ) ^ k ∧
      run.curvature k = 2 * (1 / 2 : ℝ) ^ k := by
  have hs : ((-1 : ℝ) ^ k) ^ 2 = 1 := UnexcitedMetric.sign_sq k
  have hd : run.d k = (1 / 2 : ℝ) ^ k := by
    rw [AdmissibleBFGSRun.d, AdmissibleBFGSRun.q, run_matrices, run_gradients,
      (run_constants.2.2 k)]
    simp only [metricEnergy, dot, Fin.sum_univ_two, Matrix.mulVec_diagonal,
      Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add, one_mul]
    nlinarith only [congrArg (fun t : ℝ => ((1 / 2 : ℝ) ^ k) * t) hs]
  refine ⟨hd, ?_, ?_⟩
  · rw [run_values, run_values, pow_succ]
    ring
  · rw [AdmissibleBFGSRun.curvature, AdmissibleBFGSRun.gradientChange,
      AdmissibleBFGSRun.displacement, run_gradients, run_gradients,
      run_matrices, (run_constants.2.2 k)]
    simp only [bfgsStep, dot, Fin.sum_univ_two, Matrix.mulVec_diagonal,
      Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_sub, zero_add,
      one_mul, pow_succ]
    nlinarith only [congrArg (fun t : ℝ => ((1 / 2 : ℝ) ^ k) * t) hs]

theorem run_limits :
    Tendsto run.x atTop (𝓝 0) ∧
      Tendsto (fun k => objective (run.x k)) atTop (𝓝 0) := by
  have h := UnexcitedMetric.run_limits 1 (2 / 3) (1 / 2) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1⟩

theorem run_matrix_limit :
    Tendsto run.H atTop (𝓝 (Matrix.diagonal (![1, 0] : Vec 2))) := by
  have he : UnexcitedMetric.diagonal 1 0 = Matrix.diagonal (![1, 0] : Vec 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← he]
  exact UnexcitedMetric.literal_matrix_limit 1 (ρ := 1 / 2) (v₀ := 2 / 3)
    (by norm_num) (by norm_num)

/-- A single explicit nonsmooth objective, compact sublevel, all band
certificates and an identity-initialized infinite admissible run satisfy the
complete hypotheses together. This works for every `b ≥ 2/3`. -/
theorem joint_witness {b : ℝ} (hb : (2 / 3 : ℝ) ≤ b) :
    ConvexOn ℝ univ objective ∧ IsLeast (Set.range objective) 0 ∧
      (∀ x, objective x = 0 ↔ x = 0) ∧ 0 < b ∧
      IsCompact {x : Vec 2 | objective x ≤ b} ∧
      ∃ R : AdmissibleBFGSRun 2 objective,
        R.x 0 = ![0, 2 / 3] ∧ R.H 0 = 1 ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
        (∀ k, R.x k = ![0, (2 / 3) * (-1 / 2 : ℝ) ^ k] ∧
          R.g k = ![0, (-1 : ℝ) ^ k] ∧
          R.H k = Matrix.diagonal ![1, (1 / 2 : ℝ) ^ k] ∧ R.α k = 1) ∧
        (∀ k, objective (R.x k) ≤ b) ∧
        (∀ k, R.d k = (1 / 2 : ℝ) ^ k ∧
          objective (R.x k) - objective (R.x (k + 1)) = (1 / 3) * (1 / 2 : ℝ) ^ k ∧
          R.curvature k = 2 * (1 / 2 : ℝ) ^ k) ∧
        (∀ η : ℝ, 0 < η →
          ∃ B : TransportedCertificate.BandCertificate objective {x | objective x ≤ b}
              0 R.c₁ R.c₂ η,
            B.W = (fun x => outer x x) ∧ B.m = η ^ 2 ∧ B.C = 2 * b ∧
              B.L = 0 ∧ B.δ = 1 ∧ 0 ≤ B.C) ∧
        Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  refine ⟨objective_convex, objective_minimum, objective_eq_zero_iff, hb0,
    sublevel_compact b, run, run_initial.1, run_initial.2,
    run_constants.1, run_constants.2.1,
    fun k => ⟨run_points k, run_gradients k, run_matrices k, run_constants.2.2 k⟩,
    fun k => ?_, run_scalars, fun η hη => ?_, run_limits.2, run_limits.1⟩
  · exact (run.objective_le_initial k).trans (by simpa only [run_values, pow_zero, mul_one] using hb)
  · exact ⟨certificate b _ _ η hη, certificate_parameters hb0 _ _ η hη⟩

theorem run_nonempty : Nonempty (AdmissibleBFGSRun 2 objective) := ⟨run⟩

end Mixed

namespace Gauge

def family : MaxAffine.Family 2 3 where
  a := ![![1, 0], ![-1, 1], ![-1, -1]]
  b := 0
  nonempty := ⟨0⟩

/-- A finite convex max-linear gauge with an obstructed first search ray. -/
def objective : Vec 2 → ℝ := family.objective

theorem branch_values (x : Vec 2) :
    family.branch 0 x = x 0 ∧ family.branch 1 x = -x 0 + x 1 ∧
      family.branch 2 x = -x 0 - x 1 := by
  simp [family, MaxAffine.Family.branch, dot, Fin.sum_univ_two, sub_eq_add_neg]

theorem objective_formula (x : Vec 2) :
    objective x = max (x 0) (max (-x 0 + x 1) (-x 0 - x 1)) := by
  apply le_antisymm
  · change Finset.univ.sup' family.indices_nonempty (fun i => family.branch i x) ≤ _
    apply Finset.sup'_le
    intro i _
    fin_cases i
    · change family.branch 0 x ≤ _
      rw [(branch_values x).1]
      exact le_max_left _ _
    · change family.branch 1 x ≤ _
      rw [(branch_values x).2.1]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · change family.branch 2 x ≤ _
      rw [(branch_values x).2.2]
      exact (le_max_right _ _).trans (le_max_right _ _)
  · refine max_le ?_ (max_le ?_ ?_)
    · simpa only [(branch_values x).1] using family.branch_le 0 x
    · simpa only [(branch_values x).2.1] using family.branch_le 1 x
    · simpa only [(branch_values x).2.2] using family.branch_le 2 x

theorem objective_abs_formula (x : Vec 2) :
    objective x = max (x 0) (-x 0 + |x 1|) := by
  rw [objective_formula, abs_eq_max_neg, add_max, sub_eq_add_neg]

theorem objective_convex : ConvexOn ℝ univ objective := family.objective_convex

theorem objective_continuous : Continuous objective := family.objective_continuous

theorem objective_homogeneous : Homogeneous.PositiveDegreeOne objective := by
  intro t ht x
  simp only [objective_abs_formula, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg ht, mul_max_of_nonneg _ _ ht]
  congr 1
  ring

theorem coordinate_bounds (x : Vec 2) : |x 0| ≤ objective x ∧ |x 1| / 2 ≤ objective x := by
  have h0 : x 0 ≤ objective x := by rw [objective_abs_formula]; exact le_max_left _ _
  have h1 : -x 0 + |x 1| ≤ objective x := by
    rw [objective_abs_formula]
    exact le_max_right _ _
  constructor
  · apply abs_le.mpr
    constructor <;> linarith [abs_nonneg (x 1)]
  · linarith

theorem objective_zero : objective 0 = 0 := by simp [objective_abs_formula]

theorem objective_nonneg (x : Vec 2) : 0 ≤ objective x :=
  (abs_nonneg _).trans (coordinate_bounds x).1

theorem objective_eq_zero_iff (x : Vec 2) : objective x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨h0, h1⟩ := coordinate_bounds x
    rw [hx] at h0 h1
    have hzero : x 0 = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
    have hone : x 1 = 0 := abs_eq_zero.mp (by linarith [abs_nonneg (x 1)])
    ext i
    fin_cases i <;> assumption
  · rintro rfl
    exact objective_zero

theorem objective_minimum : IsLeast (Set.range objective) 0 :=
  ⟨⟨0, objective_zero⟩, by rintro _ ⟨x, rfl⟩; exact objective_nonneg x⟩

theorem sublevel_compact (b : ℝ) : IsCompact {x : Vec 2 | objective x ≤ b} :=
  Localization.sublevel_compact objective_convex 0
    (fun x => by rw [objective_zero]; exact objective_nonneg x)
    (fun x hx => (objective_eq_zero_iff x).mp (hx.trans objective_zero)) b

theorem objective_coercive : Tendsto objective (cocompact (Vec 2)) atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(sublevel_compact b).compl_mem_cocompact] with x hx
  change ¬ objective x ≤ b at hx
  exact (lt_of_not_ge hx).le

/-- The homogeneous convergence theorem does apply to this objective; it is
conditional on an infinite admissible run, as the obstruction below illustrates. -/
theorem admissible_runs_converge (R : AdmissibleBFGSRun 2 objective) :
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) :=
  ⟨R.homogeneous_value_zero_of_lower_bound objective_homogeneous 0
      (fun k => objective_nonneg (R.x k)),
    R.homogeneous_iterates_zero_of_bounded_zero_sublevel objective_homogeneous
      (sublevel_compact 0).isBounded⟩

def initialPoint (ε : ℝ) : Vec 2 := ![ε, 0]

def initialGradient : Vec 2 := ![1, 0]

def ray (ε α : ℝ) : Vec 2 := ![ε - α, 0]

theorem ray_step (ε α : ℝ) :
    ray ε α = initialPoint ε + bfgsStep (1 : Mat 2) initialGradient α := by
  ext i
  fin_cases i <;> simp [ray, initialPoint, initialGradient, bfgsStep]
  ring

theorem ray_gradient_before {ε α : ℝ} (hα : α < ε) :
    HasFDerivAt objective (gradientFunctional initialGradient) (ray ε α) := by
  apply family.strict_active_hasGradient (i := 0)
  intro j hj
  fin_cases j <;>
    simp [family, MaxAffine.Family.branch, dot, Fin.sum_univ_two, ray] at hj ⊢ <;>
    linarith

theorem ray_value_after {ε α : ℝ} (hα : ε ≤ α) : objective (ray ε α) = α - ε := by
  rw [objective_abs_formula]
  simp only [ray, Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, add_zero]
  rw [max_eq_right (by linarith)]
  ring

/-- The entire ray at and beyond the minimizer is nondifferentiable in the plane,
because the two distinct slopes `(-1,1)` and `(-1,-1)` are simultaneously active. -/
theorem ray_not_differentiable_after {ε α : ℝ} (hα : ε ≤ α) :
    ¬ DifferentiableAt ℝ objective (ray ε α) := by
  intro hd
  have hg := hasFDerivAt_coordinateGradient hd
  have h1 : family.branch 1 (ray ε α) = objective (ray ε α) := by
    rw [(branch_values _).2.1, ray_value_after hα]
    simp [ray]
  have h2 : family.branch 2 (ray ε α) = objective (ray ε α) := by
    rw [(branch_values _).2.2, ray_value_after hα]
    simp [ray]
  have he := (family.active_eq_gradient h1 hg).trans (family.active_eq_gradient h2 hg).symm
  have hc := congrFun he 1
  change (1 : ℝ) = -1 at hc
  norm_num at hc

theorem initial_state {ε : ℝ} (hε : 0 < ε) :
    objective (initialPoint ε) = ε ∧
      HasFDerivAt objective (gradientFunctional initialGradient) (initialPoint ε) ∧
      initialGradient ≠ 0 ∧ (1 : Mat 2).PosDef := by
  refine ⟨?_, ?_, ?_, Matrix.PosDef.one⟩
  · rw [objective_abs_formula]
    simp only [initialPoint, Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, add_zero]
    exact max_eq_left (by linarith)
  · simpa only [ray, sub_zero, initialPoint] using ray_gradient_before (α := 0) hε
  · intro h
    have h0 := congrFun h 0
    norm_num [initialGradient] at h0

/-- For every `c₂ < 1`, no positive step on this identity-metric search ray can
have both a full-space derivative and weak Wolfe. Armijo is not needed. -/
theorem no_differentiable_weak_wolfe {ε c₂ α : ℝ} (hc₂ : c₂ < 1) (hα : 0 < α)
    (g : Vec 2) (hg : HasFDerivAt objective (gradientFunctional g) (ray ε α)) :
    ¬ (c₂ * dot initialGradient (bfgsStep (1 : Mat 2) initialGradient α) ≤
      dot g (bfgsStep (1 : Mat 2) initialGradient α)) := by
  intro hw
  by_cases ha : α < ε
  · have he : g = initialGradient := AffineProjection.gradientFunctional_injective
      (hg.unique (ray_gradient_before ha))
    rw [he] at hw
    have hp : dot initialGradient (bfgsStep (1 : Mat 2) initialGradient α) = -α := by
      simp [initialGradient, bfgsStep, dot, Fin.sum_univ_two]
    rw [hp] at hw
    nlinarith [mul_pos (sub_pos.mpr hc₂) hα]
  · exact ray_not_differentiable_after (le_of_not_gt ha) hg.differentiableAt

/-- Thus no infinite admissible run can start from these prescribed data. -/
theorem no_admissible_run {ε : ℝ} (hε : 0 < ε)
    (R : AdmissibleBFGSRun 2 objective) (hx : R.x 0 = initialPoint ε)
    (hH : R.H 0 = 1) : False := by
  have hg0 : R.g 0 = initialGradient := by
    apply AffineProjection.gradientFunctional_injective
    have hg := R.hasGradient 0
    rw [hx] at hg
    exact hg.unique (initial_state hε).2.1
  have hx1 : R.x 1 = ray ε (R.α 0) := by
    rw [R.step 0, hx, hH, hg0, ← ray_step]
  have hg1 := R.hasGradient 1
  rw [hx1] at hg1
  have hw := R.weak_wolfe 0
  rw [hH, hg0] at hw
  exact no_differentiable_weak_wolfe R.c₂_lt_one (R.alpha_pos 0) (R.g 1) hg1 hw

/-- All homogeneous objective hypotheses hold, yet every positive horizontal
start with identity metric has no differentiable weak-Wolfe first step. The
start has strictly positive value, and the obstruction includes the whole
nondifferentiable continuation beyond the optimizer. -/
theorem joint_obstruction {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ objective ∧ Continuous objective ∧
      Homogeneous.PositiveDegreeOne objective ∧
      IsLeast (Set.range objective) 0 ∧ (∀ x, objective x = 0 ↔ x = 0) ∧
      (∀ b : ℝ, IsCompact {x : Vec 2 | objective x ≤ b}) ∧
      Tendsto objective (cocompact (Vec 2)) atTop ∧
      objective (initialPoint ε) = ε ∧
      HasFDerivAt objective (gradientFunctional initialGradient) (initialPoint ε) ∧
      initialGradient ≠ 0 ∧ (1 : Mat 2).PosDef ∧
      (∀ α : ℝ, ray ε α = initialPoint ε + bfgsStep (1 : Mat 2) initialGradient α) ∧
      (∀ α : ℝ, α < ε →
        HasFDerivAt objective (gradientFunctional initialGradient) (ray ε α)) ∧
      (∀ α : ℝ, ε ≤ α → ¬ DifferentiableAt ℝ objective (ray ε α)) ∧
      (∀ c₂ : ℝ, c₂ < 1 → ∀ α : ℝ, 0 < α → ∀ g : Vec 2,
        HasFDerivAt objective (gradientFunctional g) (ray ε α) →
        ¬ (c₂ * dot initialGradient (bfgsStep (1 : Mat 2) initialGradient α) ≤
          dot g (bfgsStep (1 : Mat 2) initialGradient α))) ∧
      ¬ ∃ R : AdmissibleBFGSRun 2 objective, R.x 0 = initialPoint ε ∧ R.H 0 = 1 := by
  refine ⟨objective_convex, objective_continuous, objective_homogeneous,
    objective_minimum, objective_eq_zero_iff, sublevel_compact, objective_coercive,
    (initial_state hε).1, (initial_state hε).2.1, (initial_state hε).2.2.1,
    (initial_state hε).2.2.2, ray_step ε,
    fun _ hα => ray_gradient_before hα,
    fun _ hα => ray_not_differentiable_after hα,
    fun _ hc₂ _ hα g hg => no_differentiable_weak_wolfe hc₂ hα g hg, ?_⟩
  rintro ⟨R, hx, hH⟩
  exact no_admissible_run hε R hx hH

theorem obstructed_state_exists :
    ∃ ε : ℝ, 0 < ε ∧ objective (initialPoint ε) = ε ∧
      HasFDerivAt objective (gradientFunctional initialGradient) (initialPoint ε) ∧
      ¬ ∃ R : AdmissibleBFGSRun 2 objective, R.x 0 = initialPoint ε ∧ R.H 0 = 1 := by
  refine ⟨1, one_pos, (initial_state one_pos).1, (initial_state one_pos).2.1, ?_⟩
  rintro ⟨R, hx, hH⟩
  exact no_admissible_run one_pos R hx hH

end Gauge

end BfgsVerification.HypothesisExamples
