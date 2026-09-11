import BfgsVerification.HomogeneousConsequences
import BfgsVerification.RadialConvergence
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Source F:transform. The real function Φ is only
constrained on [0,∞); its extension to negative arguments is irrelevant. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification.TransformedGauge

structure IncreasingTransform (Φ : ℝ → ℝ) : Prop where
  continuous : ContinuousOn Φ (Ici 0)
  convex : ConvexOn ℝ (Ici 0) Φ
  strictMono : StrictMonoOn Φ (Ici 0)
  zero : Φ 0 = 0
  smooth : ContDiffOn ℝ 2 Φ (Ioi 0)
  deriv_pos : ∀ r, 0 < r → 0 < deriv Φ r

def objective {n : ℕ} (Φ : ℝ → ℝ) (γ : Vec n → ℝ) (star : Vec n) (x : Vec n) :=
  Φ (γ (x - star))

theorem gauge_nonneg {n : ℕ} {γ : Vec n → ℝ}
    (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (x : Vec n) : 0 ≤ γ x := by
  by_cases hx : x = 0
  · simp only [hx, Homogeneous.value_zero hh, le_refl]
  · exact (Homogeneous.positive_of_bounded_zero_sublevel hh
      (Homogeneous.bounded_zero_sublevel_of_coercive hc) hx).le

theorem objective_at_center {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ) (star : Vec n) :
    objective Φ γ star star = 0 := by
  simp only [objective, sub_self, Homogeneous.value_zero hh, hΦ.zero]

theorem objective_nonneg {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star x : Vec n) :
    0 ≤ objective Φ γ star x := by
  have h := hΦ.strictMono.monotoneOn (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (gauge_nonneg hh hc (x-star)) (gauge_nonneg hh hc (x-star))
  simpa only [hΦ.zero, objective] using h

theorem objective_eq_zero_iff {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star x : Vec n) :
    objective Φ γ star x = 0 ↔ x = star := by
  constructor
  · intro he
    by_contra hx
    have hp := Homogeneous.positive_of_bounded_zero_sublevel hh
      (Homogeneous.bounded_zero_sublevel_of_coercive hc) (sub_ne_zero.mpr hx)
    have hv := hΦ.strictMono (show (0 : ℝ) ∈ Ici 0 by norm_num) hp.le hp
    rw [hΦ.zero] at hv
    exact (ne_of_gt hv) he
  · intro hx
    subst x
    exact objective_at_center hΦ hh star

theorem objective_convex {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n) :
    ConvexOn ℝ univ (objective Φ γ star) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hid : a • x + b • y - star = a • (x-star) + b • (y-star) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t * star i) hab]
  have hinner := hγ.2 (mem_univ (x-star)) (mem_univ (y-star)) ha hb hab
  have hx := gauge_nonneg hh hc (x-star)
  have hy := gauge_nonneg hh hc (y-star)
  have habnonneg : 0 ≤ a • γ (x-star) + b • γ (y-star) := by
    simp only [smul_eq_mul]
    positivity
  have hmono := hΦ.strictMono.monotoneOn
    (gauge_nonneg hh hc (a • (x-star) + b • (y-star))) habnonneg hinner
  exact (by simpa only [objective, hid] using
    hmono.trans (hΦ.convex.2 hx hy ha hb hab))

theorem objective_sublevel_compact {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n) (a : ℝ) :
    IsCompact {x | objective Φ γ star x ≤ a} := by
  apply Localization.sublevel_compact (objective_convex hΦ hγ hh hc star) star
  · intro x
    rw [objective_at_center hΦ hh]
    exact objective_nonneg hΦ hh hc star x
  · intro x hx
    rw [objective_at_center hΦ hh] at hx
    exact (objective_eq_zero_iff hΦ hh hc star x).mp hx

theorem transform_hasDerivAt {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {r : ℝ}
    (hr : 0 < r) : HasDerivAt Φ (deriv Φ r) r :=
  ((hΦ.smooth r hr).contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by norm_num) |>.hasDerivAt

/-- Euler's identity comes from the radial curve, without assuming that γ is
differentiable at an accepted endpoint. -/
theorem actual_gradient_euler {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (star x g : Vec n) (hr : 0 < γ (x-star))
    (hg : HasFDerivAt (objective Φ γ star) (gradientFunctional g) x) :
    dot g (x-star) = γ (x-star) * deriv Φ (γ (x-star)) := by
  have hcurve : HasDerivAt (fun t : ℝ => star + t • (x-star)) (x-star) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).smul_const (x-star)).const_add star
  have hactual := hg.comp_hasDerivAt_of_eq 1 hcurve (by simp)
  have hscalar : HasDerivAt (fun t : ℝ => Φ (t * γ (x-star)))
      (deriv Φ (γ (x-star)) * γ (x-star)) 1 := by
    simpa using (show HasDerivAt Φ (deriv Φ (γ (x-star))) (1 * γ (x-star)) by
      simpa using transform_hasDerivAt hΦ hr).comp 1
      ((hasDerivAt_id (1 : ℝ)).mul_const (γ (x-star)))
  have heq : (fun t : ℝ => objective Φ γ star (star + t • (x-star))) =ᶠ[𝓝 1]
      (fun t : ℝ => Φ (t * γ (x-star))) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    simp only [objective, add_sub_cancel_left, hh t ht.le]
  have hs := hactual.congr_of_eventuallyEq heq.symm
  simpa only [gradientFunctional_apply, mul_comm] using hs.unique hscalar

def radialPairing (Φ : ℝ → ℝ) (r : ℝ) := r * deriv Φ r

theorem radialPairing_contDiff {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) :
    ContDiffOn ℝ 1 (radialPairing Φ) (Ioi 0) := by
  exact contDiffOn_id.mul (hΦ.smooth.deriv_of_isOpen isOpen_Ioi (by norm_num))

/-- Scalar mean-value control on a positive gauge annulus. Both the derivative
lower bound and the radial-pairing Lipschitz constant are derived from C². -/
theorem radialPairing_variation_on_annulus {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, s ≤ r →
      |radialPairing Φ s - radialPairing Φ r| ≤ C * (Φ r - Φ s) := by
  have hsub : Icc a b ⊆ Ioi 0 := fun r hr => ha.trans_le hr.1
  have hdcont := hΦ.smooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  obtain ⟨μ, hμ, hlower⟩ := isCompact_Icc.exists_forall_le' (hdcont.mono hsub)
    (fun r hr => hΦ.deriv_pos r (hsub hr))
  have hac := radialPairing_contDiff hΦ
  have hacder := hac.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn (hacder.mono hsub)).isBounded.exists_norm_le
  let D := |M| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D / μ, div_pos hD hμ, ?_⟩
  intro r hr s hs hsr
  have hadiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ (radialPairing Φ) t := by
    intro t ht
    exact ((hac t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt (by norm_num)
  have habound : ∀ t ∈ Icc a b, ‖deriv (radialPairing Φ) t‖ ≤ D := by
    intro t ht
    exact (hM _ (mem_image_of_mem _ ht)).trans (by dsimp [D]; linarith [le_abs_self M])
  have hv := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hadiff habound hr hs
  simp only [Real.norm_eq_abs, abs_sub_comm s r, abs_of_nonneg (sub_nonneg.mpr hsr)] at hv
  have hphidiff : DifferentiableOn ℝ Φ (interior (Icc a b)) := by
    intro t ht
    exact (transform_hasDerivAt hΦ (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt
  have hl := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (hΦ.continuous.mono (show Icc a b ⊆ Ici (0 : ℝ) from
      fun t ht => show (0 : ℝ) ≤ t from le_of_lt (hsub ht))) hphidiff
    (fun t ht => hlower t (interior_subset ht)) s hs r hr hsr
  calc
    |radialPairing Φ s - radialPairing Φ r| ≤ D * (r-s) := hv
    _ ≤ (D / μ) * (Φ r - Φ s) := by
      have hm := mul_le_mul_of_nonneg_left hl (div_pos hD hμ).le
      have he : (D / μ) * (μ * (r-s)) = D * (r-s) := by field_simp; ring
      rwa [he] at hm

theorem exists_gauge_annulus_on_positive_band {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n)
    {K : Set (Vec n)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ K, η ≤ objective Φ γ star x → γ (x-star) ∈ Icc a b := by
  let S := K ∩ {x | η ≤ objective Φ γ star x}
  have hS : IsCompact S := hK.inter_right
    (isClosed_le continuous_const (convex_continuous (objective_convex hΦ hγ hh hc star)))
  have hcont : Continuous (fun x : Vec n => γ (x-star)) :=
    (convex_continuous hγ).comp (continuous_id.sub continuous_const)
  have hpositive : ∀ x ∈ S, 0 < γ (x-star) := by
    intro x hx
    apply Homogeneous.positive_of_bounded_zero_sublevel hh
      (Homogeneous.bounded_zero_sublevel_of_coercive hc)
    intro hz
    have he : x = star := sub_eq_zero.mp hz
    have hv : η ≤ objective Φ γ star x := hx.2
    rw [he, objective_at_center hΦ hh] at hv
    exact (not_le_of_gt hη) hv
  obtain ⟨a, ha, halower⟩ := hS.exists_forall_le' hcont.continuousOn hpositive
  obtain ⟨M, hM⟩ := (hS.image hcont).isBounded.exists_norm_le
  refine ⟨a, |M|+1, ha, ?_⟩
  intro x hx hlevel
  have hxs : x ∈ S := ⟨hx,hlevel⟩
  refine ⟨halower x hxs, ?_⟩
  have hm := hM _ (mem_image_of_mem _ hxs)
  rw [Real.norm_eq_abs] at hm
  linarith [le_abs_self (γ (x-star)), le_abs_self M]

theorem actual_pairing_variation_on_positive_band {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n)
    {K : Set (Vec n)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ z ∈ K, η ≤ objective Φ γ star z →
      objective Φ γ star z ≤ objective Φ γ star x → ∀ g h : Vec n,
      HasFDerivAt (objective Φ γ star) (gradientFunctional g) x →
      HasFDerivAt (objective Φ γ star) (gradientFunctional h) z →
      |dot h (z-star) - dot g (x-star)| ≤
        C * (objective Φ γ star x - objective Φ γ star z) := by
  obtain ⟨a,b,ha,hann⟩ := exists_gauge_annulus_on_positive_band hΦ hγ hh hc star hK hη
  obtain ⟨C,hC,hbound⟩ := radialPairing_variation_on_annulus (b := b) hΦ ha
  refine ⟨C,hC,?_⟩
  intro x hx z hz hzlevel hzx g h hg hhg
  have hxann := hann x hx (hzlevel.trans hzx)
  have hzann := hann z hz hzlevel
  have horder : γ (z-star) ≤ γ (x-star) := by
    by_contra hn
    have ho := hΦ.strictMono (gauge_nonneg hh hc (x-star))
      (gauge_nonneg hh hc (z-star)) (lt_of_not_ge hn)
    exact (not_lt_of_ge hzx) ho
  rw [actual_gradient_euler hΦ hh star x g (ha.trans_le hxann.1) hg,
    actual_gradient_euler hΦ hh star z h (ha.trans_le hzann.1) hhg]
  exact hbound _ hxann _ hzann horder

/-- Exact source coefficient from the scalar pairing bound, Armijo, convexity,
and weak Wolfe. -/
theorem correction_numeric {d t Δ e C κ c : ℝ} (hd : 0 < d) (hκ : 0 < κ)
    (hc : 0 < c) (hC : 0 ≤ C) (hΔd : Δ ≤ d) (hcd : c*d ≤ Δ)
    (hκd : κ*d ≤ t) (he : |e| ≤ C*Δ) :
    (d+e)^2/t ≤ (1+C)^2/(κ*c)*Δ := by
  have hΔ : 0 < Δ := (mul_pos hc hd).trans_le hcd
  have ht : 0 < t := (mul_pos hκ hd).trans_le hκd
  have hn : |d+e| ≤ (1+C)*d := by
    calc
      |d+e| ≤ |d|+|e| := abs_add _ _
      _ ≤ d+C*Δ := by rw [abs_of_pos hd]; linarith
      _ ≤ (1+C)*d := by nlinarith [mul_le_mul_of_nonneg_left hΔd hC]
  have hs : (d+e)^2 ≤ ((1+C)*d)^2 := by
    have hb : 0 ≤ (1+C)*d := mul_nonneg (by linarith) hd.le
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (d+e)) hb).mpr hn
  apply (div_le_iff₀ ht).mpr
  have hprod : (c*d)*(κ*d) ≤ Δ*t := mul_le_mul hcd hκd (mul_pos hκ hd).le hΔ.le
  have hmul := mul_le_mul_of_nonneg_left hprod
    (div_nonneg (sq_nonneg (1+C)) (mul_pos hκ hc).le)
  have hid : (1+C)^2/(κ*c)*((c*d)*(κ*d)) = ((1+C)*d)^2 := by
    field_simp
    ring
  rw [hid] at hmul
  exact hs.trans (by simpa only [mul_assoc] using hmul)

end BfgsVerification.TransformedGauge

namespace BfgsVerification.AdmissibleBFGSRun
open TransformedGauge

theorem reference_new_pairing_difference {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (star : Vec n) (k : ℕ) :
    dot (R.gradientChange k) (R.x (k+1)-star) =
      R.d k + (R.referencePairing star (k+1)-R.referencePairing star k) := by
  have hstep : dot (R.g k) (R.x (k+1)-star) =
      R.referencePairing star k-R.d k := by
    rw [R.step]
    have he : R.x k + bfgsStep (R.H k) (R.g k) (R.α k)-star =
        (R.x k-star)+bfgsStep (R.H k) (R.g k) (R.α k) := by abel
    rw [he]
    change R.g k ⬝ᵥ ((R.x k-star)+bfgsStep (R.H k) (R.g k) (R.α k)) = _
    rw [dotProduct_add]
    change R.referencePairing star k + dot (R.g k) (bfgsStep _ _ _) = _
    rw [R.dot_step_eq_neg_d]
    ring
  change (R.g (k+1)-R.g k) ⬝ᵥ (R.x (k+1)-star) = _
  rw [sub_dotProduct]
  change R.referencePairing star (k+1) - dot (R.g k) (R.x (k+1)-star) = _
  rw [hstep]
  ring

theorem transformedGauge_correction_on_positive_band {n : ℕ} {Φ : ℝ → ℝ}
    {γ : Vec n → ℝ} (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ) (hc : Tendsto γ (cocompact (Vec n)) atTop)
    (star : Vec n) (R : AdmissibleBFGSRun n (objective Φ γ star))
    {η : ℝ} (hη : 0 < η) (hlevels : ∀ k, η ≤ objective Φ γ star (R.x k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, R.referenceCorrection star k ≤
      ((1+C)^2/((1-R.c₂)*R.c₁)) *
        (objective Φ γ star (R.x k)-objective Φ γ star (R.x (k+1))) := by
  have hK : IsCompact R.initialSublevel := objective_sublevel_compact hΦ hγ hh hc star _
  obtain ⟨C,hC,hbound⟩ := actual_pairing_variation_on_positive_band hΦ hγ hh hc star hK hη
  refine ⟨C,hC,?_⟩
  intro k
  have hv := hbound (R.x k) (R.iterate_mem_initialSublevel k)
    (R.x (k+1)) (R.iterate_mem_initialSublevel (k+1)) (hlevels (k+1))
    (R.objective_antitone (Nat.le_succ k)) (R.g k) (R.g (k+1))
    (R.hasGradient k) (R.hasGradient (k+1))
  unfold referenceCorrection
  rw [R.reference_new_pairing_difference]
  exact correction_numeric (R.d_pos k) R.wolfe_constant_pos R.c₁_pos hC.le
    (R.convexity_decrease_upper k) (R.armijo_decrease k) (R.curvature_lower_bound k) hv

/-- The positive-limit branch has summable actual corrections; no correction
budget is assumed in the source hypotheses. -/
theorem transformedGauge_corrections_summable_on_positive_band {n : ℕ} {Φ : ℝ → ℝ}
    {γ : Vec n → ℝ} (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ) (hc : Tendsto γ (cocompact (Vec n)) atTop)
    (star : Vec n) (R : AdmissibleBFGSRun n (objective Φ γ star))
    {η : ℝ} (hη : 0 < η) (hlevels : ∀ k, η ≤ objective Φ γ star (R.x k)) :
    Summable (R.referenceCorrection star) := by
  obtain ⟨C,hC,hbound⟩ := R.transformedGauge_correction_on_positive_band hΦ hγ hh hc star hη hlevels
  let D := (1+C)^2/((1-R.c₂)*R.c₁)
  have hD : 0 ≤ D := div_nonneg (sq_nonneg _) (mul_pos R.wolfe_constant_pos R.c₁_pos).le
  apply Summable.of_nonneg_of_le (R.referenceCorrection_nonneg star)
    (fun k => (hbound k).trans (mul_le_mul_of_nonneg_left (R.convexity_decrease_upper k) hD))
  exact (R.summable_predicted_decreases_of_lower_bound 0
    (fun k => objective_nonneg hΦ hh hc star (R.x k))).mul_left D

/-- Full BFGS on every source transformed gauge converges in objective value.
The positive-limit case derives the source correction estimate and invokes the
verified actual-matrix reciprocal theorem. -/
theorem transformedGauge_values {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ) (hc : Tendsto γ (cocompact (Vec n)) atTop)
    (star : Vec n) (R : AdmissibleBFGSRun n (objective Φ γ star)) :
    Tendsto (fun k => objective Φ γ star (R.x k)) atTop (𝓝 0) := by
  have hnonneg := fun k => objective_nonneg hΦ hh hc star (R.x k)
  obtain ⟨ℓ,hlim⟩ := R.objective_value_limit_of_lower_bound 0 hnonneg
  have hfloor : 0 ≤ ℓ := ge_of_tendsto hlim (Eventually.of_forall hnonneg)
  by_cases heq : ℓ = 0
  · simpa only [heq] using hlim
  have hℓ : 0 < ℓ := lt_of_le_of_ne hfloor (Ne.symm heq)
  have hlevels : ∀ k, ℓ ≤ objective Φ γ star (R.x k) := R.objective_antitone.le_of_tendsto hlim
  have hs := R.transformedGauge_corrections_summable_on_positive_band hΦ hγ hh hc star hℓ hlevels
  have hK : IsCompact R.initialSublevel := objective_sublevel_compact hΦ hγ hh hc star _
  have hmin : ∀ x, objective Φ γ star star ≤ objective Φ γ star x := by
    intro x
    rw [objective_at_center hΦ hh]
    exact objective_nonneg hΦ hh hc star x
  have hSnonneg : 0 ≤ ∑' k, R.referenceCorrection star k := tsum_nonneg (R.referenceCorrection_nonneg star)
  have hbudget : ∀ᶠ N : ℕ in atTop, (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤
      (∑' k, R.referenceCorrection star k) * (N : ℝ)^2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    apply (hs.sum_le_tsum _ (fun k _ => R.referenceCorrection_nonneg star k)).trans
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_nonneg hSnonneg (show 0 ≤ (N : ℝ)^2-1 by nlinarith)]
  have hv := R.compact_objective_tendsto_min_of_quadratic_corrections star hmin hK
    (∑' k, R.referenceCorrection star k) hbudget
  simpa only [objective_at_center hΦ hh] using hv

/-- Exact source F:transform, with compactness and the unique minimizer derived
from finite convex coercivity and strict increase. -/
theorem transformedGauge_convergence {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ) (hc : Tendsto γ (cocompact (Vec n)) atTop)
    (star : Vec n) (R : AdmissibleBFGSRun n (objective Φ γ star)) :
    Tendsto (fun k => objective Φ γ star (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 star) := by
  have hv := R.transformedGauge_values hΦ hγ hh hc star
  refine ⟨hv, R.iterates_tendsto_unique_min_of_values star ?_ ?_ ?_⟩
  · intro x
    rw [objective_at_center hΦ hh]
    exact objective_nonneg hΦ hh hc star x
  · intro x hx
    rw [objective_at_center hΦ hh] at hx
    exact (objective_eq_zero_iff hΦ hh hc star x).mp hx
  · simpa only [objective_at_center hΦ hh] using hv

end BfgsVerification.AdmissibleBFGSRun
