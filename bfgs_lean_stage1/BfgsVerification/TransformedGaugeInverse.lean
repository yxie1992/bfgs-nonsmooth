import BfgsVerification.TransformedGauge
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-! The actual half-line inverse and Θ derivative used in the source F:transform
proof. These interpretations are independent of the inverse-free convergence
argument in `TransformedGauge`. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.TransformedGauge

theorem transform_tendsto_atTop {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) :
    Tendsto Φ atTop atTop := by
  have hp : 0 < deriv Φ 1 := hΦ.deriv_pos 1 (by norm_num)
  have hline : Tendsto (fun r : ℝ => deriv Φ 1 * (r-1) + Φ 1) atTop atTop := by
    have hmul := (tendsto_const_mul_atTop_of_pos hp).mpr
      (show Tendsto (fun r : ℝ => r-1) atTop atTop by
        simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    exact tendsto_atTop_add_const_right atTop (Φ 1) hmul
  apply tendsto_atTop_mono' atTop ?_ hline
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hs := hΦ.convex.le_slope_of_hasDerivAt (by norm_num : (1 : ℝ) ∈ Ici 0)
    (show r ∈ Ici 0 by exact (by norm_num : (0 : ℝ) < 1).trans hr |>.le)
    hr (transform_hasDerivAt hΦ (by norm_num))
  rw [slope_def_field] at hs
  have hm := (le_div_iff₀ (sub_pos.mpr hr)).mp hs
  linarith

theorem transform_nonneg {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ Φ r := by
  simpa only [hΦ.zero] using hΦ.strictMono.monotoneOn (by norm_num : (0 : ℝ) ∈ Ici 0) hr hr

theorem transform_positive {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {r : ℝ}
    (hr : 0 < r) : 0 < Φ r := by
  simpa only [hΦ.zero] using hΦ.strictMono (by norm_num : (0 : ℝ) ∈ Ici 0) hr.le hr

theorem transform_surjOn {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) :
    SurjOn Φ (Ici 0) (Ici 0) := by
  have h := isPreconnected_Ici.intermediate_value_Ici (a := (0 : ℝ))
    (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (show (atTop : Filter ℝ) ≤ 𝓟 (Ici 0) from le_principal_iff.mpr (eventually_ge_atTop 0))
    hΦ.continuous (transform_tendsto_atTop hΦ)
  simpa only [hΦ.zero] using h

def inverse (Φ : ℝ → ℝ) : ℝ → ℝ := Function.invFunOn Φ (Ici 0)

theorem inverse_nonneg {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ inverse Φ t := Function.invFunOn_mem (transform_surjOn hΦ ht)

theorem transform_inverse {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {t : ℝ} (ht : 0 ≤ t) :
    Φ (inverse Φ t) = t := Function.invFunOn_eq (transform_surjOn hΦ ht)

theorem inverse_transform {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {r : ℝ} (hr : 0 ≤ r) :
    inverse Φ (Φ r) = r := hΦ.strictMono.injOn.leftInvOn_invFunOn hr

theorem inverse_positive {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {t : ℝ} (ht : 0 < t) :
    0 < inverse Φ t := by
  have hn := inverse_nonneg hΦ ht.le
  by_contra h
  have hz : inverse Φ t = 0 := le_antisymm (le_of_not_gt h) hn
  have he := transform_inverse hΦ ht.le
  rw [hz,hΦ.zero] at he
  linarith

theorem inverse_strictMonoOn {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) :
    StrictMonoOn (inverse Φ) (Ici 0) := by
  intro s hs t ht hst
  by_contra h
  have hi := hΦ.strictMono.monotoneOn (inverse_nonneg hΦ ht) (inverse_nonneg hΦ hs)
    (le_of_not_gt h)
  rw [transform_inverse hΦ ht,transform_inverse hΦ hs] at hi
  exact (not_le_of_gt hst) hi

theorem inverse_image {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) :
    inverse Φ '' Ici 0 = Ici 0 := by
  ext r
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact inverse_nonneg hΦ ht
  · intro hr
    exact ⟨Φ r,transform_nonneg hΦ hr,inverse_transform hΦ hr⟩

theorem inverse_continuousAt {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (inverse Φ) t := by
  apply (inverse_strictMonoOn hΦ).continuousAt_of_image_mem_nhds
    (Ici_mem_nhds ht)
  rw [inverse_image hΦ]
  exact Ici_mem_nhds (inverse_positive hΦ ht)

theorem inverse_hasDerivAt {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (inverse Φ) (deriv Φ (inverse Φ t))⁻¹ t := by
  apply HasDerivAt.of_local_left_inverse (inverse_continuousAt hΦ ht)
    (transform_hasDerivAt hΦ (inverse_positive hΦ ht))
    (hΦ.deriv_pos _ (inverse_positive hΦ ht)).ne'
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact transform_inverse hΦ hs.le

def theta (Φ : ℝ → ℝ) (t : ℝ) := inverse Φ t * deriv Φ (inverse Φ t)

theorem radialPairing_hasDerivAt {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {r : ℝ}
    (hr : 0 < r) : HasDerivAt (radialPairing Φ)
      (deriv Φ r + r * deriv (deriv Φ) r) r := by
  have hd : ContDiffOn ℝ 1 (deriv Φ) (Ioi 0) :=
    hΦ.smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdd := ((hd r hr).contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by norm_num)
  simpa only [one_mul] using (hasDerivAt_id r).mul hdd.hasDerivAt

/-- The literal source derivative, with r = Φ⁻¹(t). -/
theorem theta_hasDerivAt {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (theta Φ)
      (1 + inverse Φ t * deriv (deriv Φ) (inverse Φ t) / deriv Φ (inverse Φ t)) t := by
  have hd := (radialPairing_hasDerivAt hΦ (inverse_positive hΦ ht)).comp t
    (inverse_hasDerivAt hΦ ht)
  have hp := (hΦ.deriv_pos _ (inverse_positive hΦ ht)).ne'
  have he : (deriv Φ (inverse Φ t) + inverse Φ t * deriv (deriv Φ) (inverse Φ t)) *
      (deriv Φ (inverse Φ t))⁻¹ =
        1 + inverse Φ t * deriv (deriv Φ) (inverse Φ t) / deriv Φ (inverse Φ t) := by
    field_simp
  simpa only [he, Function.comp_def, radialPairing, theta] using hd

theorem actual_gradient_eq_theta {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (star x g : Vec n) (hr : 0 < γ (x-star))
    (hg : HasFDerivAt (objective Φ γ star) (gradientFunctional g) x) :
    dot g (x-star) = theta Φ (objective Φ γ star x) := by
  rw [actual_gradient_euler hΦ hh star x g hr hg]
  simp only [theta, objective, inverse_transform hΦ hr.le]

theorem theta_derivative_continuousOn {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ) :
    ContinuousOn (deriv (theta Φ)) (Ioi 0) := by
  intro t ht
  have hr := inverse_positive hΦ ht
  have hd1 : ContDiffOn ℝ 1 (deriv Φ) (Ioi 0) :=
    hΦ.smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc1 : ContinuousAt (deriv Φ) (inverse Φ t) :=
    hd1.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hr)
  have hc2 : ContinuousAt (deriv (deriv Φ)) (inverse Φ t) :=
    (hd1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).continuousAt (isOpen_Ioi.mem_nhds hr)
  have hi := inverse_continuousAt hΦ ht
  have hc : ContinuousAt (fun s => 1 + inverse Φ s * deriv (deriv Φ) (inverse Φ s) /
      deriv Φ (inverse Φ s)) t :=
    continuousAt_const.add ((hi.mul (hc2.comp hi)).div (hc1.comp hi) (hΦ.deriv_pos _ hr).ne')
  have heq : deriv (theta Φ) =ᶠ[𝓝 t] (fun s => 1 + inverse Φ s * deriv (deriv Φ) (inverse Φ s) /
      deriv Φ (inverse Φ s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (theta_hasDerivAt hΦ hs).deriv
  exact (hc.congr_of_eventuallyEq heq).continuousWithinAt

/-- The source Θ′ is bounded on every closed positive objective interval. -/
theorem theta_derivative_bounded {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ)
    {a b : ℝ} (ha : 0 < a) : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc a b, |deriv (theta Φ) t| ≤ C := by
  have hsub : Icc a b ⊆ Ioi 0 := fun t ht => ha.trans_le ht.1
  obtain ⟨M,hM⟩ := (isCompact_Icc.image_of_continuousOn
    ((theta_derivative_continuousOn hΦ).mono hsub)).isBounded.exists_norm_le
  refine ⟨|M|+1,by positivity,?_⟩
  intro t ht
  have h := hM _ (mem_image_of_mem _ ht)
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self M]

/-- The source Θ mean-value inequality, now using the actual inverse function. -/
theorem theta_lipschitz_on_positive_interval {Φ : ℝ → ℝ} (hΦ : IncreasingTransform Φ)
    {a b : ℝ} (ha : 0 < a) : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc a b, ∀ u ∈ Icc a b,
      |theta Φ u - theta Φ t| ≤ C * |u-t| := by
  obtain ⟨C,hC,hbound⟩ := theta_derivative_bounded (b := b) hΦ ha
  refine ⟨C,hC,?_⟩
  intro t ht u hu
  simpa only [Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (theta_hasDerivAt hΦ (ha.trans_le hs.1)).differentiableAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs) ht hu

/-- Differentiability of the gauge at a positive differentiable endpoint is a
consequence of the actual inverse chain rule, not an extra run hypothesis. -/
theorem gauge_hasFDerivAt_of_objective {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star x g : Vec n)
    (hr : 0 < γ (x-star))
    (hg : HasFDerivAt (objective Φ γ star) (gradientFunctional g) x) :
    HasFDerivAt γ ((deriv Φ (γ (x-star)))⁻¹ • gradientFunctional g) (x-star) := by
  have hi := inverse_hasDerivAt hΦ (transform_positive hΦ hr)
  have hd := hi.comp_hasFDerivAt x hg
  simp only [objective, inverse_transform hΦ hr.le] at hd
  have hd' : HasFDerivAt (inverse Φ ∘ objective Φ γ star)
      ((deriv Φ (γ (x-star)))⁻¹ • gradientFunctional g) (x-star+star) := by
    simpa only [sub_add_cancel] using hd
  have htrans := hd'.comp (x-star) ((hasFDerivAt_id (x-star)).add_const star)
  simp only [ContinuousLinearMap.comp_id] at htrans
  apply htrans.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => by
    simp only [Function.comp_def, id_eq, objective, add_sub_cancel_right,
      inverse_transform hΦ (gauge_nonneg hh hc z)]

theorem objective_coercive {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hγ : ConvexOn ℝ univ γ)
    (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n) :
    Tendsto (objective Φ γ star) (cocompact (Vec n)) atTop := by
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [(objective_sublevel_compact hΦ hγ hh hc star a).compl_mem_cocompact]
    with x hx
  change ¬ objective Φ γ star x ≤ a at hx
  exact (lt_of_not_ge hx).le

end BfgsVerification.TransformedGauge

namespace BfgsVerification.AdmissibleBFGSRun
open TransformedGauge

theorem transformedGauge_radius_pos {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n)
    (R : AdmissibleBFGSRun n (objective Φ γ star)) (k : ℕ) :
    0 < γ (R.x k-star) := by
  apply Homogeneous.positive_of_bounded_zero_sublevel hh
    (Homogeneous.bounded_zero_sublevel_of_coercive hc)
  intro hz
  have hx := sub_eq_zero.mp hz
  have hd := R.objective_strict_decrease k
  have hn := objective_nonneg hΦ hh hc star (R.x (k+1))
  rw [hx,objective_at_center hΦ hh] at hd
  linarith

/-- The source a_k = r_k Φ′(r_k) = Θ(F_k) holds at every accepted iterate. -/
theorem transformedGauge_euler {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n)
    (R : AdmissibleBFGSRun n (objective Φ γ star)) (k : ℕ) :
    R.referencePairing star k = γ (R.x k-star) * deriv Φ (γ (R.x k-star)) ∧
      R.referencePairing star k = theta Φ (objective Φ γ star (R.x k)) := by
  have hr := R.transformedGauge_radius_pos hΦ hh hc star k
  exact ⟨actual_gradient_euler hΦ hh star (R.x k) (R.g k) hr (R.hasGradient k),
    actual_gradient_eq_theta hΦ hh star (R.x k) (R.g k) hr (R.hasGradient k)⟩

theorem transformedGauge_actual_gauge_derivative {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}
    (hΦ : IncreasingTransform Φ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hc : Tendsto γ (cocompact (Vec n)) atTop) (star : Vec n)
    (R : AdmissibleBFGSRun n (objective Φ γ star)) (k : ℕ) :
    HasFDerivAt γ ((deriv Φ (γ (R.x k-star)))⁻¹ • gradientFunctional (R.g k)) (R.x k-star) :=
  gauge_hasFDerivAt_of_objective hΦ hh hc star (R.x k) (R.g k)
    (R.transformedGauge_radius_pos hΦ hh hc star k) (R.hasGradient k)

end BfgsVerification.AdmissibleBFGSRun
