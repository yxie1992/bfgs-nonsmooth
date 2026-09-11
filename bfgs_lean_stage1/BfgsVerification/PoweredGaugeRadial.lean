import BfgsVerification.InwardRadial
import BfgsVerification.Homogeneous
import BfgsVerification.CenteredLocalUniform
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Scalar real-power profiles for source R.6. No integer-exponent restriction
and no bound on a full spatial Hessian is used. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.RadialPower

def profile (p t : ℝ) := (1-t)^p

theorem profile_contDiffOn_Iio (p : ℝ) {N : WithTop ℕ∞} :
    ContDiffOn ℝ N (profile p) (Iio 1) := by
  apply (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
  intro t ht
  exact (sub_pos.mpr ht).ne'

theorem profile_contDiff (p : ℝ) : ContDiffOn ℝ 2 (profile p) (Icc 0 (1/2)) := by
  apply (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
  intro t ht
  have hp : 0 < 1-t := by linarith [ht.2]
  exact hp.ne'

theorem profile_hasDerivAt (p : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (profile p) (-p*(1-t)^(p-1)) t := by
  have hp : 1-t ≠ 0 := (sub_pos.mpr ht).ne'
  convert ((hasDerivAt_id t).const_sub 1).rpow_const (Or.inl hp) using 1 <;>
    dsimp only [profile,id_eq] <;> ring

theorem profile_hasDerivAt_zero (p : ℝ) : HasDerivAt (profile p) (-p) 0 := by
  simpa only [sub_zero, Real.one_rpow, mul_one] using profile_hasDerivAt p (by norm_num : (0 : ℝ) < 1)

theorem profile_derivative_hasDerivAt (p : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (deriv (profile p)) (p*(p-1)*(1-t)^(p-2)) t := by
  have hp : 1-t ≠ 0 := (sub_pos.mpr ht).ne'
  have hd := (((hasDerivAt_id t).const_sub 1).rpow_const (p := p-1) (Or.inl hp)).const_mul (-p)
  have heq : deriv (profile p) =ᶠ[𝓝 t] (fun u => -p*(1-u)^(p-1)) := by
    filter_upwards [eventually_lt_nhds ht] with u hu
    exact (profile_hasDerivAt p hu).deriv
  have he : p-1-1 = p-2 := by ring
  convert hd.congr_of_eventuallyEq heq using 1 <;> simp only [id_eq,he] <;> ring

theorem profile_second_derivative_bounded (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 (1/2), |deriv (deriv (profile p)) t| ≤ C := by
  have hd : ContDiffOn ℝ 1 (deriv (profile p)) (Iio 1) :=
    (profile_contDiffOn_Iio (N := 2) p).deriv_of_isOpen isOpen_Iio (by norm_num)
  have hc := hd.continuousOn_deriv_of_isOpen isOpen_Iio (by norm_num)
  have hsub : Icc (0 : ℝ) (1/2) ⊆ Iio 1 := fun t ht => lt_of_le_of_lt ht.2 (by norm_num)
  obtain ⟨M,hM⟩ := (isCompact_Icc.image_of_continuousOn (hc.mono hsub)).isBounded.exists_norm_le
  refine ⟨|M|+1,by positivity,?_⟩
  intro t ht
  have hm := hM _ (mem_image_of_mem _ ht)
  rw [Real.norm_eq_abs] at hm
  linarith [le_abs_self M]

theorem profile_one_zero_remainder (t : ℝ) : (1-t)^(1 : ℝ)-1+1*t = 0 := by
  rw [Real.rpow_one]
  ring

/-- Signed finite sublinear functions have exactly zero radial error. This
first source case does not need the nonnegativity used for arbitrary powers. -/
theorem degree_one_inward_error_zero {n : ℕ} {γ : Vec n → ℝ}
    (hγ : ConvexOn ℝ univ γ) (hh : Homogeneous.PositiveDegreeOne γ)
    (star : Vec n) {x g : Vec n}
    (hg : HasFDerivAt (fun w => γ (w-star)) (gradientFunctional g) x)
    {t : ℝ} (ht : t ≤ 1) :
    RadialCertificate.supportingError (fun w => γ (w-star)) x g
      (RadialCertificate.inwardPoint star x t) = 0 := by
  have hd : HasFDerivAt (fun w => γ (w-star)) (gradientFunctional g) (x-star+star) := by
    simpa only [sub_add_cancel] using hg
  have hc := hd.comp (x-star) ((hasFDerivAt_id (x-star)).add_const star)
  simp only [ContinuousLinearMap.comp_id] at hc
  have hactual : HasFDerivAt γ (gradientFunctional g) (x-star) := by
    apply hc.congr_of_eventuallyEq
    exact Eventually.of_forall (fun w => by simp)
  have he := Homogeneous.supporting_euler hh (convex_supporting_inequality hγ hactual)
  rw [RadialCertificate.inward_error_eq]
  have hrad : RadialCertificate.inwardPoint star x t-star = (1-t) • (x-star) := by
    unfold RadialCertificate.inwardPoint
    module
  rw [hrad,hh (1-t) (sub_nonneg.mpr ht),he]
  ring

theorem profile_taylor_polynomial (p t : ℝ) :
    taylorWithinEval (profile p) 1 (Icc 0 (1/2)) 0 t = 1-p*t := by
  have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) (1/2)) 0 :=
    uniqueDiffOn_Icc (by norm_num) 0 (by constructor <;> norm_num)
  have hd : derivWithin (profile p) (Icc 0 (1/2)) 0 = -p :=
    (profile_hasDerivAt_zero p).hasDerivWithinAt.derivWithin hu
  change taylorWithinEval (profile p) (0+1) (Icc 0 (1/2)) 0 t = _
  rw [taylorWithinEval_succ]
  simp only [taylor_within_zero_eval, iteratedDerivWithin_one, hd, Nat.cast_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, one_mul, inv_one, sub_zero, pow_one, smul_eq_mul,
    profile, Real.one_rpow]
  ring

/-- Uniform fractional radial Taylor bound for every real exponent. In the
convex gauge family p≥1, this includes the whole interval 1<p<2. -/
theorem profile_taylor_bound (p : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 (1/2),
    |(1-t)^p-1+p*t| ≤ C*t^2 := by
  obtain ⟨C,hC⟩ := exists_taylor_mean_remainder_bound (n := 1)
    (by norm_num : (0 : ℝ) ≤ 1/2) (profile_contDiff p)
  refine ⟨max C 0+1,by positivity,?_⟩
  intro t ht
  have hb := hC t ht
  rw [profile_taylor_polynomial] at hb
  simp only [Real.norm_eq_abs,sub_zero,profile] at hb
  have he : (1-t)^p-(1-p*t) = (1-t)^p-1+p*t := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left C 0]) (sq_nonneg t))

def powered {n : ℕ} (γ : Vec n → ℝ) (p : ℝ) (x : Vec n) := (γ x)^p

theorem powered_homogeneous {n : ℕ} {γ : Vec n → ℝ}
    (hh : Homogeneous.PositiveDegreeOne γ) (hn : ∀ x, 0 ≤ γ x) (p : ℝ)
    (a : ℝ) (ha : 0 ≤ a) (x : Vec n) : powered γ p (a • x) = a^p*powered γ p x := by
  simp only [powered,hh a ha x,Real.mul_rpow ha (hn x)]

theorem powered_nonneg {n : ℕ} (γ : Vec n → ℝ) (hn : ∀ x, 0 ≤ γ x)
    (p : ℝ) (x : Vec n) : 0 ≤ powered γ p x := Real.rpow_nonneg (hn x) p

theorem powered_convex {n : ℕ} {γ : Vec n → ℝ} (hγ : ConvexOn ℝ univ γ)
    (hn : ∀ x, 0 ≤ γ x) {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ univ (powered γ p) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have hinner := hγ.2 (mem_univ x) (mem_univ y) ha hb hab
  have hnonneg : 0 ≤ a • γ x+b • γ y := by
    exact add_nonneg (mul_nonneg ha (hn x)) (mul_nonneg hb (hn y))
  have hm := Real.rpow_le_rpow (hn (a • x+b • y)) hinner (by linarith : 0 ≤ p)
  exact hm.trans ((convexOn_rpow hp).2 (hn x) (hn y) ha hb hab)

def sumObjective {n : ℕ} {ι : Type*} [Fintype ι]
    (Γ : ι → Vec n → ℝ) (p : ι → ℝ) (star x : Vec n) := ∑ j, powered (Γ j) (p j) (x-star)

theorem inward_radius {n : ℕ} (star x : Vec n) (t : ℝ) :
    RadialCertificate.inwardPoint star x t-star = (1-t) • (x-star) := by
  unfold RadialCertificate.inwardPoint
  module

theorem sumObjective_inward {n : ℕ} {ι : Type*} [Fintype ι]
    {Γ : ι → Vec n → ℝ} (hh : ∀ j, Homogeneous.PositiveDegreeOne (Γ j))
    (hn : ∀ j x, 0 ≤ Γ j x) (p : ι → ℝ) (star x : Vec n) {t : ℝ} (ht : t ≤ 1) :
    sumObjective Γ p star (RadialCertificate.inwardPoint star x t) =
      ∑ j, profile (p j) t * powered (Γ j) (p j) (x-star) := by
  simp only [sumObjective,inward_radius,powered_homogeneous (hh _) (hn _) _ _ (sub_nonneg.mpr ht),profile]

/-- The derivative in the radial direction is obtained from the actual full
objective derivative and the explicit scalar power profiles. No derivative
of any gauge is assumed. -/
theorem actual_radial_pairing {n : ℕ} {ι : Type*} [Fintype ι]
    {F ψ : Vec n → ℝ} {Γ : ι → Vec n → ℝ}
    (hh : ∀ j, Homogeneous.PositiveDegreeOne (Γ j)) (hn : ∀ j x, 0 ≤ Γ j x)
    (p : ι → ℝ) (star : Vec n) {U : Set (Vec n)} (hU : IsOpen U)
    (hrep : ∀ x ∈ U, F x = ψ x+sumObjective Γ p star x)
    {x g : Vec n} (hx : x ∈ U) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hψ : DifferentiableAt ℝ ψ x) :
    dot g (x-star) = (fderiv ℝ ψ x) (x-star) + ∑ j, p j*powered (Γ j) (p j) (x-star) := by
  have hcurve : HasDerivAt (fun t => RadialCertificate.inwardPoint star x t) (-(x-star)) 0 := by
    simpa only [RadialCertificate.inwardPoint,one_smul,zero_sub] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (x-star)).const_sub x
  have hdF := hg.comp_hasDerivAt_of_eq 0 hcurve (by simp [RadialCertificate.inwardPoint])
  have hdψ := hψ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp [RadialCertificate.inwardPoint])
  have hdterm (j : ι) : HasDerivAt (fun t => profile (p j) t*powered (Γ j) (p j) (x-star))
      (-p j*powered (Γ j) (p j) (x-star)) 0 :=
    (profile_hasDerivAt_zero (p j)).mul_const _
  have hdsum := HasDerivAt.sum (u := Finset.univ) (fun j _ => hdterm j)
  have hdmodel := hdψ.add hdsum
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), RadialCertificate.inwardPoint star x t ∈ U :=
    hcurve.continuousAt.eventually (by simpa [RadialCertificate.inwardPoint] using hU.mem_nhds hx)
  have heq : (fun t => F (RadialCertificate.inwardPoint star x t)) =ᶠ[𝓝 0]
      (fun t => ψ (RadialCertificate.inwardPoint star x t) +
        ∑ j, profile (p j) t*powered (Γ j) (p j) (x-star)) := by
    filter_upwards [hnear,eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht ht1
    rw [hrep _ ht,sumObjective_inward hh hn p star x ht1.le]
  have hder := (hdF.congr_of_eventuallyEq heq.symm).unique hdmodel
  simp only [gradientFunctional_apply,map_neg] at hder
  have hsum : (∑ j, -p j*powered (Γ j) (p j) (x-star)) =
      -(∑ j, p j*powered (Γ j) (p j) (x-star)) := by
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [hsum] at hder
  linarith

theorem inward_error_decomposition {n : ℕ} {ι : Type*} [Fintype ι]
    {F ψ : Vec n → ℝ} {Γ : ι → Vec n → ℝ}
    (hh : ∀ j, Homogeneous.PositiveDegreeOne (Γ j)) (hn : ∀ j x, 0 ≤ Γ j x)
    (p : ι → ℝ) (star : Vec n) {U : Set (Vec n)} (hU : IsOpen U)
    (hrep : ∀ x ∈ U, F x = ψ x+sumObjective Γ p star x)
    {x g : Vec n} (hx : x ∈ U) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hψ : DifferentiableAt ℝ ψ x) {t : ℝ} (ht : t ≤ 1)
    (hi : RadialCertificate.inwardPoint star x t ∈ U) :
    RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint star x t) =
      (ψ (RadialCertificate.inwardPoint star x t)-ψ x + t*(fderiv ℝ ψ x) (x-star)) +
      ∑ j, ((1-t)^(p j)-1+p j*t)*powered (Γ j) (p j) (x-star) := by
  rw [RadialCertificate.inward_error_eq,actual_radial_pairing hh hn p star hU hrep hx hg hψ,
    hrep _ hi,hrep _ hx,sumObjective_inward hh hn p star x ht]
  simp only [sumObjective,profile,Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,add_mul,sub_mul,one_mul]
  have hm : (∑ j, p j*t*powered (Γ j) (p j) (x-star)) =
      ∑ j, t*(p j*powered (Γ j) (p j) (x-star)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hm]
  simp only [mul_add,Finset.mul_sum,mul_assoc]
  ring

theorem powered_values_bounded_on_compact {n : ℕ} {ι : Type*} [Fintype ι]
    {Γ : ι → Vec n → ℝ} (hΓ : ∀ j, ConvexOn ℝ univ (Γ j))
    (hn : ∀ j x, 0 ≤ Γ j x) {p : ι → ℝ} (hp : ∀ j, 1 ≤ p j)
    (star : Vec n) {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ B : ι → ℝ, (∀ j, 0 < B j) ∧ ∀ j x, x ∈ K → powered (Γ j) (p j) (x-star) ≤ B j := by
  have hex (j : ι) : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, powered (Γ j) (p j) (x-star) ≤ B := by
    have hc : Continuous (fun x => powered (Γ j) (p j) (x-star)) :=
      (convex_continuous (powered_convex (hΓ j) (hn j) (hp j))).comp (continuous_id.sub continuous_const)
    obtain ⟨M,hM⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨|M|+1,by positivity,fun x hx => (hM ⟨x,hx,rfl⟩).trans (by linarith [le_abs_self M])⟩
  choose B hB hb using hex
  exact ⟨B,hB,hb⟩

theorem uniform_power_remainder {n : ℕ} {ι : Type*} [Fintype ι]
    {Γ : ι → Vec n → ℝ} (hΓ : ∀ j, ConvexOn ℝ univ (Γ j))
    (hn : ∀ j x, 0 ≤ Γ j x) {p : ι → ℝ} (hp : ∀ j, 1 ≤ p j)
    (star : Vec n) {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ x ∈ K, ∀ t ∈ Icc 0 (1/2),
      (∑ j, ((1-t)^(p j)-1+p j*t)*powered (Γ j) (p j) (x-star)) ≤ P*t^2 := by
  obtain ⟨B,hB,hb⟩ := powered_values_bounded_on_compact hΓ hn hp star hK
  choose C hC hc using fun j => profile_taylor_bound (p j)
  refine ⟨∑ j, C j*B j, Finset.sum_nonneg (fun j _ => (mul_pos (hC j) (hB j)).le),?_⟩
  intro x hx t ht
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hv := powered_nonneg (Γ j) (hn j) (p j) (x-star)
  calc
    ((1-t)^(p j)-1+p j*t)*powered (Γ j) (p j) (x-star) ≤
        (C j*t^2)*powered (Γ j) (p j) (x-star) :=
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hc j t ht)) hv
    _ ≤ (C j*t^2)*B j := mul_le_mul_of_nonneg_left (hb j x hx) (mul_nonneg (hC j).le (sq_nonneg t))
    _ = C j*B j*t^2 := by ring

theorem sqNorm_smul {n : ℕ} (c : ℝ) (v : Vec n) : sqNorm (c • v) = c^2*sqNorm v := by
  simp only [sqNorm,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]

theorem uniform_smooth_inward_remainder {n : ℕ} {ψ : Vec n → ℝ} {U K : Set (Vec n)}
    (hU : IsOpen U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U) (star : Vec n) :
    ∃ D θ : ℝ, 0 ≤ D ∧ 0 < θ ∧ θ ≤ 1/2 ∧ ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ θ →
      RadialCertificate.inwardPoint star x t ∈ U ∧
      |ψ (RadialCertificate.inwardPoint star x t)-ψ x+t*(fderiv ℝ ψ x) (x-star)| ≤ D*t^2 := by
  obtain ⟨M,ρ,hρ,hballs⟩ := CenteredSmoothSublinear.compact_uniform_local_lipschitz hU hK hKU hsmooth.2
  obtain ⟨R,hR,hr⟩ := compact_sqNorm_radius hK star
  let θ := min (1/2) (ρ/(2*R))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hρ (by positivity))
  refine ⟨(M : ℝ)*R^2,θ,by positivity,hθ,min_le_left _ _,?_⟩
  intro x hx t ht htθ
  have hnorm : ‖x-star‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    exact (CenteredSmoothSublinear.pi_norm_sq_le_sqNorm _).trans (hr x hx)
  have htρ : t*R < ρ := by
    have hle := htθ.trans (min_le_right (1/2) (ρ/(2*R)))
    have hm := (le_div_iff₀ (show 0 < 2*R by positivity)).mp hle
    nlinarith
  have hsub : RadialCertificate.inwardPoint star x t-x = (-t) • (x-star) := by
    unfold RadialCertificate.inwardPoint
    module
  have hball : RadialCertificate.inwardPoint star x t ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball,dist_eq_norm,hsub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left hnorm ht).trans_lt htρ
  refine ⟨(hballs x hx).1 hball,?_⟩
  have hdiff : ∀ w ∈ Metric.ball x ρ, DifferentiableAt ℝ ψ w := by
    intro w hw
    exact (hsmooth.1 w ((hballs x hx).1 hw)).differentiableAt (hU.mem_nhds ((hballs x hx).1 hw))
  have hb := CenteredSmoothSublinear.taylor_remainder_le (convex_ball x ρ) hdiff
    (hballs x hx).2 (Metric.mem_ball_self hρ) hball
  rw [hsub,map_smul,smul_eq_mul,sqNorm_smul,neg_sq] at hb
  have he : ψ (RadialCertificate.inwardPoint star x t)-ψ x- -t*(fderiv ℝ ψ x) (x-star) =
      ψ (RadialCertificate.inwardPoint star x t)-ψ x+t*(fderiv ℝ ψ x) (x-star) := by ring
  rw [he] at hb
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left (hr x hx) (mul_nonneg M.coe_nonneg (sq_nonneg t))
  nlinarith

/-- Source R mixed powers satisfy IR directly under the local representation.
The individual gauges need not be coercive, and their full gradients need not
be Lipschitz or even exist at the sampled inward point. -/
theorem mixed_powers_inward {n : ℕ} {ι : Type*} [Fintype ι]
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F) {Γ : ι → Vec n → ℝ}
    (hΓ : ∀ j, ConvexOn ℝ univ (Γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (Γ j))
    (hn : ∀ j x, 0 ≤ Γ j x) (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j)
    (star : Vec n) {U K : Set (Vec n)} (hU : IsOpen U)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+sumObjective Γ p star x) :
    RadialCertificate.HasInwardTaylorBounds F K star := by
  obtain ⟨P,hP,hpow⟩ := uniform_power_remainder hΓ hn hp star hK
  obtain ⟨D,θ,hD,hθ,hθhalf,hsmoothbound⟩ := uniform_smooth_inward_remainder hU hsmooth hK hKU star
  intro η hη
  refine ⟨2*(D+P),θ,hθ,hθhalf,?_⟩
  intro x g hx _ hg t ht htθ
  have hs := hsmoothbound x hx t ht htθ
  refine ⟨RadialCertificate.supportingError_nonneg hF hg _,?_⟩
  have hd : DifferentiableAt ℝ ψ x := (hsmooth.1 x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  rw [inward_error_decomposition hh hn p star hU hrep (hKU hx) hg hd (by linarith) hs.1]
  have hb := hpow x hx t ⟨ht,htθ.trans hθhalf⟩
  have hs' := (le_abs_self _).trans hs.2
  nlinarith

theorem mixed_powers_radial {n : ℕ} {ι : Type*} [Fintype ι]
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F) {Γ : ι → Vec n → ℝ}
    (hΓ : ∀ j, ConvexOn ℝ univ (Γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (Γ j))
    (hn : ∀ j x, 0 ≤ Γ j x) (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j)
    (star : Vec n) {U K : Set (Vec n)} (hU : IsOpen U)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+sumObjective Γ p star x) :
    RadialCertificate.HasRadialSecantBounds F K star :=
  RadialCertificate.radial_of_inward_on_compact hF hK star
    (mixed_powers_inward hF hΓ hh hn p hp star hU hsmooth hK hKU hrep)

theorem composed_gauge_homogeneous {n m : ℕ} {γ : Vec m → ℝ}
    (hh : Homogeneous.PositiveDegreeOne γ) (A : Vec n →ₗ[ℝ] Vec m) :
    Homogeneous.PositiveDegreeOne (γ ∘ A) := by
  intro a ha x
  simp only [Function.comp_def,map_smul,hh a ha]

theorem composed_gauge_convex {n m : ℕ} {γ : Vec m → ℝ}
    (hγ : ConvexOn ℝ univ γ) (A : Vec n →ₗ[ℝ] Vec m) :
    ConvexOn ℝ univ (γ ∘ A) := by
  simpa only [preimage_univ] using hγ.comp_linearMap A

/-- The source's arbitrary linear images, including singular maps and gauges
in different finite-dimensional spaces, retain the derived radial bound. -/
theorem mixed_linear_powers_radial {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (γ : ∀ j, Vec (m j) → ℝ)
    (hγ : ∀ j, ConvexOn ℝ univ (γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (γ j))
    (hn : ∀ j x, 0 ≤ γ j x) (A : ∀ j, Vec n →ₗ[ℝ] Vec (m j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec n) {U K : Set (Vec n)}
    (hU : IsOpen U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j, (γ j (A j (x-star)))^(p j)) :
    RadialCertificate.HasRadialSecantBounds F K star :=
  mixed_powers_radial hF (fun j => composed_gauge_convex (hγ j) (A j))
    (fun j => composed_gauge_homogeneous (hh j) (A j)) (fun j x => hn j (A j x))
    p hp star hU hsmooth hK hKU hrep

end BfgsVerification.RadialPower

namespace BfgsVerification.AdmissibleBFGSRun
open RadialPower

/-- Compact-basin convergence for the actual unmodified full-BFGS run on a
local mixed-power representation. No individual summand coercivity or iterate
convergence is assumed. The distance is the actual Euclidean distance. -/
theorem mixed_powers_convergence {n : ℕ} {ι : Type*} [Fintype ι]
    {F ψ : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {Γ : ι → Vec n → ℝ}
    (hΓ : ∀ j, ConvexOn ℝ univ (Γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (Γ j))
    (hn : ∀ j x, 0 ≤ Γ j x) (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) {U : Set (Vec n)} (hU : IsOpen U)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact R.initialSublevel) (hKU : R.initialSublevel ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+sumObjective Γ p star x) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) := by
  have hrs := mixed_powers_radial R.convex hΓ hh hn p hp star hU hsmooth hK hKU hrep
  have hv := R.radial_certificate_values _ hK R.iterate_mem_initialSublevel star hmin hrs
  exact ⟨hv,euclidean_distance_to_argmin_of_values (convex_continuous R.convex) star hmin hK
    R.iterate_mem_initialSublevel hv,fun hu => R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

theorem mixed_linear_powers_convergence {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (γ : ∀ j, Vec (m j) → ℝ)
    (hγ : ∀ j, ConvexOn ℝ univ (γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (γ j))
    (hn : ∀ j x, 0 ≤ γ j x) (A : ∀ j, Vec n →ₗ[ℝ] Vec (m j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    {U : Set (Vec n)} (hU : IsOpen U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact R.initialSublevel) (hKU : R.initialSublevel ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j, (γ j (A j (x-star)))^(p j)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) :=
  R.mixed_powers_convergence (fun j => composed_gauge_convex (hγ j) (A j))
    (fun j => composed_gauge_homogeneous (hh j) (A j)) (fun j x => hn j (A j x))
    p hp star hmin hU hsmooth hK hKU hrep

end BfgsVerification.AdmissibleBFGSRun

namespace BfgsVerification.RadialPower

/-- At a unique minimizer, a merely local representation supplies a uniform
positive starting basin, derived before selecting any run or SPD matrix. -/
theorem local_mixed_linear_powers_basin {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (γ : ∀ j, Vec (m j) → ℝ)
    (hγ : ∀ j, ConvexOn ℝ univ (γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (γ j))
    (hn : ∀ j x, 0 ≤ γ j x) (A : ∀ j, Vec n →ₗ[ℝ] Vec (m j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hu : ∀ x, F x = F star → x = star) {U : Set (Vec n)} (hU : IsOpen U)
    (hstar : star ∈ U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j, (γ j (A j (x-star)))^(p j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨δ,hδ,hsub⟩ := Localization.neighborhood_basin hF star hmin hu (hU.mem_nhds hstar)
  refine ⟨δ,hδ,?_⟩
  intro R hstart
  have hK := R.initialSublevel_compact_of_unique_minimizer star hmin hu
  have hKU : R.initialSublevel ⊆ U := fun x hx => hsub (hx.trans hstart)
  have hconv := R.mixed_linear_powers_convergence γ hγ hh hn A p hp star hmin hU hsmooth hK hKU hrep
  exact ⟨fun k => hKU (R.iterate_mem_initialSublevel k),hconv.1,hconv.2.2 hu⟩

end BfgsVerification.RadialPower
