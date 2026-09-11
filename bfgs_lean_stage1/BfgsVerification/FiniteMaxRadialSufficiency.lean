import BfgsVerification.FiniteMaxScalarCalculus
import BfgsVerification.QuadraticCellRadial

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter
namespace BfgsVerification.FiniteMaxRadial

/-- A finite C2 family has one common local derivative Lipschitz constant.
All constants are derived from the actual branch regularity. -/
theorem finite_branch_neighborhood {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hs : star ∈ U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U) :
    ∃ M : ℝ≥0, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball star ρ ⊆ U ∧
      ∀ i, LipschitzOnWith M (fderiv ℝ (f i)) (Metric.ball star ρ) := by
  have hsm (i : ι) := ConvexCellRadial.contDiffOn_two_locallyC11 hU (hf i)
  choose M ρ hρ hb using fun i => CenteredSmoothSublinear.compact_uniform_local_lipschitz
    hU (isCompact_singleton : IsCompact ({star} : Set (Vec n))) (by simpa using hs) (hsm i).2
  obtain ⟨r,hr,hri⟩ := CenteredSmoothSublinear.finite_positive_lower_bound Finset.univ ρ
    (fun i _ => hρ i)
  obtain ⟨i₀,hi₀⟩ := hne
  have hsub (i : ι) : Metric.ball star r ⊆ Metric.ball star (ρ i) :=
    Metric.ball_subset_ball (hri i (Finset.mem_univ i))
  refine ⟨∑ i, M i,r,hr,(hsub i₀).trans (hb i₀ star (by simp)).1,?_⟩
  intro i
  have hl := ((hb i star (by simp)).2).mono (hsub i)
  rw [lipschitzOnWith_iff_dist_le_mul] at hl ⊢
  intro x hx z hz
  apply (hl x hx z hz).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  exact_mod_cast (Finset.single_le_sum (f := M) (fun j _ => zero_le _) (Finset.mem_univ i))

theorem inward_curve_hasDerivAt {n : ℕ} (star x : Vec n) (t : ℝ) :
    HasDerivAt (fun u => RadialCertificate.inwardPoint star x u) (-(x-star)) t := by
  simpa only [RadialCertificate.inwardPoint,one_smul,zero_sub] using
    ((hasDerivAt_id t).smul_const (x-star)).const_sub x

theorem inward_curve_mem_ball {n : ℕ} {star x : Vec n} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ Metric.ball star (ρ/4)) {t : ℝ} (ht : t ∈ Ioo (-1/2) (3/4)) :
    RadialCertificate.inwardPoint star x t ∈ Metric.ball star ρ := by
  rw [Metric.mem_ball,dist_eq_norm,RadialPower.inward_radius,norm_smul,Real.norm_eq_abs]
  have hpos : 0 < 1-t := by linarith [ht.2]
  rw [abs_of_pos hpos]
  have hnorm : ‖x-star‖ < ρ/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have htbound : 1-t < 2 := by linarith [ht.1]
  nlinarith [norm_nonneg (x-star)]

theorem radial_branch_derivative_lipschitz {n : ℕ} {f : Vec n → ℝ} {V : Set (Vec n)}
    {M : ℝ≥0} (hM : LipschitzOnWith M (fderiv ℝ f) V) (star x : Vec n)
    {I : Set ℝ} (hI : ∀ t ∈ I, RadialCertificate.inwardPoint star x t ∈ V) :
    LipschitzOnWith (M*‖x-star‖₊*‖x-star‖₊)
      (fun t => (fderiv ℝ f (RadialCertificate.inwardPoint star x t)) (-(x-star))) I := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  have he : RadialCertificate.inwardPoint star x u-RadialCertificate.inwardPoint star x v =
      (v-u) • (x-star) := by
    unfold RadialCertificate.inwardPoint
    module
  have hnorm := hM.norm_sub_le (hI u hu) (hI v hv)
  rw [he,norm_smul] at hnorm
  have hb := (fderiv ℝ f (RadialCertificate.inwardPoint star x u)-
    fderiv ℝ f (RadialCertificate.inwardPoint star x v)).le_opNorm (-(x-star))
  rw [ContinuousLinearMap.sub_apply,norm_neg] at hb
  rw [dist_eq_norm]
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (x-star))
  simp only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm] at hm ⊢
  rw [norm_sub_rev v u] at hm
  nlinarith

/-- The actual finite maximum has a uniform inward remainder on the small
ball when its active branch derivatives agree in the radial direction. -/
theorem finite_max_inward_error {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    {star : Vec n} {ρ : ℝ} (hρ : 0 < ρ) (hBU : Metric.ball star ρ ⊆ U)
    {M : ℝ≥0} (hM : ∀ i, LipschitzOnWith M (fderiv ℝ (f i)) (Metric.ball star ρ))
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne (fun i => f i w))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w-star) = (fderiv ℝ (f j) w) (w-star))
    {x g : Vec n} (hx : x ∈ Metric.ball star (ρ/4))
    (hg : HasFDerivAt F (gradientFunctional g) x) {t : ℝ} (ht : t ∈ Icc 0 (1/2)) :
    0 ≤ RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint star x t) ∧
      RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint star x t) ≤
        (M : ℝ)*ρ^2*t^2 := by
  let I := Ioo (-1/2 : ℝ) (3/4)
  let q : ι → ℝ → ℝ := fun i u => f i (RadialCertificate.inwardPoint star x u)
  let d : ι → ℝ → ℝ := fun i u => (fderiv ℝ (f i) (RadialCertificate.inwardPoint star x u)) (-(x-star))
  let Q := maximum Finset.univ hne q
  let Φ := fun u => F (RadialCertificate.inwardPoint star x u)
  have hIB (u : ℝ) (hu : u ∈ I) := inward_curve_mem_ball hρ hx hu
  have hIU (u : ℝ) (hu : u ∈ I) := hBU (hIB u hu)
  have hd : ∀ i ∈ (Finset.univ : Finset ι), ∀ u ∈ I, HasDerivAt (q i) (d i u) u := by
    intro i hi u hu
    exact (((hf i).differentiableOn (by norm_num) _ (hIU u hu)).differentiableAt
      (hU.mem_nhds (hIU u hu))).hasFDerivAt.comp_hasDerivAt u (inward_curve_hasDerivAt star x u)
  have hqrep (u : ℝ) (hu : u ∈ I) : Φ u = Q u := hrep _ (hIU u hu)
  have ha : ∀ u ∈ I, ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ Finset.univ,
      q i u = Q u → q j u = Q u → d i u = d j u := by
    intro u hu i hi j hj hai haj
    have hic : f i (RadialCertificate.inwardPoint star x u) = F (RadialCertificate.inwardPoint star x u) :=
      hai.trans (hqrep u hu).symm
    have hjc : f j (RadialCertificate.inwardPoint star x u) = F (RadialCertificate.inwardPoint star x u) :=
      haj.trans (hqrep u hu).symm
    have he := hcompat _ (hIU u hu) i j hic hjc
    rw [RadialPower.inward_radius,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at he
    have hne' : 1-u ≠ 0 := by have := hu.2; linarith
    have hv := (mul_left_cancel₀ hne' he)
    dsimp only [d]
    rw [map_neg,map_neg,hv]
  have hLip : ∀ i ∈ (Finset.univ : Finset ι),
      LipschitzOnWith (M*‖x-star‖₊*‖x-star‖₊) (d i) I := by
    intro i hi
    exact radial_branch_derivative_lipschitz (hM i) star x hIB
  have hLQ := maximum_deriv_lipschitzOn hne isOpen_Ioo (convex_Ioo _ _) hd ha hLip
  have hΦderiv (u : ℝ) (hu : u ∈ I) : HasDerivAt Φ (deriv Q u) u := by
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' hne (fun i => q i u)
    have hQ := maximum_hasDerivAt_of_active_agreement hne (fun j hj => hd j hj u hu)
      (fun j hj hja => ha u hu j hj i hi hja he.symm)
    have hQ' : HasDerivAt Q (deriv Q u) u := hQ.differentiableAt.hasDerivAt
    apply hQ'.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact hqrep v hv
  have hzero : (0 : ℝ) ∈ I := by constructor <;> norm_num
  have htI : t ∈ I := by constructor <;> linarith [ht.1,ht.2]
  have hΦ0 := hg.comp_hasDerivAt_of_eq 0 (inward_curve_hasDerivAt star x 0)
    (by simp [RadialCertificate.inwardPoint])
  have hD0 : deriv Q 0 = -dot g (x-star) := by
    have he := (hΦderiv 0 hzero).unique hΦ0
    simpa only [gradientFunctional_apply,map_neg] using he
  have hΦconv : ConvexOn ℝ univ Φ := by
    have he : Φ = F ∘ AffineMap.lineMap (k := ℝ) x star := by
      funext u
      change F (RadialCertificate.inwardPoint star x u) = F ((AffineMap.lineMap (k := ℝ) x star) u)
      congr 1
      change x-u • (x-star) = u • (star-x)+x
      module
    rw [he]
    simpa only [preimage_univ] using hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x star)
  refine ⟨RadialCertificate.supportingError_nonneg hF hg _,?_⟩
  by_cases ht0 : t = 0
  · subst t
    simp [RadialCertificate.inwardPoint,RadialCertificate.supportingError,dot]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hs := hΦconv.slope_le_of_hasDerivAt (mem_univ 0) (mem_univ t) htpos (hΦderiv t htI)
  rw [slope_def_field,sub_zero] at hs
  have hs' := (div_le_iff₀ htpos).mp hs
  have hdiff := hLQ.norm_sub_le htI hzero
  simp only [NNReal.coe_mul,coe_nnnorm,sub_zero,Real.norm_eq_abs,abs_of_pos htpos] at hdiff
  have hdle := (le_abs_self _).trans hdiff
  rw [hD0] at hdle
  have hrad : ‖x-star‖ ≤ ρ := by
    have hx' : ‖x-star‖ < ρ/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    linarith
  have hsq : ‖x-star‖^2 ≤ ρ^2 := (sq_le_sq₀ (norm_nonneg _) hρ.le).mpr hrad
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq M.coe_nonneg) (sq_nonneg t)
  have hdd := mul_le_mul_of_nonneg_left hdle ht.1
  rw [RadialCertificate.inward_error_eq]
  have hphi0 : Φ 0 = F x := by simp [Φ,RadialCertificate.inwardPoint]
  rw [hphi0] at hs'
  dsimp only [Φ] at hs'
  nlinarith

/-- Source R's finite smooth-branch radial-agreement test gives IR on a fixed
neighborhood. Uniform constants are derived from the actual C2 branches. -/
theorem local_finite_max_inward {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne (fun i => f i w))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w-star) = (fderiv ℝ (f j) w) (w-star)) :
    ∃ r : ℝ, 0 < r ∧ ∀ K : Set (Vec n), K ⊆ Metric.ball star r →
      RadialCertificate.HasInwardTaylorBounds F K star := by
  obtain ⟨M,ρ,hρ,hBU,hM⟩ := finite_branch_neighborhood hne f hU hs hf
  refine ⟨ρ/4,by positivity,?_⟩
  intro K hK η hη
  refine ⟨2*(M : ℝ)*ρ^2,1/2,by norm_num,le_rfl,?_⟩
  intro x g hx hxgap hg t ht htθ
  have he := finite_max_inward_error hne hF f hU hf hρ hBU hM hrep hcompat (hK hx) hg ⟨ht,htθ⟩
  refine ⟨he.1,?_⟩
  nlinarith [he.2]

theorem local_finite_max_radial {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne (fun i => f i w))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w-star) = (fderiv ℝ (f j) w) (w-star)) :
    ∃ r : ℝ, 0 < r ∧ ∀ K : Set (Vec n), IsCompact K → K ⊆ Metric.ball star r →
      RadialCertificate.HasRadialSecantBounds F K star := by
  obtain ⟨r,hr,hIR⟩ := local_finite_max_inward hne hF f hU hf hs hrep hcompat
  exact ⟨r,hr,fun K hK hKB => RadialCertificate.radial_of_inward_on_compact hF hK star (hIR K hKB)⟩

/-- Every sufficiently low-starting actual full-BFGS run converges under the
finite C2 maximum branch test; no branch-identification or switching-count
condition is imposed on the run or on the radial intervals. -/
theorem local_finite_max_basin {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne (fun i => f i w))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w-star) = (fderiv ℝ (f j) w) (w-star))
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨r,hr,hRS⟩ := local_finite_max_radial hne hF f hU hf hs hrep hcompat
  obtain ⟨δ,hδ,hsub⟩ := Localization.neighborhood_basin hF star hmin hu
    (inter_mem (Metric.ball_mem_nhds star hr) (hU.mem_nhds hs))
  refine ⟨δ,hδ,?_⟩
  intro R hstart
  have hK := R.initialSublevel_compact_of_unique_minimizer star hmin hu
  have hKB : R.initialSublevel ⊆ Metric.ball star r := fun x hx => (hsub (hx.trans hstart)).1
  have hKU : R.initialSublevel ⊆ U := fun x hx => (hsub (hx.trans hstart)).2
  have hv := R.radial_certificate_values _ hK R.iterate_mem_initialSublevel star hmin (hRS _ hK hKB)
  exact ⟨fun k => hKU (R.iterate_mem_initialSublevel k),hv,
    R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

end BfgsVerification.FiniteMaxRadial

namespace BfgsVerification.FiniteMaxRadial

/-- The compact-basin source version also permits nonunique minimizers and
concludes Euclidean distance to the entire minimizer set. -/
theorem finite_max_compact_basin {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne (fun i => f i w))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w-star) = (fderiv ℝ (f j) w) (w-star))
    (hmin : ∀ x, F star ≤ F x) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : AdmissibleBFGSRun n F, IsCompact R.initialSublevel →
      R.initialSublevel ⊆ Metric.ball star r →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
        Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
        ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) := by
  obtain ⟨r,hr,hRS⟩ := local_finite_max_radial hne hF f hU hf hs hrep hcompat
  refine ⟨r,hr,?_⟩
  intro R hK hKB
  have hv := R.radial_certificate_values _ hK R.iterate_mem_initialSublevel star hmin (hRS _ hK hKB)
  exact ⟨hv,euclidean_distance_to_argmin_of_values (convex_continuous hF) star hmin hK
    R.iterate_mem_initialSublevel hv,fun hu => R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

end BfgsVerification.FiniteMaxRadial
