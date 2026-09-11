import BfgsVerification.RadialReverse

/-! Module R's derivative-free central difference, on nested positive bands.
Outward samples must remain in the structural sublevel; local converses shrink
that upper level explicitly. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix MeasureTheory

namespace BfgsVerification
namespace RadialCertificate

def outwardPoint {n : ℕ} (star x : Vec n) (t : ℝ) : Vec n := inwardPoint star x (-t)

def centralDifference {n : ℕ} (F : Vec n → ℝ) (star x : Vec n) (t : ℝ) : ℝ :=
  F (outwardPoint star x t) + F (inwardPoint star x t) - 2 * F x

theorem outwardPoint_eq_homothety {n : ℕ} (star x : Vec n) (t : ℝ) :
    outwardPoint star x t = AffineMap.homothety star (1 + t) x := by
  simp only [outwardPoint, inwardPoint_eq_homothety, sub_neg_eq_add]

theorem continuous_outwardPoint {n : ℕ} (star : Vec n) (t : ℝ) :
    Continuous (fun x : Vec n => outwardPoint star x t) := continuous_inwardPoint star (-t)

theorem centralDifference_eq_errors {n : ℕ} (F : Vec n → ℝ)
    (star x g : Vec n) (t : ℝ) :
    centralDifference F star x t = supportingError F x g (outwardPoint star x t) +
      supportingError F x g (inwardPoint star x t) := by
  simp only [centralDifference, outwardPoint, inward_error_eq]
  ring

theorem inwardPoint_outwardPoint {n : ℕ} (star x : Vec n) {t : ℝ} (ht : 0 ≤ t) :
    inwardPoint star (outwardPoint star x t) (t / (1 + t)) = x := by
  rw [inwardPoint_eq_homothety, outwardPoint_eq_homothety,
    ← AffineMap.homothety_mul_apply]
  have hp : 1 + t ≠ 0 := by linarith
  have he : (1 - t / (1 + t)) * (1 + t) = 1 := by field_simp
  rw [he, AffineMap.homothety_one]
  rfl

theorem outward_value_ge {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (x : Vec n) {t : ℝ} (ht : 0 ≤ t) :
    F x ≤ F (outwardPoint star x t) := by
  have hp : 0 < 1 + t := by linarith
  have h := inward_value_le hF star hmin (outwardPoint star x t)
    (div_nonneg ht hp.le) ((div_le_one hp).mpr (by linarith : t ≤ 1 + t))
  rwa [inwardPoint_outwardPoint star x ht] at h

theorem outward_secant_identities {n : ℕ} (star x g h : Vec n) (t : ℝ) :
    secantCurvature (outwardPoint star x t) x h g = t * dot (h - g) (x - star) ∧
    radialNumerator star x h g = -dot (h - g) (x - star) := by
  have hs : x - outwardPoint star x t = -t • (x - star) := by
    unfold outwardPoint inwardPoint
    module
  unfold secantCurvature radialNumerator
  rw [hs, dot_smul_right, dot_sub_left, dot_sub_left]
  constructor <;> ring

/-- RS on the outer/middle pair bounds the outward supporting remainder by Ct². -/
theorem outward_error_le_of_pair_radial {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star x g h : Vec n) (t C : ℝ)
    (ht : 0 ≤ t) (hC : 0 ≤ C) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) (outwardPoint star x t))
    (hRS : 0 < secantCurvature (outwardPoint star x t) x h g →
      (radialNumerator star x h g) ^ 2 ≤ C * secantCurvature (outwardPoint star x t) x h g) :
    supportingError F x g (outwardPoint star x t) ≤ C * t ^ 2 := by
  by_cases htzero : t = 0
  · subst t
    simp [outwardPoint, inwardPoint, supportingError, dot]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
  have hid := outward_secant_identities star x g h t
  have hD := supportingError_nonneg hF hg (outwardPoint star x t)
  have hDT : supportingError F x g (outwardPoint star x t) ≤
      secantCurvature (outwardPoint star x t) x h g := by
    rw [secantCurvature_eq_errors F]
    exact le_add_of_nonneg_left (supportingError_nonneg hF hh x)
  rw [hid.1] at hDT
  have ha : 0 ≤ dot (h - g) (x - star) := by nlinarith
  by_cases hazero : dot (h - g) (x - star) = 0
  · rw [hazero, mul_zero] at hDT
    exact hDT.trans (by positivity)
  have hapos : 0 < dot (h - g) (x - star) := lt_of_le_of_ne ha (Ne.symm hazero)
  have hb := hRS (by rw [hid.1]; exact mul_pos htpos hapos)
  rw [hid.1, hid.2] at hb
  have hab : dot (h - g) (x - star) ≤ C * t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hab ht]

/-- Exact source 5C bound on differentiable outer/middle/inner triples. -/
theorem central_difference_le_five_of_pair_radial {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star x go gm gi : Vec n) (t C : ℝ)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hC : 0 ≤ C)
    (ho : HasFDerivAt F (gradientFunctional go) (outwardPoint star x t))
    (hm : HasFDerivAt F (gradientFunctional gm) x)
    (hi : HasFDerivAt F (gradientFunctional gi) (inwardPoint star x t))
    (hRSo : 0 < secantCurvature (outwardPoint star x t) x go gm →
      (radialNumerator star x go gm) ^ 2 ≤ C * secantCurvature (outwardPoint star x t) x go gm)
    (hRSi : 0 < secantCurvature x (inwardPoint star x t) gm gi →
      (radialNumerator star (inwardPoint star x t) gm gi) ^ 2 ≤
        C * secantCurvature x (inwardPoint star x t) gm gi) :
    centralDifference F star x t ≤ 5 * C * t ^ 2 := by
  rw [centralDifference_eq_errors F star x gm t]
  have hoB := outward_error_le_of_pair_radial hF star x gm go t C ht0 hC hm ho hRSo
  have hiB := inward_error_le_of_pair_radial hF star x gm gi t C ht0 ht hC hm hi hRSi
  linarith

/-- A central difference bounds each nonnegative remainder at a differentiable
middle point. No derivative is needed at either dilated endpoint. -/
theorem inward_error_le_central {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star x g : Vec n) (t : ℝ)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    supportingError F x g (inwardPoint star x t) ≤ centralDifference F star x t := by
  rw [centralDifference_eq_errors F star x g t]
  exact le_add_of_nonneg_left (supportingError_nonneg hF hg _)

/-- The function-value bound only asserts coverage when the outer point stays
inside the upper sublevel and the inner point stays on the positive band. -/
def HasNestedCentralBounds {n : ℕ} (F : Vec n → ℝ) (star : Vec n) (b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x : Vec n, ∀ t : ℝ, 0 ≤ t → t ≤ θ →
      F (outwardPoint star x t) ≤ b → F star + η ≤ F (inwardPoint star x t) →
      centralDifference F star x t ≤ C * t ^ 2

/-- Three full-measure differentiability conditions give actual joint density. -/
theorem dense_radial_differentiable_triples {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Dense {x : Vec n | DifferentiableAt ℝ F (outwardPoint star x t) ∧
      DifferentiableAt ℝ F x ∧ DifferentiableAt ℝ F (inwardPoint star x t)} := by
  have ho : ConvexOn ℝ univ (F ∘ AffineMap.homothety star (1 + t)) := by
    simpa only [preimage_univ] using hF.comp_affineMap (AffineMap.homothety star (1 + t))
  have hi : ConvexOn ℝ univ (F ∘ AffineMap.homothety star (1 - t)) := by
    simpa only [preimage_univ] using hF.comp_affineMap (AffineMap.homothety star (1 - t))
  apply MeasureTheory.Measure.dense_of_ae (μ := volume)
  filter_upwards [convex_ae_differentiable ho, convex_ae_differentiable hF,
    convex_ae_differentiable hi] with x hox hx hix
  refine ⟨?_, hx, ?_⟩
  · rw [outwardPoint_eq_homothety]
    exact differentiableAt_of_comp_homothety star (by linarith : 1 + t ≠ 0) x hox
  · rw [inwardPoint_eq_homothety]
    exact differentiableAt_of_comp_homothety star (sub_pos.mpr ht1).ne' x hix

/-- A generic dense-set approximation in the interior of a positive sublevel. -/
theorem exists_dense_sublevel_approximation {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (b : ℝ) (hb : F star < b)
    (x : Vec n) (hx : F x ≤ b) {O D : Set (Vec n)} (hO : IsOpen O) (hxO : x ∈ O)
    (hD : Dense D) : ∃ u : ℕ → Vec n, Tendsto u atTop (𝓝 x) ∧
      ∀ j, F (u j) ≤ b ∧ u j ∈ O ∧ u j ∈ D := by
  let K := {w : Vec n | F w ≤ b}
  have hc := convex_continuous hF
  have hKclosed : IsClosed K := isClosed_le hc continuous_const
  have hKconvex : Convex ℝ K := by simpa only [mem_univ, true_and] using hF.convex_le b
  have hstar : star ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    have hopen : IsOpen {w : Vec n | F w < b} := isOpen_lt hc continuous_const
    have hmem : {w : Vec n | F w < b} ∈ 𝓝 star := hopen.mem_nhds hb
    exact Filter.mem_of_superset hmem (fun w (hw : F w < b) => show w ∈ K from hw.le)
  have hxclosure : x ∈ closure (interior K) := by
    rw [hKconvex.closure_interior_eq_closure_of_nonempty_interior ⟨star, hstar⟩, hKclosed.closure_eq]
    exact hx
  have hxOS : x ∈ closure (interior K ∩ O) := hO.closure_inter ⟨hxclosure, hxO⟩
  have hxgood : x ∈ closure ((interior K ∩ O) ∩ D) := by
    simpa only [closure_closure] using
      closure_mono (hD.open_subset_closure_inter (isOpen_interior.inter hO)) hxOS
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hxgood
  exact ⟨u, hux, fun j => ⟨interior_subset (s := K) (hu j).1.1, (hu j).1.2, (hu j).2⟩⟩


set_option maxHeartbeats 800000 in
/-- RS yields the derivative-free central bound. Approximation retains the
original upper sublevel even when the outward sample is on its boundary. -/
theorem central_of_radial_on_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b : ℝ) (hb : F star < b) (hRS : HasRadialSecantBounds F {x | F x ≤ b} star) :
    HasNestedCentralBounds F star b := by
  have hc := convex_continuous hF
  intro η hη
  obtain ⟨C, hC⟩ := hRS (η / 2) (by positivity)
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  refine ⟨5 * C', 1 / 2, by norm_num, le_rfl, ?_⟩
  intro x t ht0 hthalf hxout hxband
  let O := {w : Vec n | F star + η / 2 < F (inwardPoint star w t)}
  let D := {w : Vec n | DifferentiableAt ℝ F (outwardPoint star w t) ∧
    DifferentiableAt ℝ F w ∧ DifferentiableAt ℝ F (inwardPoint star w t)}
  let Fo := fun w : Vec n => F (outwardPoint star w t)
  have hFo : ConvexOn ℝ univ Fo := by
    simpa only [Fo, Function.comp_def, outwardPoint_eq_homothety, preimage_univ] using
      hF.comp_affineMap (AffineMap.homothety star (1 + t))
  have hFostar : Fo star < b := by simpa [Fo, outwardPoint, inwardPoint] using hb
  have hO : IsOpen O := isOpen_lt continuous_const (hc.comp (continuous_inwardPoint star t))
  have hxO : x ∈ O := by dsimp only [O, mem_setOf_eq]; linarith
  have hD : Dense D := dense_radial_differentiable_triples hF star ht0 (by linarith)
  obtain ⟨u, hux, hu⟩ := exists_dense_sublevel_approximation hFo star b hFostar x hxout hO hxO hD
  have hbound (j : ℕ) : centralDifference F star (u j) t ≤ 5 * C' * t ^ 2 := by
    let go := coordinateGradient F (outwardPoint star (u j) t)
    let gm := coordinateGradient F (u j)
    let gi := coordinateGradient F (inwardPoint star (u j) t)
    have ho : HasFDerivAt F (gradientFunctional go) (outwardPoint star (u j) t) :=
      hasFDerivAt_coordinateGradient (hu j).2.2.1
    have hm : HasFDerivAt F (gradientFunctional gm) (u j) :=
      hasFDerivAt_coordinateGradient (hu j).2.2.2.1
    have hi : HasFDerivAt F (gradientFunctional gi) (inwardPoint star (u j) t) :=
      hasFDerivAt_coordinateGradient (hu j).2.2.2.2
    have hout := outward_value_ge hF star hmin (u j) ht0
    have hin := inward_value_le hF star hmin (u j) ht0 (by linarith : t ≤ 1)
    have hko : F (outwardPoint star (u j) t) ≤ b := (hu j).1
    have hkm : F (u j) ≤ b := hout.trans hko
    have hki : F (inwardPoint star (u j) t) ≤ b := hin.trans hkm
    have hbi : F star + η / 2 ≤ F (inwardPoint star (u j) t) := (hu j).2.1.le
    apply central_difference_le_five_of_pair_radial hF star (u j) go gm gi t C'
      ht0 hthalf hC' ho hm hi
    · intro ht
      exact (hC _ _ go gm hko hkm (hbi.trans hin) hout ho hm ht).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) ht.le)
    · intro ht
      exact (hC _ _ gm gi hkm hki hbi hin hm hi ht).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) ht.le)
  have hcont : Continuous (fun w : Vec n => centralDifference F star w t) := by
    unfold centralDifference
    exact ((hc.comp (continuous_outwardPoint star t)).add
      (hc.comp (continuous_inwardPoint star t))).sub (continuous_const.mul hc)
  exact le_of_tendsto_of_tendsto' ((hcont.tendsto x).comp hux) tendsto_const_nhds hbound

/-- Convexity bounds an outward sample by interpolation with the doubled radius. -/
theorem outward_value_interpolation {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star x : Vec n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    F (outwardPoint star x t) ≤ (1 - t) * F x + t * F (outwardPoint star x 1) := by
  have hc := hF.2 (show x ∈ univ by trivial) (show outwardPoint star x 1 ∈ univ by trivial)
    (sub_nonneg.mpr ht1) ht0 (show (1 - t) + t = 1 by ring)
  have he : (1 - t) • x + t • outwardPoint star x 1 = outwardPoint star x t := by
    unfold outwardPoint inwardPoint
    module
  simpa only [he, smul_eq_mul] using hc

set_option maxHeartbeats 800000 in
/-- The converse is local in the upper level: every strictly smaller compact
sublevel has IR. No claim is made for outward probes beyond the top boundary. -/
theorem inward_of_central_on_smaller_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b b' : ℝ) (hbb : b' < b) (hK : IsCompact {x : Vec n | F x ≤ b})
    (hcentral : HasNestedCentralBounds F star b) :
    HasInwardTaylorBounds F {x | F x ≤ b'} star := by
  have hc := convex_continuous hF
  have hK' : IsCompact {x : Vec n | F x ≤ b'} := hK.of_isClosed_subset
    (isClosed_le hc continuous_const) (fun x hx => hx.trans hbb.le)
  obtain ⟨G, hG, hgBound⟩ := convex_gradient_bound_on_compact hF hK'
  obtain ⟨R, hR, hrBound⟩ := compact_sqNorm_radius hK' star
  obtain ⟨B, hB⟩ := hK'.bddAbove_image (hc.comp (continuous_outwardPoint star 1)).continuousOn
  let D := max (B - F star) 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  intro η hη
  obtain ⟨C, θ₀, hθ₀, hθ₀half, hC⟩ := hcentral (η / 2) (by positivity)
  let C' := max C 0
  let θ := min θ₀ (min (η / (4 * G * R)) ((b - b') / D))
  have hθ : 0 < θ := lt_min hθ₀ (lt_min (div_pos hη (by positivity)) (div_pos (sub_pos.mpr hbb) hD))
  have hθhalf : θ ≤ 1 / 2 := (min_le_left _ _).trans hθ₀half
  refine ⟨2 * C', θ, hθ, hθhalf, ?_⟩
  intro x g hx hxband hg t ht0 htθ
  refine ⟨supportingError_nonneg hF hg _, ?_⟩
  have htθ₀ : t ≤ θ₀ := htθ.trans (min_le_left _ _)
  have htr : t ≤ η / (4 * G * R) := htθ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htd : t ≤ (b - b') / D := htθ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hthalf : t ≤ 1 / 2 := htθ.trans hθhalf
  have hmargin := inward_positive_band_margin hF star x g hg G R η hG hR
    (hgBound x hx g hg) (hrBound x hx) hxband ht0 htr
  have hout : F (outwardPoint star x t) ≤ b := by
    have hcOut := outward_value_interpolation hF star x ht0 (by linarith : t ≤ 1)
    have hBx : F (outwardPoint star x 1) ≤ B := hB ⟨x, hx, rfl⟩
    have hBD : B - F star ≤ D := le_max_left _ _
    have htD := (le_div_iff₀ hD).mp htd
    have hdrop : F (outwardPoint star x 1) - F x ≤ D := by linarith [hmin x]
    have hmul := mul_le_mul_of_nonneg_left hdrop ht0
    change F x ≤ b' at hx
    nlinarith
  have hinner : F star + η / 2 ≤ F (inwardPoint star x t) := by linarith
  have hbound := hC x t ht0 htθ₀ hout hinner
  calc
    supportingError F x g (inwardPoint star x t) ≤ centralDifference F star x t :=
      inward_error_le_central hF star x g t hg
    _ ≤ C * t ^ 2 := hbound
    _ ≤ C' * t ^ 2 := mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg t)
    _ = (2 * C') / 2 * t ^ 2 := by ring

/-- Nested central bounds give RS on every strictly smaller compact sublevel. -/
theorem radial_of_central_on_smaller_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b b' : ℝ) (hbb : b' < b) (hK : IsCompact {x : Vec n | F x ≤ b})
    (hcentral : HasNestedCentralBounds F star b) :
    HasRadialSecantBounds F {x | F x ≤ b'} star := by
  have hK' : IsCompact {x : Vec n | F x ≤ b'} := hK.of_isClosed_subset
    (isClosed_le (convex_continuous hF) continuous_const) (fun x hx => hx.trans hbb.le)
  exact radial_of_inward_on_compact hF hK' star
    (inward_of_central_on_smaller_sublevel hF star hmin b b' hbb hK hcentral)

/-- Precise local equivalence: a positive compact structural sublevel exists
for RS exactly when one exists for the derivative-free nested central condition. -/
theorem local_radial_iff_nested_central {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x) :
    (∃ b : ℝ, F star < b ∧ IsCompact {x : Vec n | F x ≤ b} ∧
      HasRadialSecantBounds F {x | F x ≤ b} star) ↔
    (∃ b : ℝ, F star < b ∧ IsCompact {x : Vec n | F x ≤ b} ∧
      HasNestedCentralBounds F star b) := by
  constructor
  · rintro ⟨b, hb, hK, hRS⟩
    exact ⟨b, hb, hK, central_of_radial_on_sublevel hF star hmin b hb hRS⟩
  · rintro ⟨b, hb, hK, hC⟩
    let b' := (F star + b) / 2
    have hb' : F star < b' := by dsimp only [b']; linarith
    have hbb : b' < b := by dsimp only [b']; linarith
    have hK' : IsCompact {x : Vec n | F x ≤ b'} := hK.of_isClosed_subset
      (isClosed_le (convex_continuous hF) continuous_const) (fun x hx => hx.trans hbb.le)
    exact ⟨b', hb', hK', radial_of_central_on_smaller_sublevel hF star hmin b b' hbb hK hC⟩

end RadialCertificate
end BfgsVerification
