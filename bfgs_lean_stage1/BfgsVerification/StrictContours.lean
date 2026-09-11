import BfgsVerification.Localization

/-!
# Module M: strict contours force vanishing accepted steps

The contour condition is literally the absence of a nontrivial segment in the
frontier of the limiting sublevel. A point with smaller objective value ensures
that the limiting level is on this frontier. The proof uses compact endpoint
pairs and convex-combination value bounds; it does not assume convergent
gradients, iterates, or matrices.
-/

noncomputable section
open scoped Topology
open Set Metric Filter

namespace BfgsVerification.StrictContours

/-- Above an attained lower value, a level point of a continuous convex
function lies on the frontier of its sublevel. -/
theorem level_mem_frontier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F) (hcont : Continuous F)
    {ℓ : ℝ} (hlower : ∃ y, F y < ℓ) {x : E} (hx : F x = ℓ) :
    x ∈ frontier {z | F z ≤ ℓ} := by
  rw [(isClosed_le hcont continuous_const).frontier_eq]
  refine ⟨hx.le, ?_⟩
  intro hinterior
  obtain ⟨y, hy⟩ := hlower
  let p : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y x
  have hpone : p 1 = x := by simp [p]
  have hpcont : Continuous p := AffineMap.lineMap_continuous
  have hnear : ∀ᶠ t in 𝓝 (1 : ℝ), F (p t) ≤ ℓ := by
    have ht : Tendsto p (𝓝 1) (𝓝 x) := by simpa [hpone] using hpcont.tendsto 1
    exact ht.eventually (mem_interior_iff_mem_nhds.mp hinterior)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let t := 1 + ε / 2
  have ht : (1 : ℝ) < t := by dsimp [t]; linarith
  have htmem : t ∈ Metric.ball (1 : ℝ) ε := by
    change |t - 1| < ε
    dsimp [t]
    rw [add_sub_cancel_left, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have hpt : F (p t) ≤ ℓ := hball htmem
  have hc : ConvexOn ℝ Set.univ (F ∘ p) := by
    simpa using hF.comp_affineMap p
  have hs := hc.slope_mono_adjacent (show (0 : ℝ) ∈ Set.univ by trivial)
    (show t ∈ Set.univ by trivial) (show (0 : ℝ) < 1 by norm_num) ht
  have hnonpos : (F (p t) - F (p 1)) / (t - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by simpa [hpone, hx] using sub_nonpos.mpr hpt)
      (sub_nonneg.mpr ht.le)
  have hpos : 0 < ((F ∘ p) 1 - (F ∘ p) 0) / ((1 : ℝ) - 0) := by
    simpa [Function.comp_def, p, hx] using sub_pos.mpr hy
  have := hs.trans hnonpos
  linarith

end BfgsVerification.StrictContours

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The current supporting gradient controls objective values throughout its
accepted segment by the actual predicted decrease. -/
theorem segment_value_lower (k : ℕ) (a b : ℝ) (hab : a + b = 1) :
    F (R.x k) - b * R.d k ≤ F (a • R.x k + b • R.x (k + 1)) := by
  have h := convex_supporting_inequality R.convex (R.hasGradient k)
    (a • R.x k + b • R.x (k + 1))
  have heq : a • R.x k + b • R.x (k + 1) - R.x k =
      b • bfgsStep (R.H k) (R.g k) (R.α k) := by
    rw [R.step, smul_add]
    have ha : a = 1 - b := by linarith
    rw [ha, sub_smul, one_smul]
    abel
  rw [heq, dot_smul_right, R.dot_step_eq_neg_d] at h
  linarith

/-- Every segment joining a simultaneous cluster pair of successive accepted
iterates is constant at the limiting objective value. -/
theorem cluster_pair_segment_constant (ℓ : ℝ)
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {x z : Vec n}
    (hx : Tendsto (fun k => R.x (φ k)) atTop (𝓝 x))
    (hz : Tendsto (fun k => R.x (φ k + 1)) atTop (𝓝 z)) :
    ∀ w ∈ segment ℝ x z, F w = ℓ := by
  have hcont := convex_continuous R.convex
  have hxvalue : F x = ℓ :=
    tendsto_nhds_unique ((hcont.tendsto x).comp hx) (hlim.comp hφ.tendsto_atTop)
  have hzvalue : F z = ℓ :=
    tendsto_nhds_unique ((hcont.tendsto z).comp hz)
      (hlim.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop))
  have hd : Tendsto R.d atTop (𝓝 0) :=
    (R.summable_predicted_decreases_of_value_limit ℓ hlim).tendsto_atTop_zero
  intro w hw
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  have hpoint := (hx.const_smul a).add (hz.const_smul b)
  have hvalue := (hcont.tendsto (a • x + b • z)).comp hpoint
  have hlower : Tendsto (fun k => F (R.x (φ k)) - b * R.d (φ k)) atTop (𝓝 ℓ) := by
    simpa using (hlim.comp hφ.tendsto_atTop).sub
      (tendsto_const_nhds.mul (hd.comp hφ.tendsto_atTop))
  apply le_antisymm
  · have hc := R.convex.2 (show x ∈ Set.univ by trivial) (show z ∈ Set.univ by trivial)
      ha hb hab
    simpa [hxvalue, hzvalue, smul_eq_mul, ← add_mul, hab] using hc
  · exact le_of_tendsto_of_tendsto' hlower hvalue
      (fun k => R.segment_value_lower (φ k) a b hab)

/-- Module M's strict-contour conclusion for actual accepted iterates. The
contour hypothesis literally rules out every nontrivial closed segment in the
frontier of the limiting sublevel. A lower objective value is the precise
positive-level condition; no existence of a minimizer is needed. -/
theorem differences_tendsto_zero_of_strict_contour
    (hK : IsCompact R.initialSublevel) (ℓ : ℝ)
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ))
    (hlower : ∃ y, F y < ℓ)
    (hcontour : ∀ x z : Vec n,
      segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z) :
    Tendsto (fun k => R.x (k + 1) - R.x k) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push_neg at hn
  let S : Set (Vec n × Vec n) := (R.initialSublevel ×ˢ R.initialSublevel) ∩
    {p | ε ≤ dist p.2 p.1}
  have hS : IsCompact S :=
    (hK.prod hK).inter_right (isClosed_le continuous_const (continuous_snd.dist continuous_fst))
  have hfreq : ∃ᶠ k in atTop, (R.x k, R.x (k + 1)) ∈ S := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk, hdist⟩ := hn N
    refine ⟨k, hk, ⟨⟨R.iterate_mem_initialSublevel k,
      R.iterate_mem_initialSublevel (k + 1)⟩, ?_⟩⟩
    change ε ≤ dist (R.x (k + 1)) (R.x k)
    simpa only [dist_eq_norm, sub_zero] using hdist
  obtain ⟨p, hp, φ, hφ, hpconv⟩ := hS.tendsto_subseq' hfreq
  have hx : Tendsto (fun k => R.x (φ k)) atTop (𝓝 p.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto p).comp hpconv
  have hz : Tendsto (fun k => R.x (φ k + 1)) atTop (𝓝 p.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto p).comp hpconv
  have hsegment : segment ℝ p.1 p.2 ⊆ frontier {w | F w ≤ ℓ} := by
    intro w hw
    exact StrictContours.level_mem_frontier R.convex (convex_continuous R.convex) hlower
      (R.cluster_pair_segment_constant ℓ hlim hφ hx hz w hw)
  have heq := hcontour p.1 p.2 hsegment
  have hdist : ε ≤ dist p.2 p.1 := hp.2
  rw [heq, dist_self] at hdist
  linarith

/-- The same conclusion stated for the actual unmodified BFGS accepted steps. -/
theorem steps_tendsto_zero_of_strict_contour
    (hK : IsCompact R.initialSublevel) (ℓ : ℝ)
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ))
    (hlower : ∃ y, F y < ℓ)
    (hcontour : ∀ x z : Vec n,
      segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z) :
    Tendsto (fun k => bfgsStep (R.H k) (R.g k) (R.α k)) atTop (𝓝 0) := by
  have heq : (fun k => bfgsStep (R.H k) (R.g k) (R.α k)) =
      (fun k => R.x (k + 1) - R.x k) := by
    funext k
    rw [R.step]
    abel
  rw [heq]
  exact R.differences_tendsto_zero_of_strict_contour hK ℓ hlim hlower hcontour

end BfgsVerification.AdmissibleBFGSRun
