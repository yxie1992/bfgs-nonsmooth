import BfgsVerification.RadialApproximation

/-! The complete reverse half of R:thm:equiv. Approximation removes inner-point
differentiability on the same original compact sublevel, including its boundary. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace RadialCertificate

set_option maxHeartbeats 800000 in
/-- Module R's full RS→IR implication. No derivative is assumed at the inward
sample. No enlarged sublevel, unique minimizer, or gradient continuity is used. -/
theorem inward_of_radial_on_compact_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b : ℝ) (hb : F star < b) (hK : IsCompact {x : Vec n | F x ≤ b})
    (hRS : HasRadialSecantBounds F {x | F x ≤ b} star) :
    HasInwardTaylorBounds F {x | F x ≤ b} star := by
  obtain ⟨G, hG, hgBound⟩ := convex_gradient_bound_on_compact hF hK
  obtain ⟨R, hR, hrBound⟩ := compact_sqNorm_radius hK star
  have hc := convex_continuous hF
  intro η hη
  obtain ⟨C, hC⟩ := hRS (η / 2) (by positivity)
  let C' := max C 0
  let θ := min (1 / 2 : ℝ) (η / (4 * G * R))
  have hC' : 0 ≤ C' := le_max_right _ _
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hθhalf : θ ≤ 1 / 2 := min_le_left _ _
  refine ⟨8 * C', θ, hθ, hθhalf, ?_⟩
  intro x g hx hxband hg t ht0 htθ
  refine ⟨supportingError_nonneg hF hg _, ?_⟩
  by_cases htzero : t = 0
  · subst t
    simp [inwardPoint, supportingError, dot]
  have hthalf : t ≤ 1 / 2 := htθ.trans hθhalf
  have htone : t ≤ 1 := by linarith
  have htne : t ≠ 1 := by linarith
  have hmargin := inward_positive_band_margin hF star x g hg G R η hG hR
    (hgBound x hx g hg) (hrBound x hx) hxband ht0 (htθ.trans (min_le_right _ _))
  let O := {w : Vec n | F star + η / 2 < F (inwardPoint star w t)}
  have hO : IsOpen O := isOpen_lt continuous_const (hc.comp (continuous_inwardPoint star t))
  have hxO : x ∈ O := by dsimp only [O, mem_setOf_eq]; linarith
  obtain ⟨u, hux, hu⟩ := exists_inward_pair_approximation hF star b hb x hx hO hxO htne
  let gj := fun j => coordinateGradient F (u j)
  let hj := fun j => coordinateGradient F (inwardPoint star (u j) t)
  have hgj (j : ℕ) : HasFDerivAt F (gradientFunctional (gj j)) (u j) :=
    hasFDerivAt_coordinateGradient (hu j).2.2.1
  have hhj (j : ℕ) : HasFDerivAt F (gradientFunctional (hj j)) (inwardPoint star (u j) t) :=
    hasFDerivAt_coordinateGradient (hu j).2.2.2
  have hbound (j : ℕ) : supportingError F (u j) (gj j) (inwardPoint star (u j) t) ≤
      4 * C' * t ^ 2 := by
    apply inward_error_le_of_pair_radial hF star (u j) (gj j) (hj j) t C'
      ht0 hthalf hC' (hgj j) (hhj j)
    intro htcurv
    have huK : F (u j) ≤ b :=
      interior_subset (s := {w : Vec n | F w ≤ b}) (hu j).1
    have horder := inward_value_le hF star hmin (u j) ht0 htone
    have hzK : F (inwardPoint star (u j) t) ≤ b := horder.trans huK
    have hzband : F star + η / 2 ≤ F (inwardPoint star (u j) t) := (hu j).2.1.le
    exact (hC (u j) (inwardPoint star (u j) t) (gj j) (hj j)
      huK hzK hzband horder (hgj j) (hhj j) htcurv).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) htcurv.le)
  have hgjlim : Tendsto gj atTop (𝓝 g) :=
    convex_gradients_tendsto_at_differentiable hF hux hgj hg
  have hzlim : Tendsto (fun j => inwardPoint star (u j) t) atTop (𝓝 (inwardPoint star x t)) :=
    ((continuous_inwardPoint star t).tendsto x).comp hux
  have hdot : Tendsto (fun j => dot (gj j) (u j - star)) atTop (𝓝 (dot g (x - star))) :=
    (continuous_dot.tendsto (g, x - star)).comp (hgjlim.prodMk_nhds (hux.sub tendsto_const_nhds))
  have herr : Tendsto (fun j => supportingError F (u j) (gj j) (inwardPoint star (u j) t))
      atTop (𝓝 (supportingError F x g (inwardPoint star x t))) := by
    simp only [inward_error_eq]
    exact (((hc.tendsto _).comp hzlim).sub ((hc.tendsto x).comp hux)).add
      (tendsto_const_nhds.mul hdot)
  have hfinal := le_of_tendsto_of_tendsto' herr tendsto_const_nhds hbound
  calc
    supportingError F x g (inwardPoint star x t) ≤ 4 * C' * t ^ 2 := hfinal
    _ = (8 * C') / 2 * t ^ 2 := by ring

/-- R:thm:equiv, with the exact same compact positive sublevel in both directions. -/
theorem radial_iff_inward_on_compact_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b : ℝ) (hb : F star < b) (hK : IsCompact {x : Vec n | F x ≤ b}) :
    HasRadialSecantBounds F {x | F x ≤ b} star ↔
      HasInwardTaylorBounds F {x | F x ≤ b} star :=
  ⟨inward_of_radial_on_compact_sublevel hF star hmin b hb hK,
    radial_of_inward_on_compact hF hK star⟩

/-- All three source objective-pair formulations are equivalent on the same
compact sublevel: radial secants, inward Taylor bounds, and supporting intercepts. -/
theorem inward_iff_intercept_on_compact_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b : ℝ) (hb : F star < b) (hK : IsCompact {x : Vec n | F x ≤ b}) :
    HasInwardTaylorBounds F {x | F x ≤ b} star ↔
      HasInterceptBounds F {x | F x ≤ b} star :=
  (radial_iff_inward_on_compact_sublevel hF star hmin b hb hK).symm.trans
    (radial_iff_intercept_on_compact hF hK star)

end RadialCertificate
end BfgsVerification
