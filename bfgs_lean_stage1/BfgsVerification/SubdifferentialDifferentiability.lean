import BfgsVerification.ConvexSubdifferential

/-! For a finite convex function, a singleton actual subdifferential is equivalent
to differentiability. This also provides two distinct supports at every genuinely
nondifferentiable point, without a regularity assumption on a selected support. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace ConvexSubdifferential

/-- Closedness and local boundedness force supporting vectors to converge when
the limiting subdifferential is a singleton. -/
theorem supporting_vectors_tendsto_of_singleton {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x a : ℕ → Vec n} {star g : Vec n}
    (hx : Tendsto x atTop (𝓝 star))
    (hsupport : ∀ k, a k ∈ subdifferential F (x k))
    (hsingle : subdifferential F star = {g}) : Tendsto a atTop (𝓝 g) := by
  obtain ⟨G, hG, hbound⟩ := convex_supporting_bound_on_compact hF hx.isCompact_insert_range
  have hanorm (k : ℕ) : ‖a k‖ ≤ G :=
    norm_le_of_sqNorm_le hG.le
      (hbound (x k) (mem_insert_of_mem _ (mem_range_self k)) (a k) (hsupport k))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push_neg at hn
  let S := Metric.closedBall (0 : Vec n) G ∩ {p | ε ≤ dist p g}
  have hS : IsCompact S := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfreq : ∃ᶠ k in atTop, a k ∈ S := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk, hd⟩ := hn N
    refine ⟨k, hk, ?_, hd⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hanorm k
  obtain ⟨p, hp, φ, hφ, hpconv⟩ := hS.tendsto_subseq' hfreq
  have hps : p ∈ subdifferential F star := supporting_limit (convex_continuous hF)
    (hx.comp hφ.tendsto_atTop) hpconv (fun k z => hsupport (φ k) z)
  have heq : p = g := by simpa only [hsingle, mem_singleton_iff] using hps
  have hd : ε ≤ dist p g := hp.2
  rw [heq, dist_self] at hd
  linarith

/-- The coordinate representation of a derivative depends continuously on its
representing vector, in the actual continuous-linear-map operator norm. -/
theorem continuous_gradientFunctional {n : ℕ} :
    Continuous (gradientFunctional : Vec n → (Vec n →L[ℝ] ℝ)) := by
  unfold gradientFunctional
  fun_prop

/-- The singleton criterion is derived from actual supporting inequalities. -/
theorem hasFDerivAt_of_subdifferential_eq_singleton {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x g : Vec n}
    (hsingle : subdifferential F x = {g}) :
    HasFDerivAt F (gradientFunctional g) x := by
  choose a ha using subdifferential_nonempty hF
  have hag : Tendsto a (𝓝 x) (𝓝 g) := by
    apply tendsto_nhds_iff_seq_tendsto.mpr
    intro z hz
    exact supporting_vectors_tendsto_of_singleton hF hz (fun k => ha (z k)) hsingle
  have hlim : Tendsto (fun z => ‖gradientFunctional (a z - g)‖) (𝓝 x) (𝓝 0) := by
    have h := (continuous_gradientFunctional.tendsto (0 : Vec n)).comp
      (by simpa using hag.sub_const g)
    simpa [gradientFunctional] using h.norm
  have hgs : g ∈ subdifferential F x := by rw [hsingle]; exact mem_singleton g
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun z => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ hlim
  intro z
  by_cases hzx : z = x
  · simp [hzx]
  · have hnorm : ‖z - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzx)
    have hlo : 0 ≤ F z - F x - dot g (z - x) := sub_nonneg.mpr (hgs z)
    have hhi : F z - F x - dot g (z - x) ≤ dot (a z - g) (z - x) := by
      have h := ha z x
      have hxz : x - z = -(z - x) := by abel
      change dotProduct (a z) (x - z) ≤ _ at h
      rw [hxz, dotProduct_neg] at h
      change _ ≤ dotProduct (a z - g) (z - x)
      rw [sub_dotProduct]
      change F z - F x - g ⬝ᵥ (z - x) ≤ a z ⬝ᵥ (z - x) - g ⬝ᵥ (z - x)
      linarith
    have hrem : ‖F z - F x - gradientFunctional g (z - x)‖ ≤
        ‖gradientFunctional (a z - g)‖ * ‖z - x‖ := by
      rw [gradientFunctional_apply, Real.norm_eq_abs, abs_of_nonneg hlo]
      exact hhi.trans ((le_abs_self _).trans
        (by simpa only [Real.norm_eq_abs, gradientFunctional_apply] using
          (gradientFunctional (a z - g)).le_opNorm (z - x)))
    calc
      _ ≤ ‖z - x‖⁻¹ * (‖gradientFunctional (a z - g)‖ * ‖z - x‖) :=
        mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr (norm_nonneg _))
      _ = ‖gradientFunctional (a z - g)‖ := by
        rw [mul_left_comm, inv_mul_cancel₀ hnorm, mul_one]

/-- Exact equivalence, including identification of the actual derivative. -/
theorem subdifferential_eq_singleton_iff_hasFDerivAt {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x g : Vec n} :
    subdifferential F x = {g} ↔ HasFDerivAt F (gradientFunctional g) x :=
  ⟨hasFDerivAt_of_subdifferential_eq_singleton hF,
    subdifferential_eq_singleton_of_hasFDerivAt hF⟩

/-- Every genuinely nondifferentiable point has distinct actual subgradients. -/
theorem exists_distinct_supports_of_not_differentiableAt {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x : Vec n} (hx : ¬DifferentiableAt ℝ F x) :
    ∃ g ∈ subdifferential F x, ∃ h ∈ subdifferential F x, g ≠ h := by
  obtain ⟨g, hg⟩ := subdifferential_nonempty hF x
  by_contra hn
  push_neg at hn
  have hsingle : subdifferential F x = {g} := by
    ext a
    constructor
    · intro ha
      exact (hn g hg a ha).symm
    · rintro rfl
      exact hg
  exact hx (hasFDerivAt_of_subdifferential_eq_singleton hF hsingle).differentiableAt

end ConvexSubdifferential
end BfgsVerification
