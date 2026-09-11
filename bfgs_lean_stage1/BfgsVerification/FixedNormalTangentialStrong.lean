import BfgsVerification.FixedNormalRunBounds

/-! Strong curvature restricted to an actual linear projection. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace FixedNormal

/-- Every actual support inherits the Euclidean strong supporting inequality,
even at a nondifferentiable point. -/
theorem projected_strong_supporting_inequality {n m : ℕ} (P : Vec n →ₗ[ℝ] Vec m) {F : Vec n → ℝ}
    {U : Set (Vec n)} {μ : ℝ} (hstrong : ConvexOn ℝ U (fun x => F x - (μ / 2) * sqNorm (P x)))
    {x z g : Vec n} (hx : x ∈ U) (hz : z ∈ U)
    (hg : Homogeneous.Supports F x g) :
    dot g (z - x) + (μ / 2) * sqNorm (P (z - x)) ≤ F z - F x := by
  have hlim : Tendsto (fun t : ℝ => dot g (z - x) +
      (μ / 2) * (1 - t) * sqNorm (P (z - x))) (𝓝[>] 0)
      (𝓝 (dot g (z - x) + (μ / 2) * sqNorm (P (z - x)))) := by
    have hc : Continuous (fun t : ℝ => dot g (z - x) +
      (μ / 2) * (1 - t) * sqNorm (P (z - x))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht1 ht0
  have ht : 0 < t := ht0
  have hc := hstrong.2 hx hz (by linarith : 0 ≤ 1 - t) ht.le
    (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hc
  rw [map_add, map_smul, map_smul, sqNorm_convex_combination, ← map_sub] at hc
  have hgs := hg ((1 - t) • x + t • z)
  have hv : (1 - t) • x + t • z - x = t • (z - x) := by module
  change dotProduct g ((1 - t) • x + t • z - x) ≤ _ at hgs
  rw [hv, dotProduct_smul] at hgs
  simp only [smul_eq_mul] at hgs
  have hm : t * (dot g (z - x) + (μ / 2) * (1 - t) * sqNorm (P (z - x))) ≤
      t * (F z - F x) := by
    change t * (g ⬝ᵥ (z - x) + _) ≤ _
    nlinarith
  exact (mul_le_mul_left ht).mp hm

/-- Projected strong monotonicity for two actual supports, with no full
positive-curvature lower bound. -/
theorem projected_strong_support_monotonicity {n m : ℕ} (P : Vec n →ₗ[ℝ] Vec m)
    {F : Vec n → ℝ} {U : Set (Vec n)} {μ : ℝ}
    (hstrong : ConvexOn ℝ U (fun x => F x - (μ / 2) * sqNorm (P x)))
    {x z g h : Vec n} (hx : x ∈ U) (hz : z ∈ U)
    (hg : Homogeneous.Supports F x g) (hh : Homogeneous.Supports F z h) :
    μ * sqNorm (P (z - x)) ≤ dot (h - g) (z - x) := by
  have hxz := projected_strong_supporting_inequality P hstrong hx hz hg
  have hzx := projected_strong_supporting_inequality P hstrong hz hx hh
  have hs : sqNorm (P (x - z)) = sqNorm (P (z - x)) := by
    rw [show x - z = -(z - x) by abel, map_neg]
    simp only [sqNorm, Pi.neg_apply, neg_sq]
  have hd : dot h (x - z) = -dot h (z - x) := by
    change h ⬝ᵥ (x - z) = -(h ⬝ᵥ (z - x))
    rw [show x - z = -(z - x) by abel, dotProduct_neg]
  rw [hs, hd] at hzx
  change _ ≤ (h - g) ⬝ᵥ (z - x)
  rw [sub_dotProduct]
  simp only [dot, dotProduct] at hxz hzx ⊢
  nlinarith

/-- On the optimizer's hyperplane, a vanishing common tangential support forces
the point to be the optimizer, including differentiable exceptional points. -/
theorem tangent_zero_on_minimizer_plane_of_projected_strong {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {U : Set (Vec n)} {μ : ℝ} (hμ : 0 < μ)
    {a : Vec n} (hstrong : ConvexOn ℝ U (fun x => F x - (μ / 2) * sqNorm (tangentProjection a x))) {star p : Vec n}
    (hstar : star ∈ U) (hp : p ∈ U) (hmin : ∀ z, F star ≤ F z)
    (hplane : dot a p = dot a star)
    (hA : ∀ g, Homogeneous.Supports F p g → tangentProjection a g = 0) : p = star := by
  obtain ⟨g, hg⟩ := ConvexSubdifferential.subdifferential_nonempty hF p
  have hz : Homogeneous.Supports F star (0 : Vec n) :=
    ConvexSubdifferential.zero_mem_iff_global_minimum.mpr hmin
  have hs := projected_strong_support_monotonicity (tangentMap a) hstrong hstar hp hz hg
  have hge : g = dot a g • a := sub_eq_zero.mp (hA g hg)
  have had : dot a (p - star) = 0 := by
    change dotProduct a (p - star) = 0
    rw [dotProduct_sub]
    exact sub_eq_zero.mpr hplane
  have hgd : dot (g - 0) (p - star) = 0 := by
    simp only [sub_zero]
    change dotProduct g (p - star) = 0
    conv_lhs => arg 1; rw [hge]
    rw [smul_dotProduct]
    change dot a g * dot a (p - star) = 0
    rw [had, mul_zero]
  rw [hgd, tangentMap_apply, tangentProjection_eq_self had] at hs
  have hsq : sqNorm (p - star) ≤ 0 := by nlinarith
  have hnorm : ‖p - star‖ ≤ 0 :=
    ConvexSubdifferential.norm_le_of_sqNorm_le le_rfl (by simpa using hsq)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

end FixedNormal

namespace AdmissibleBFGSRun
open FixedNormal
variable {n m : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem projected_displacement_budget (P : Vec n →ₗ[ℝ] Vec m)
    {U : Set (Vec n)} {μ : ℝ}
    (hstrong : ConvexOn ℝ U (fun x => F x - (μ / 2) * sqNorm (P x)))
    (hx : ∀ k, R.x k ∈ U) (k : ℕ) :
    (μ / 2) * sqNorm (P (R.displacement k)) ≤
      R.d k - (F (R.x k) - F (R.x (k + 1))) := by
  have h := projected_strong_supporting_inequality P hstrong (hx k) (hx (k+1))
    (convex_supporting_inequality R.convex (R.hasGradient k))
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [displacement]
  rw [he] at h
  have hd : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
  rw [hd] at h
  linarith

theorem projected_displacement_sq_le (P : Vec n →ₗ[ℝ] Vec m)
    {U : Set (Vec n)} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ U (fun x => F x - (μ / 2) * sqNorm (P x)))
    (hx : ∀ k, R.x k ∈ U) (k : ℕ) :
    sqNorm (P (R.displacement k)) ≤ (2 / μ) * R.d k := by
  have hb := R.projected_displacement_budget P hstrong hx k
  have hm := R.objective_strict_decrease k
  have hmul : μ * sqNorm (P (R.displacement k)) ≤ 2 * R.d k := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  simpa only [mul_comm] using hmul

end AdmissibleBFGSRun
end BfgsVerification
