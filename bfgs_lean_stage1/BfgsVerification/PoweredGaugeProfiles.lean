import BfgsVerification.PoweredGaugeRadial
import Mathlib.Analysis.Seminorm

/-! Actual scalar radial derivatives and standard seminorm instances for R.6. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.RadialPower

theorem powered_radial_hasDerivAt {n : ℕ} {γ : Vec n → ℝ}
    (hh : Homogeneous.PositiveDegreeOne γ) (hn : ∀ z, 0 ≤ γ z)
    (p : ℝ) (z : Vec n) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun u : ℝ => powered γ p ((1-u) • z))
      (-p*(1-t)^(p-1)*powered γ p z) t := by
  have heq : (fun u : ℝ => powered γ p ((1-u) • z)) =ᶠ[𝓝 t]
      (fun u => profile p u*powered γ p z) := by
    filter_upwards [eventually_lt_nhds ht] with u hu
    exact powered_homogeneous hh hn p (1-u) (sub_nonneg.mpr hu.le) z
  exact ((profile_hasDerivAt p ht).mul_const _).congr_of_eventuallyEq heq

theorem powered_radial_derivative_hasDerivAt {n : ℕ} {γ : Vec n → ℝ}
    (hh : Homogeneous.PositiveDegreeOne γ) (hn : ∀ z, 0 ≤ γ z)
    (p : ℝ) (z : Vec n) {t : ℝ} (ht : t < 1) :
    HasDerivAt (deriv (fun u : ℝ => powered γ p ((1-u) • z)))
      (p*(p-1)*(1-t)^(p-2)*powered γ p z) t := by
  have heq : deriv (fun u : ℝ => powered γ p ((1-u) • z)) =ᶠ[𝓝 t]
      (fun u => deriv (profile p) u*powered γ p z) := by
    filter_upwards [eventually_lt_nhds ht] with u hu
    rw [(powered_radial_hasDerivAt hh hn p z hu).deriv,
      (profile_hasDerivAt p hu).deriv]
  exact ((profile_derivative_hasDerivAt p ht).mul_const _).congr_of_eventuallyEq heq

/-- The source's bounded-set assertion concerns the actual one-dimensional
radial profile. This is valid for every real exponent p≥1, including 1<p<2. -/
theorem powered_radial_second_derivative_bounded {n : ℕ} {γ : Vec n → ℝ}
    (hγ : ConvexOn ℝ univ γ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hn : ∀ z, 0 ≤ γ z) {p : ℝ} (hp : 1 ≤ p) {K : Set (Vec n)}
    (hK : Bornology.IsBounded K) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, ∀ t ∈ Icc 0 (1/2),
      |deriv (deriv (fun u : ℝ => powered γ p ((1-u) • z))) t| ≤ M := by
  obtain ⟨C,hC,hc⟩ := profile_second_derivative_bounded p
  obtain ⟨B,hb⟩ := (hK.isCompact_closure.bddAbove_image
    (convex_continuous (powered_convex hγ hn hp)).continuousOn)
  refine ⟨C*(|B|+1),mul_pos hC (by positivity),?_⟩
  intro z hz t ht
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 (by norm_num)
  rw [(powered_radial_derivative_hasDerivAt hh hn p z ht1).deriv,abs_mul,
    abs_of_nonneg (powered_nonneg γ hn p z)]
  have hc' := hc t ht
  rw [(profile_derivative_hasDerivAt p ht1).deriv] at hc'
  have hb' : powered γ p z ≤ |B|+1 := by
    exact (hb ⟨z,subset_closure hz,rfl⟩).trans (by linarith [le_abs_self B])
  exact mul_le_mul hc' hb' (powered_nonneg γ hn p z) hC.le

theorem seminorm_homogeneous {n : ℕ} (q : Seminorm ℝ (Vec n)) :
    Homogeneous.PositiveDegreeOne q := by
  intro a ha z
  rw [map_smul_eq_mul,Real.norm_of_nonneg ha]

/-- Arbitrary finite seminorms are admissible components, even when singular
linear maps or null directions make individual terms noncoercive. -/
theorem seminorm_mixed_powers_radial {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (q : ∀ j, Seminorm ℝ (Vec (m j))) (A : ∀ j, Vec n →ₗ[ℝ] Vec (m j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec n) {U K : Set (Vec n)}
    (hU : IsOpen U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j, (q j (A j (x-star)))^(p j)) :
    RadialCertificate.HasRadialSecantBounds F K star :=
  mixed_linear_powers_radial hF (fun j => q j) (fun j => (q j).convexOn)
    (fun j => seminorm_homogeneous (q j)) (fun j x => apply_nonneg (q j) x)
    A p hp star hU hsmooth hK hKU hrep

end BfgsVerification.RadialPower
