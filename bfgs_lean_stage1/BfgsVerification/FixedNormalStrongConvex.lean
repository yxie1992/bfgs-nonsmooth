import BfgsVerification.ConvexSubdifferential
import BfgsVerification.CenteredSmoothCalculus
import BfgsVerification.CompactConvergence

/-! Euclidean strong convexity, stated using the actual sum of coordinate
squares, and its consequences for actual BFGS displacements. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace FixedNormal

/-- Euclidean strong convexity on a specified neighborhood. The ambient Pi norm
is not used in this definition. -/
def EuclideanStrongConvexOn {n : ℕ} (U : Set (Vec n)) (μ : ℝ) (F : Vec n → ℝ) : Prop :=
  ConvexOn ℝ U (fun x => F x - (μ / 2) * sqNorm x)

theorem sqNorm_convex_combination {n : ℕ} (x z : Vec n) (t : ℝ) :
    sqNorm ((1 - t) • x + t • z) =
      (1 - t) * sqNorm x + t * sqNorm z - t * (1 - t) * sqNorm (z - x) := by
  simp only [sqNorm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Every actual support inherits the Euclidean strong supporting inequality,
even at a nondifferentiable point. -/
theorem strong_supporting_inequality {n : ℕ} {F : Vec n → ℝ}
    {U : Set (Vec n)} {μ : ℝ} (hstrong : EuclideanStrongConvexOn U μ F)
    {x z g : Vec n} (hx : x ∈ U) (hz : z ∈ U)
    (hg : Homogeneous.Supports F x g) :
    dot g (z - x) + (μ / 2) * sqNorm (z - x) ≤ F z - F x := by
  have hlim : Tendsto (fun t : ℝ => dot g (z - x) +
      (μ / 2) * (1 - t) * sqNorm (z - x)) (𝓝[>] 0)
      (𝓝 (dot g (z - x) + (μ / 2) * sqNorm (z - x))) := by
    have hc : Continuous (fun t : ℝ => dot g (z - x) +
      (μ / 2) * (1 - t) * sqNorm (z - x)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht1 ht0
  have ht : 0 < t := ht0
  have hc := hstrong.2 hx hz (by linarith : 0 ≤ 1 - t) ht.le
    (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hc
  rw [sqNorm_convex_combination] at hc
  have hgs := hg ((1 - t) • x + t • z)
  have hv : (1 - t) • x + t • z - x = t • (z - x) := by module
  change dotProduct g ((1 - t) • x + t • z - x) ≤ _ at hgs
  rw [hv, dotProduct_smul] at hgs
  simp only [smul_eq_mul] at hgs
  have hm : t * (dot g (z - x) + (μ / 2) * (1 - t) * sqNorm (z - x)) ≤
      t * (F z - F x) := by
    change t * (g ⬝ᵥ (z - x) + _) ≤ _
    nlinarith
  exact (mul_le_mul_left ht).mp hm

/-- Strong monotonicity of any two actual subgradients. -/
theorem strong_support_monotonicity {n : ℕ} {F : Vec n → ℝ}
    {U : Set (Vec n)} {μ : ℝ} (hstrong : EuclideanStrongConvexOn U μ F)
    {x z g h : Vec n} (hx : x ∈ U) (hz : z ∈ U)
    (hg : Homogeneous.Supports F x g) (hh : Homogeneous.Supports F z h) :
    μ * sqNorm (z - x) ≤ dot (h - g) (z - x) := by
  have ha := strong_supporting_inequality hstrong hx hz hg
  have hb := strong_supporting_inequality hstrong hz hx hh
  have hsq : sqNorm (x - z) = sqNorm (z - x) := by
    unfold sqNorm
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hxz : x - z = -(z - x) := by abel
  rw [hsq] at hb
  change dotProduct h (x - z) + _ ≤ _ at hb
  rw [hxz, dotProduct_neg] at hb
  change _ ≤ dotProduct (h - g) (z - x)
  rw [sub_dotProduct]
  change g ⬝ᵥ (z - x) + _ ≤ _ at ha
  linarith

end FixedNormal

namespace AdmissibleBFGSRun
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- U.10, for the actual accepted step and actual predicted decrease. -/
theorem strong_displacement_budget {U : Set (Vec n)} {μ : ℝ}
    (hstrong : FixedNormal.EuclideanStrongConvexOn U μ F)
    (hx : ∀ k, R.x k ∈ U) (k : ℕ) :
    (μ / 2) * sqNorm (R.displacement k) ≤
      R.d k - (F (R.x k) - F (R.x (k + 1))) := by
  have hs := FixedNormal.strong_supporting_inequality hstrong (hx k) (hx (k + 1))
    (convex_supporting_inequality R.convex (R.hasGradient k))
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [displacement]
  have hdot : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
  rw [he, hdot] at hs
  linarith

/-- U.10's actual strong curvature lower bound. -/
theorem strong_curvature_bound {U : Set (Vec n)} {μ : ℝ}
    (hstrong : FixedNormal.EuclideanStrongConvexOn U μ F)
    (hx : ∀ k, R.x k ∈ U) (k : ℕ) :
    μ * sqNorm (R.displacement k) ≤ R.curvature k := by
  have hs := FixedNormal.strong_support_monotonicity hstrong (hx k) (hx (k + 1))
    (convex_supporting_inequality R.convex (R.hasGradient k))
    (convex_supporting_inequality R.convex (R.hasGradient (k + 1)))
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [displacement]
  rw [he] at hs
  exact hs

/-- Strong convexity converts the actual predicted decrease into a Euclidean
squared-displacement bound. -/
theorem strong_displacement_sq_le {U : Set (Vec n)} {μ : ℝ}
    (hμ : 0 < μ) (hstrong : FixedNormal.EuclideanStrongConvexOn U μ F)
    (hx : ∀ k, R.x k ∈ U) (k : ℕ) :
    sqNorm (R.displacement k) ≤ (2 / μ) * R.d k := by
  have hs := R.strong_displacement_budget hstrong hx k
  have hd := R.objective_strict_decrease k
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  nlinarith

/-- Compact sublevel trapping and Armijo derive square summability; no iterate
or matrix limit, nor a summability premise, is supplied. -/
theorem summable_sq_displacement_of_strong_convexity {U : Set (Vec n)} {μ : ℝ}
    (hμ : 0 < μ) (hstrong : FixedNormal.EuclideanStrongConvexOn U μ F)
    (hK : IsCompact R.initialSublevel) (hKU : R.initialSublevel ⊆ U) :
    Summable (fun k => sqNorm (R.displacement k)) := by
  have hs := (R.summable_predicted_decreases_of_compact_sublevel hK).mul_left (2 / μ)
  exact hs.of_nonneg_of_le (fun k => sqNorm_nonneg _)
    (R.strong_displacement_sq_le hμ hstrong (fun k => hKU (R.iterate_mem_initialSublevel k)))

/-- Every actual displacement tends to zero under the objective's local strong
convexity and compact sublevel assumptions. -/
theorem displacement_tendsto_zero_of_strong_convexity {U : Set (Vec n)} {μ : ℝ}
    (hμ : 0 < μ) (hstrong : FixedNormal.EuclideanStrongConvexOn U μ F)
    (hK : IsCompact R.initialSublevel) (hKU : R.initialSublevel ⊆ U) :
    Tendsto R.displacement atTop (𝓝 0) := by
  have hs := (R.summable_sq_displacement_of_strong_convexity hμ hstrong hK hKU).tendsto_atTop_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) (fun k =>
    ConvexSubdifferential.norm_le_of_sqNorm_le (Real.sqrt_nonneg _)
      (le_of_eq (Real.sq_sqrt (sqNorm_nonneg (R.displacement k))).symm))
  simpa using hs.sqrt

end AdmissibleBFGSRun
end BfgsVerification
