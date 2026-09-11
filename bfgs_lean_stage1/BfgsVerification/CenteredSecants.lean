import BfgsVerification.CenteredCocoercivity
import BfgsVerification.Homogeneous

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix

namespace BfgsVerification
namespace CenteredSmoothSublinear

/-- The weighted square estimate, including either zero curvature component. -/
theorem square_sum_le_weighted {a b A B ξ ζ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hξ : ξ ^ 2 ≤ A * a) (hζ : ζ ^ 2 ≤ B * b) :
    (ξ + ζ) ^ 2 ≤ (A + B) * (a + b) := by
  by_cases haz : a = 0
  · have hξz : ξ = 0 := by rw [haz] at hξ; nlinarith [sq_nonneg ξ]
    rw [haz, hξz]
    nlinarith [mul_nonneg hA hb]
  by_cases hbz : b = 0
  · have hζz : ζ = 0 := by rw [hbz] at hζ; nlinarith [sq_nonneg ζ]
    rw [hbz, hζz]
    nlinarith [mul_nonneg hB ha]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hw : (ξ + ζ) ^ 2 ≤ (a + b) * (ξ ^ 2 / a + ζ ^ 2 / b) := by
    apply (mul_le_mul_right (mul_pos hap hbp)).mp
    field_simp
    nlinarith [sq_nonneg (b * ξ - a * ζ)]
  have hdiv : ξ ^ 2 / a + ζ ^ 2 / b ≤ A + B :=
    add_le_add ((div_le_iff₀ hap).mpr hξ) ((div_le_iff₀ hbp).mpr hζ)
  exact hw.trans ((mul_le_mul_of_nonneg_left hdiv (add_nonneg ha hb)).trans_eq (mul_comm _ _))

theorem gradientFunctional_sub {n : ℕ} (g p : Vec n) :
    gradientFunctional g - gradientFunctional p = gradientFunctional (g - p) := by
  ext v
  simp only [ContinuousLinearMap.sub_apply, gradientFunctional_apply]
  exact (sub_dotProduct _ _ _).symm

/-- At a differentiable accepted endpoint the nonsmooth summand's derivative
is derived by subtraction and translation from the actual objective derivative. -/
theorem homogeneous_summand_derivative {n : ℕ} {F ψ γ : Vec n → ℝ}
    (star : Vec n) {U : Set (Vec n)} (hU : IsOpen U)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    {x g p : Vec n} (hx : x ∈ U)
    (hF : HasFDerivAt F (gradientFunctional g) x)
    (hψ : HasFDerivAt ψ (gradientFunctional p) x) :
    HasFDerivAt γ (gradientFunctional (g - p)) (x - star) := by
  have hd := hF.sub hψ
  rw [gradientFunctional_sub] at hd
  have hd' : HasFDerivAt (fun y => F y - ψ y) (gradientFunctional (g - p))
      (x - star + star) := by simpa only [sub_add_cancel] using hd
  have hc := hd'.comp (x - star) ((hasFDerivAt_id (x - star)).add_const star)
  simp only [ContinuousLinearMap.comp_id] at hc
  apply hc.congr_of_eventuallyEq
  have hnear : ∀ᶠ z in 𝓝 (x - star), z + star ∈ U := by
    have ht : Tendsto (fun z : Vec n => z + star) (𝓝 (x - star)) (𝓝 x) := by
      have ht' : Continuous (fun z : Vec n => z + star) := by fun_prop
      simpa only [sub_add_cancel] using ht'.tendsto (x - star)
    exact ht.eventually (hU.mem_nhds hx)
  filter_upwards [hnear] with z hz
  dsimp [Function.comp_def]
  rw [hrep (z + star) hz, add_sub_cancel_right]
  ring

/-- The homogeneous contribution has a nonnegative new-point pairing bounded
by its own secant curvature, with no sign or coercivity assumption on gamma. -/
theorem homogeneous_secant_pairing {n : ℕ} {γ : Vec n → ℝ}
    (hγ : Homogeneous.PositiveDegreeOne γ) {x y p q : Vec n}
    (hp : Homogeneous.Supports γ x p) (hq : Homogeneous.Supports γ y q) :
    0 ≤ dot (q - p) y ∧ dot (q - p) y ≤ dot (q - p) (y - x) := by
  have hep := Homogeneous.supporting_euler hγ hp
  have heq := Homogeneous.supporting_euler hγ hq
  have hpy := Homogeneous.supporting_linear_le hγ hp y
  have hqx := Homogeneous.supporting_linear_le hγ hq x
  have hy : dot (q - p) y = dot q y - dot p y := sub_dotProduct _ _ _
  have hx : dot (q - p) x = dot q x - dot p x := sub_dotProduct _ _ _
  have hs : dot (q - p) (y - x) = dot (q - p) y - dot (q - p) x := dotProduct_sub _ _ _
  constructor <;> linarith


/-- The source correction estimate from the two actual secant components.
Both component curvatures are allowed to vanish. -/
theorem correction_le_of_split {n : ℕ} (u v r s : Vec n) (L G R : ℝ)
    (hL : 0 < L) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hu : sqNorm u ≤ L * dot u s)
    (hv : 0 ≤ dot v r ∧ dot v r ≤ dot v s)
    (hvn : sqNorm v ≤ (2 * G) ^ 2) (hr : sqNorm r ≤ R ^ 2)
    (ht : 0 < dot (u + v) s) :
    (dot (u + v) r) ^ 2 / dot (u + v) s ≤ L * R ^ 2 + 2 * G * R := by
  have ha : 0 ≤ dot u s := nonneg_of_mul_nonneg_right ((sqNorm_nonneg u).trans hu) hL
  have hb : 0 ≤ dot v s := hv.1.trans hv.2
  have hξ : (dot u r) ^ 2 ≤ (L * R ^ 2) * dot u s := by
    calc
      (dot u r) ^ 2 ≤ sqNorm u * sqNorm r := dot_sq_le_sqNorm_mul_sqNorm u r
      _ ≤ (L * dot u s) * R ^ 2 := mul_le_mul hu hr (sqNorm_nonneg r) (mul_nonneg hL.le ha)
      _ = _ := by ring
  have hζ : dot v r ≤ 2 * G * R :=
    (le_abs_self _).trans (abs_dot_le_of_sqNorm_le v r (2 * G) R (by positivity) hR hvn hr)
  have hζsq : (dot v r) ^ 2 ≤ (2 * G * R) * dot v s := by
    have hmul := mul_le_mul hv.2 hζ hv.1 hb
    nlinarith
  have hh := square_sum_le_weighted ha hb (mul_nonneg hL.le (sq_nonneg R))
    (by positivity : 0 ≤ 2 * G * R) hξ hζsq
  apply (div_le_iff₀ ht).mpr
  have hsr : dot (u + v) r = dot u r + dot v r := add_dotProduct _ _ _
  have hss : dot (u + v) s = dot u s + dot v s := add_dotProduct _ _ _
  simpa only [hsr, hss] using hh

end CenteredSmoothSublinear
end BfgsVerification
