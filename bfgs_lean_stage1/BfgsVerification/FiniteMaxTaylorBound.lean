import BfgsVerification.FiniteMaxGradientBound
import BfgsVerification.RadialHessian

/-! The upper Taylor model for the actual finite maximum, derived from the
branches and the proved removal of inactive branches. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification
namespace FiniteMaxHessian
open ConvexSubdifferential

/-- The Euclidean descent lemma with the original constant and actual coordinate
 gradients. Convexity is not required. -/
theorem branch_upper_taylor {n : ℕ} {f : Vec n → ℝ} {g : Vec n → Vec n}
    {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ z, HasFDerivAt f (gradientFunctional (g z)) z)
    (hlip : ∀ z w, sqNorm (g z - g w) ≤ L ^ 2 * sqNorm (z - w))
    (x z : Vec n) : f z ≤ f x + dot (g x) (z - x) + (L / 2) * sqNorm (z - x) := by
  let v := z - x
  let r : ℝ → ℝ := fun t => f (RadialHessian.ray x v t) - f x -
    t * dot (g x) v - (L / 2) * t ^ 2 * sqNorm v
  let dr : ℝ → ℝ := fun t => dot (g (RadialHessian.ray x v t)) v -
    dot (g x) v - L * t * sqNorm v
  have hd (t : ℝ) : HasDerivAt r (dr t) t := by
    have hlinear : HasDerivAt (fun u : ℝ => u * dot (g x) v) (dot (g x) v) t := by
      simpa using (hasDerivAt_id t).mul_const (dot (g x) v)
    have hquad : HasDerivAt (fun u : ℝ => (L / 2) * u ^ 2 * sqNorm v)
        (L * t * sqNorm v) t := by
      convert (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (sqNorm v) using 1 <;> simp only [id_eq] <;> ring
    simpa only [r, dr, Function.comp_apply, gradientFunctional_apply] using
      ((((hg (RadialHessian.ray x v t)).comp_hasDerivAt t
        (RadialHessian.ray_hasDerivAt x v t)).sub_const (f x)).sub hlinear).sub hquad
  have hneg (t : ℝ) (ht : 0 ≤ t) : dr t ≤ 0 := by
    have hb := hlip (RadialHessian.ray x v t) x
    have he : RadialHessian.ray x v t - x = t • v := by simp [RadialHessian.ray]
    rw [he, RadialPower.sqNorm_smul] at hb
    have hsq : sqNorm (g (RadialHessian.ray x v t) - g x) ≤
        (L * t) ^ 2 * sqNorm v := by nlinarith [hb]
    have ha := abs_dot_le_relative (mul_nonneg hL ht) hsq
    have hle := (le_abs_self _).trans ha
    have hedot : dot (g (RadialHessian.ray x v t) - g x) v =
        dot (g (RadialHessian.ray x v t)) v - dot (g x) v := sub_dotProduct _ _ _
    rw [hedot] at hle
    dsimp [dr]
    nlinarith
  have hanti : AntitoneOn r (Icc (0 : ℝ) 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      ((continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hd t).deriv]; exact hneg t (by simpa using (interior_subset ht).1))
  have hb := hanti (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hz : RadialHessian.ray x v 1 = z := by simp [RadialHessian.ray, v]
  simp only [r, hz, RadialHessian.ray, zero_smul, add_zero, zero_mul,
    sub_self, sub_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, one_mul, one_pow, mul_one] at hb
  dsimp [v] at hb
  simp only [one_smul, add_sub_cancel] at hb
  linarith

/-- The same upper quadratic model holds locally for the actual maximum at any
 differentiable point, after deriving the inactive-branch gap. -/
theorem finiteMax_local_upper_taylor {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n → Vec n}
    {x a : Vec n} {L : ℝ} (hL : 0 ≤ L) (hrep : LocalFiniteMax F f x)
    (hF : HasFDerivAt F (gradientFunctional a) x)
    (hg : ∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z)
    (hlip : ∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w)) :
    ∀ᶠ z in 𝓝 x, F z ≤ F x + dot a (z - x) + (L / 2) * sqNorm (z - x) := by
  filter_upwards [hrep, activeIndices_eventually_subset hF.continuousAt
    (fun i => (hg i x).continuousAt) hrep] with z hz hsub
  obtain ⟨i, hi⟩ := hz.1
  dsimp only at hi
  have hix := hsub (mem_activeIndices.mpr hi)
  have hgrad := active_derivative_eq hrep hF (hg i x) hix
  have he : dot (g i x) (z - x) = dot a (z - x) := by
    simpa only [gradientFunctional_apply] using DFunLike.congr_fun hgrad (z - x)
  have hb := branch_upper_taylor hL (hg i) (hlip i) x z
  rwa [hi, mem_activeIndices.mp hix, he] at hb

end FiniteMaxHessian
end BfgsVerification
