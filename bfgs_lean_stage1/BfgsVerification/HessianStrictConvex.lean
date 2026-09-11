import BfgsVerification.RadialHessian
import Mathlib.Analysis.Convex.Deriv

/-! Strict convexity from the actual second Fréchet derivative on a convex open
region. This proves the sufficient branch-Hessian condition in Module C. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification
namespace HessianGeometry
open RadialHessian

theorem ray_second_derivative_at {n : ℕ} {f : Vec n → ℝ} (x v : Vec n) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (ray x v t)) :
    deriv (deriv (fun s => f (ray x v s))) t = dot v ((matrix f (ray x v t)).mulVec v) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (ray x v t) :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).differentiableAt (by norm_num)
  have hd := hfd.hasFDerivAt.comp_hasDerivAt t (ray_hasDerivAt x v t)
  have ha := hd.clm_apply (hasDerivAt_const t v)
  have heq : deriv (fun s => f (ray x v s)) =ᶠ[𝓝 t]
      (fun s => (fderiv ℝ f (ray x v s)) v) := by
    have hnear := (ray_hasDerivAt x v t).continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hnear] with s hs
    exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (ray_hasDerivAt x v s)).deriv
  rw [matrix,bilinearMatrix_quadratic]
  simpa only [map_zero,add_zero] using (ha.congr_of_eventuallyEq heq).deriv

theorem strictConvexOn_of_positive_hessian {n : ℕ} {f : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    (hh : ∀ x∈U, ∀ v : Vec n, v≠0 → 0<dot v ((matrix f x).mulVec v)) :
    StrictConvexOn ℝ U f := by
  refine ⟨hUc,?_⟩
  intro x hx y hy hxy a b ha hb hab
  let q : ℝ → ℝ := fun t => f (ray x (y-x) t)
  have hp (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : ray x (y-x) t∈U := by
    have he : ray x (y-x) t = (1-t) • x+t • y := by dsimp [ray]; module
    rw [he]
    exact hUc hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (((hf.contDiffAt (hU.mem_nhds (hp t ht))).continuousAt).comp
      (ray_hasDerivAt x (y-x) t).continuousAt).continuousWithinAt
  have hq : StrictConvexOn ℝ (Icc (0 : ℝ) 1) q := by
    apply strictConvexOn_of_deriv2_pos' (convex_Icc _ _) hqc
    intro t ht
    change 0<deriv (deriv (fun s => f (ray x (y-x) s))) t
    rw [ray_second_derivative_at x (y-x) t (hf.contDiffAt (hU.mem_nhds (hp t ht)))]
    exact hh _ (hp t ht) _ (sub_ne_zero.mpr hxy.symm)
  have h := hq.2 (show (0 : ℝ)∈Icc 0 1 by norm_num)
    (show (1 : ℝ)∈Icc 0 1 by norm_num) (by norm_num : (0 : ℝ)≠1) ha hb hab
  have he : ray x (y-x) b=a • x+b • y := by
    rw [show a=1-b by linarith]
    dsimp [ray]
    module
  have h' : f (ray x (y-x) b)<a*f (ray x (y-x) 0)+b*f (ray x (y-x) 1) := by
    simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,q] using h
  rw [he] at h'
  simpa only [ray,zero_smul,add_zero,one_smul,add_sub_cancel,smul_eq_mul] using h'


end HessianGeometry
end BfgsVerification
