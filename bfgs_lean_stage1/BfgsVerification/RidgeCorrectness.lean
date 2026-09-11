import BfgsVerification.RidgeCalculus

noncomputable section
open scoped Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification.RidgeSupersession
open ConvexSubdifferential HomogeneousPlanar AffineCriticalObjective PlanarCornerCharts

theorem profile_convex {a b : ℝ → ℝ} (ha : ConvexOn ℝ univ a) (hb : ConvexOn ℝ univ b)
    {p q : ℝ} (hp : 0<p) (hq : 0<q) : ConvexOn ℝ univ (profile a b p q) := by
  have h := ((ha.smul hq.le).add (hb.smul hp.le)).smul (inv_nonneg.mpr (add_pos hp hq).le)
  simpa only [profile,Pi.add_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

theorem profile_deriv_zero_implies_optimizer {a b : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    {p q u : ℝ} (hp : 0<p) (hq : 0<q)
    (hmin : ∀t,profile a b p q u ≤ profile a b p q t)
    (hunique : ∀t,profile a b p q t=profile a b p q u → t=u)
    (t : ℝ) (ht : deriv (profile a b p q) t=0) : t=u := by
  have hd := (profile_hasDerivAt ha hb p q t).differentiableAt
  have he : derivWithin (profile a b p q) (Ioi t) t=0 := by
    rw [hd.derivWithin (uniqueDiffWithinAt_Ioi t),ht]
  have hm := (profile_convex hca hcb hp hq).isMinOn_of_rightDeriv_eq_zero (by simp) he
  exact hunique t (le_antisymm (hm (mem_univ u)) (hmin t))

theorem tie_point {a b : ℝ → ℝ} {p q : ℝ} (hpq : p+q≠0)
    (x : Vec 2) (htie : branch a b p q 0 x=branch a b p q 1 x) :
    x=optimizer a b p q (x 0) := by
  have hv : x 1=ridge a b p q (x 0) := by
    apply (eq_div_iff hpq).mpr
    change a (x 0)+p*x 1=b (x 0)-q*x 1 at htie
    nlinarith
  ext i
  fin_cases i <;> simp [optimizer,hv]

/-- There is no false affine criticality, including the two-active-gradient
switching curve; its only determinant-zero tie is the actual optimizer. -/
theorem source_affineCorrect {a b : ℝ → ℝ}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    {p q u : ℝ} (hp : 0<p) (hq : 0<q)
    (hmin : ∀t,profile a b p q u ≤ profile a b p q t)
    (hunique : ∀t,profile a b p q t=profile a b p q u → t=u)
    (x : Vec 2) : AffineCorrectAt (objective a b p q) x := by
  have hF := objective_convex hca hcb p q
  have hA := ha.differentiable (by norm_num)
  have hB := hb.differentiable (by norm_num)
  have hg := branch_hasGradient hA hB p q x
  have hrep := localFiniteMax a b p q x
  by_cases htie : branch a b p q 0 x=branch a b p q 1 x
  · intro hcrit
    have hact : ∀i,branch a b p q i x=objective a b p q x := by
      have ht : a (x 0)+p*x 1=b (x 0)-q*x 1 := htie
      intro i
      fin_cases i <;> simp [branch,objective,ht]
    have hdet : pairDet (gradient a b p q x 0) (gradient a b p q x 1)=0 := by
      by_contra hn
      let v := (pairMatrix (gradient a b p q x 0) (gradient a b p q x 1))⁻¹.mulVec 1
      have hv := PlanarActiveGeometry.inverse_common_rate _ _ hn
      have hpair : ∀g∈subdifferential (objective a b p q) x,dot g v=1 :=
        PlanarNormalGeometry.two_branch_support_pairing hF hrep hg hact (by
          intro i
          fin_cases i
          · exact hv.1
          · exact hv.2)
      apply ((equal_rate_exists_iff_not_affineCritical hF x).mp ?_) hcrit
      refine ⟨-v,?_⟩
      intro g hg'
      calc
        dot g (-v) = -dot g v := by simp [dot]
        _ = -1 := congrArg Neg.neg (hpair g hg')
    have hd : deriv (profile a b p q) (x 0)=0 := by
      rw [actual_gradient_determinant hA hB (add_pos hp hq).ne'] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left (neg_ne_zero.mpr (add_pos hp hq).ne')
    have hu := profile_deriv_zero_implies_optimizer hA hB hca hcb hp hq hmin hunique (x 0) hd
    have hx : x=optimizer a b p q u := by simpa only [hu] using tie_point (add_pos hp hq).ne' x htie
    rw [hx]
    exact zero_mem_iff_global_minimum.mpr (optimizer_minimum hp hq hmin)
  · exact affineCorrectAt_of_hasFDerivAt hF
      (hasFDerivAt_coordinateGradient (two_branch_smooth_of_ne hrep (hg 0).differentiableAt
        (hg 1).differentiableAt htie))

end BfgsVerification.RidgeSupersession
