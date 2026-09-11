import BfgsVerification.RidgeProfiles

noncomputable section
open scoped Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification.RidgeSupersession
open ConvexSubdifferential HomogeneousPlanar

def gradient (a b : ℝ → ℝ) (p q : ℝ) (x : Vec 2) : Fin 2 → Vec 2 :=
  ![![deriv a (x 0),p],![deriv b (x 0),-q]]

theorem branch_C2 {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (p q : ℝ) (i : Fin 2) : ContDiff ℝ 2 (branch a b p q i) := by
  fin_cases i
  · change ContDiff ℝ 2 (fun x : Vec 2 => a (x 0)+p*x 1)
    fun_prop
  · change ContDiff ℝ 2 (fun x : Vec 2 => b (x 0)-q*x 1)
    fun_prop

theorem branch_hasGradient {a b : ℝ → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (p q : ℝ) (x : Vec 2) (i : Fin 2) :
    HasFDerivAt (branch a b p q i) (gradientFunctional (gradient a b p q x i)) x := by
  let e (j : Fin 2) : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have h0 := e 0 |>.hasFDerivAt (x:=x)
  have h1 := e 1 |>.hasFDerivAt (x:=x)
  have hA := (ha (x 0)).hasDerivAt.comp_hasFDerivAt x h0
  have hB := (hb (x 0)).hasDerivAt.comp_hasFDerivAt x h0
  fin_cases i
  · convert hA.add (h1.const_mul p) using 1
    ext v
    simp [gradient,branch,e,gradientFunctional_apply,dot,Fin.sum_univ_two]
  · convert hB.sub (h1.const_mul q) using 1
    ext v
    simp [gradient,branch,e,gradientFunctional_apply,dot,Fin.sum_univ_two]
    ring

theorem coordinateGradient_eq {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (p q : ℝ) (x : Vec 2) (i : Fin 2) :
    coordinateGradient (branch a b p q i) x=gradient a b p q x i :=
  AffineProjection.gradientFunctional_injective
    ((hasFDerivAt_coordinateGradient ((branch_C2 ha hb p q i).differentiable (by norm_num) x)).unique
      (branch_hasGradient (ha.differentiable (by norm_num)) (hb.differentiable (by norm_num)) p q x i))

theorem localFiniteMax (a b : ℝ → ℝ) (p q : ℝ) (x : Vec 2) :
    LocalFiniteMax (objective a b p q) (branch a b p q) x := by
  apply Eventually.of_forall
  intro z
  constructor
  · by_cases h : a (z 0)+p*z 1 ≤ b (z 0)-q*z 1
    · exact ⟨1,by simpa [branch,objective,max_eq_right h]⟩
    · exact ⟨0,by simpa [branch,objective,max_eq_left (le_of_not_ge h)]⟩
  · rintro v ⟨i,rfl⟩
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem gradients_affineIndependent {a b : ℝ → ℝ} {p q : ℝ} (hp : 0<p) (hq : 0<q)
    (x : Vec 2) : AffineIndependent ℝ (gradient a b p q x) := by
  apply affineIndependent_of_ne
  intro h
  have hv := congrArg (fun v : Vec 2 => v 1) h
  norm_num at hv
  linarith

theorem source_regular {a b : ℝ → ℝ}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    {p q : ℝ} (hp : 0<p) (hq : 0<q) (x : Vec 2)
    (hn : ¬AffineCriticalObjective.IsAffineCritical (objective a b p q) x) :
    ContDiffAt ℝ 2 (objective a b p q) x ∨
      PlanarCornerCharts.ConvexTwoBranchRegularAt (objective a b p q) x := by
  apply PlanarMaxRegular.regular_of_finite_max_independent
    (objective_convex hca hcb p q) isOpen_univ (mem_univ x)
    (fun i => ⟨branch_convex hca hcb p q i,(branch_C2 ha hb p q i).contDiffOn⟩)
    (localFiniteMax a b p q x) _ hn
  simpa only [coordinateGradient_eq ha hb] using gradients_affineIndependent (a:=a) (b:=b) hp hq x

theorem profile_hasDerivAt {a b : ℝ → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (p q u : ℝ) : HasDerivAt (profile a b p q)
      ((q*deriv a u+p*deriv b u)/(p+q)) u :=
  (((ha u).hasDerivAt.const_mul q).add ((hb u).hasDerivAt.const_mul p)).div_const (p+q)

theorem actual_gradient_determinant {a b : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) {p q : ℝ}
    (hpq : p+q≠0) (x : Vec 2) :
    pairDet (gradient a b p q x 0) (gradient a b p q x 1)=
      -(p+q)*deriv (profile a b p q) (x 0) := by
  rw [(profile_hasDerivAt ha hb p q (x 0)).deriv]
  norm_num [gradient,pairDet]
  field_simp
  ring

end BfgsVerification.RidgeSupersession
