import BfgsVerification.LEmbeddingGradientBounds
import BfgsVerification.LEmbeddingLocal

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LEmbedding

theorem objective_isGreatest (x : Vec 2) : IsGreatest (range (fun i => branch i x)) (objective x) := by
  refine ⟨?_,?_⟩
  · obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : Fin 4 => branch i x)
    exact ⟨i,hi.symm.trans (objective_eq_max x).symm⟩
  · rintro v ⟨i,rfl⟩
    exact branch_le i x

theorem localFiniteMax (x : Vec 2) : ConvexSubdifferential.LocalFiniteMax objective branch x :=
  Eventually.of_forall objective_isGreatest

theorem local_upper_taylor {x g : Vec 2} (hg : HasFDerivAt objective (gradientFunctional g) x) :
    ∀ᶠ z in 𝓝 x,objective z≤objective x+dot g (z-x)+256*sqNorm (z-x) := by
  convert FiniteMaxHessian.finiteMax_local_upper_taylor (L := 512) (by norm_num) (localFiniteMax x)
    hg branch_hasGradient branch_gradient_bound using 1 <;> norm_num

theorem actual_hessian_bounds {x : Vec 2}
    (hfirst : ∀ᶠ z in 𝓝 x,DifferentiableAt ℝ objective z)
    (hsecond : DifferentiableAt ℝ (fderiv ℝ objective) x) :
    (RadialHessian.matrix objective x).IsSymm ∧ ∀v,
      mu*sqNorm v≤dot v ((RadialHessian.matrix objective x).mulVec v) ∧
      dot v ((RadialHessian.matrix objective x).mulVec v)≤512*sqNorm v :=
  FiniteMaxHessian.finiteMax_actual_hessian_bounds (by norm_num) objective_convex objective_strongConvex
    (localFiniteMax x) branch_hasGradient branch_gradient_bound hfirst hsecond

theorem branch_old_actual_hessian_bounds (i : Fin 3) {x : Vec 2}
    (hsecond : DifferentiableAt ℝ (fderiv ℝ (branch i.castSucc)) x) :
    (RadialHessian.matrix (branch i.castSucc) x).IsSymm ∧ ∀v,
      mu*sqNorm v≤dot v ((RadialHessian.matrix (branch i.castSucc) x).mulVec v) ∧
      dot v ((RadialHessian.matrix (branch i.castSucc) x).mulVec v)≤gradientBound i*sqNorm v := by
  have hr : ConvexSubdifferential.LocalFiniteMax (branch i.castSucc)
      (fun _ : Fin 1 => branch i.castSucc) x := Eventually.of_forall (fun z =>
    ⟨⟨0,rfl⟩,by rintro v ⟨j,rfl⟩; exact le_refl _⟩)
  exact FiniteMaxHessian.finiteMax_actual_hessian_bounds (gradientBound_pos i).le
    (branch_convex i.castSucc) (branch_strongConvex i.castSucc) hr
    (fun _ z => branch_hasGradient i.castSucc z) (fun _ z w => branch_old_gradient_bound i z w)
    (Eventually.of_forall (fun z => (branch_hasGradient i.castSucc z).differentiableAt)) hsecond

theorem branch_zero (i : Fin 4) : branch i 0=0 := by
  simp [branch,LQuadraticSeed.quadratic,sqNorm,residualBranch_zero]

theorem objective_nested_max (x : Vec 2) :
    objective x=max (max (branch 0 x) (branch 1 x)) (max (branch 2 x) (branch 3 x)) := by
  apply le_antisymm
  · apply objective_le
    intro i
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact max_le (max_le (branch_le 0 x) (branch_le 1 x)) (max_le (branch_le 2 x) (branch_le 3 x))

theorem branch_ray_hasDerivAt_zero (i : Fin 4) (h : Vec 2) :
    HasDerivAt (fun t : ℝ => branch i (t • h)) (dot (branchGradient i 0) h) 0 := by
  have hd := (branch_hasGradient i (0 : Vec 2)).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const h) (by simp)
  simpa only [Function.comp_def,gradientFunctional_apply,id_eq,one_smul] using hd

theorem objective_directional_derivative_zero (h : Vec 2) :
    Tendsto (fun t : ℝ => (objective (t • h)-objective 0)/t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1))) := by
  have hold (i : Fin 3) : Tendsto (fun t : ℝ => branch i.castSucc (t • h)/t) (𝓝[>] 0) (𝓝 0) := by
    have hh := (branch_ray_hasDerivAt_zero i.castSucc h).tendsto_slope_zero_right
    simpa only [branchGradient_zero,dot,Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero,
      zero_add,zero_smul,branch_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh
  have hlast : Tendsto (fun t : ℝ => branch 3 (t • h)/t) (𝓝[>] 0) (𝓝 (h 1)) := by
    have hh := (branch_ray_hasDerivAt_zero 3 h).tendsto_slope_zero_right
    have he : branchGradient 3 (0 : Vec 2)=![0,1] := by
      change mu • (0 : Vec 2)+![0,1]=![0,1]
      simp
    simpa only [he,dot,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      zero_mul,one_mul,zero_add,zero_smul,branch_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh
  have hm := ((hold 0).max (hold 1)).max ((hold 2).max hlast)
  simp only [max_self] at hm
  rw [max_eq_right (le_max_left (0 : ℝ) (h 1))] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [objective_zero,sub_zero,objective_nested_max]
  change max (max (branch 0 (t • h)/t) (branch 1 (t • h)/t))
    (max (branch 2 (t • h)/t) (branch 3 (t • h)/t))=_
  rw [max_div_div_right ht.le,max_div_div_right ht.le,max_div_div_right ht.le]

theorem center_nonstationary (n : ℕ) :
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential objective (copyCenter n) := by
  intro hh
  have hm := ConvexSubdifferential.zero_mem_iff_global_minimum.mp hh (0 : Vec 2)
  rw [objective_zero] at hm
  linarith [center_value_pos n]

end BfgsVerification.LEmbedding
