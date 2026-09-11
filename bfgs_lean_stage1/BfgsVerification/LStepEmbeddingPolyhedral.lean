import BfgsVerification.LStepEmbeddingObjective
import BfgsVerification.AffineQuadraticGerm

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LStepEmbedding
open LEmbedding ConvexSubdifferential

theorem residual_local_representation (x : Vec 2) : LocalFiniteMax residual residualBranch x := by
  apply Eventually.of_forall
  intro z
  constructor
  · obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      Finset.univ_nonempty (fun i => residualBranch i z)
    exact ⟨i,hi.symm⟩
  · rintro _ ⟨i,rfl⟩
    exact residualBranch_le i z

theorem slope_pair_joint_kernel {x : Vec 2}
    (h0 : dot (slope 0) x=0) (h1 : dot (slope 1) x=0) : x=0 := by
  rw [slope_first] at h0
  rw [slope_second] at h1
  norm_num only [dot,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  ext i
  fin_cases i
  · change x 0=0
    linarith
  · change x 1=0
    linarith

theorem residual_positive_of_ne_zero {x : Vec 2} (hx : x ≠ 0) : 0<residual x := by
  have h : dot (slope 0) x≠0 ∨ dot (slope 1) x≠0 := by
    by_contra hn
    push_neg at hn
    exact hx (slope_pair_joint_kernel hn.1 hn.2)
  rcases h with h | h
  · exact (LScalarStep.phi_positive_of_ne_zero (parameter_bounds 0).1.le (parameter_bounds 0).2.le h).trans_le
      (residualBranch_le 0 x)
  · exact (LScalarStep.phi_positive_of_ne_zero (parameter_bounds 1).1.le (parameter_bounds 1).2.le h).trans_le
      (residualBranch_le 1 x)

theorem active_scalar_argument_ne_zero {x : Vec 2} (hx : x≠0) (i : Fin 3)
    (hi : i.castSucc ∈ activeIndices residual residualBranch x) : dot (slope i) x≠0 := by
  intro he
  have hv := mem_activeIndices.mp hi
  rw [residualBranch_old,he,LScalarStep.phi_zero (parameter_bounds i).1.le (parameter_bounds i).2.le] at hv
  exact (residual_positive_of_ne_zero hx).ne hv

theorem ridge_binary_affine {x : Vec 2} (i : Fin 3) (hx : dot (slope i) x≠0) :
    FiniteAffineLocal.BinaryAffineGerm (residualBranch i.castSucc) x := by
  obtain ⟨a,c,A,C,he⟩ := LScalarStep.phi_binary_affine_of_ne_zero
    (parameter_bounds i).1.le (parameter_bounds i).2.le hx
  refine ⟨a • gradientFunctional (slope i),A • gradientFunctional (slope i),c,C,?_⟩
  have hev := he.comp_tendsto (gradientFunctional (slope i)).continuous.continuousAt
  filter_upwards [hev] with z hz
  simpa only [residualBranch_old,ContinuousLinearMap.smul_apply,gradientFunctional_apply,smul_eq_mul] using hz

theorem active_branch_binary_affine {x : Vec 2} (hx : x≠0) (i : Fin 4)
    (hi : i ∈ activeIndices residual residualBranch x) :
    FiniteAffineLocal.BinaryAffineGerm (residualBranch i) x := by
  fin_cases i
  · exact ridge_binary_affine 0 (active_scalar_argument_ne_zero hx 0 hi)
  · exact ridge_binary_affine 1 (active_scalar_argument_ne_zero hx 1 hi)
  · exact ridge_binary_affine 2 (active_scalar_argument_ne_zero hx 2 hi)
  · apply FiniteAffineLocal.AffineGerm.binary
    exact ⟨ContinuousLinearMap.proj (1 : Fin 2),0,Eventually.of_forall (fun z => by simp [residualBranch])⟩

theorem residual_polyhedral_of_ne_zero {x : Vec 2} (hx : x≠0) :
    FiniteAffineLocal.PolyhedralGerm residual x := by
  have hr := localFiniteMax_restrict_active
    (convex_continuous residual_convex).continuousAt
    (fun i => (convex_continuous (residualBranch_convex i)).continuousAt)
    (residual_local_representation x)
  apply FiniteAffineLocal.polyhedral_of_binary_branches hr
  intro i
  apply active_branch_binary_affine hx
  have hm : activeIndexMap residual residualBranch x i ∈ range (activeIndexMap residual residualBranch x) :=
    mem_range_self i
  rw [range_activeIndexMap] at hm
  exact hm

theorem objective_not_differentiable_zero : ¬DifferentiableAt ℝ objective (0 : Vec 2) := by
  intro hd
  have hm : IsLocalMin objective (0 : Vec 2) := by
    apply Eventually.of_forall
    intro z
    rw [objective_zero]
    exact objective_nonnegative z
  have hm' : IsLocalMin (fun z => objective z-z 1) (0 : Vec 2) := by
    apply Eventually.of_forall
    intro z
    change objective 0-0≤objective z-z 1
    rw [objective_zero,sub_self]
    have hl := residualBranch_le 3 z
    have hq : 0≤LQuadraticSeed.quadratic mu z := by
      exact mul_nonneg (div_nonneg mu_pos.le (by norm_num)) (sqNorm_nonneg z)
    change z 1≤residual z at hl
    dsimp [objective]
    linarith
  have h0 := hm.hasFDerivAt_eq_zero hd.hasFDerivAt
  have h1 := hm'.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub
    (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt)
  rw [h0,zero_sub] at h1
  have hv := DFunLike.congr_fun h1 (Pi.single (1 : Fin 2) 1)
  norm_num at hv

theorem residual_affine_at_differentiable {x : Vec 2} (hd : DifferentiableAt ℝ objective x) :
    FiniteAffineLocal.AffineGerm residual x := by
  have hx : x≠0 := by intro he; subst x; exact objective_not_differentiable_zero hd
  have hp : DifferentiableAt ℝ residual x := by
    convert hd.sub (LQuadraticSeed.quadratic_hasGradient mu x).differentiableAt using 1
    funext z
    dsimp [objective]
    ring
  exact FiniteAffineLocal.affine_of_differentiable (residual_polyhedral_of_ne_zero hx) hp

theorem objective_actual_hessian {x : Vec 2} (hd : DifferentiableAt ℝ objective x) :
    HasFDerivAt (fderiv ℝ objective) (mu • LQuadraticSeed.pairingMap) x ∧
    RadialHessian.matrix objective x=mu • (1 : Mat 2) :=
  FiniteAffineLocal.hessian_of_affine_residual mu (residual_affine_at_differentiable hd)

end BfgsVerification.LStepEmbedding
