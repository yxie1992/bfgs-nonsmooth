import BfgsVerification.AlgebraicSeedCoercive

noncomputable section
namespace BfgsVerification.DLiteralIdentities
open SeedOrbit SeedCycle AlgebraicSeed
set_option maxHeartbeats 1000000

theorem beta_quarter_iff {c d : ℝ} (hU : U c d≠0) (hV : V c d≠0)
    (hA : U c d+129≠0) :
    beta c d=1/4 ↔ 264192*R c d*K c d-U c d*V c d*(U c d+129)=0 := by
  constructor
  · intro h
    unfold beta at h
    field_simp [hU,hV,hA] at h
    nlinarith [h]
  · exact beta_quarter hU hV hA

theorem gamma_sixteenth_iff {c d : ℝ} (hU : U c d≠0) (hR : R c d≠0)
    (hY : Y c d≠0) :
    gamma c d=1/16 ↔ 16*V c d*T c d*K c d-R c d*U c d*Y c d=0 := by
  constructor
  · intro h
    unfold gamma at h
    field_simp [hU,hR,hY] at h
    nlinarith [h]
  · exact gamma_sixteenth hU hR hY

theorem original_box_polynomial_iff {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    P x=0 ↔ beta (x 0) (x 1)=1/4 ∧ gamma (x 0) (x 1)=1/16 := by
  obtain ⟨hU,hV,hR,_,_,hY,hA,_,_⟩ := box_denominators_and_ratio hx
  rw [beta_quarter_iff hU.ne' hV.ne' hA.ne',gamma_sixteenth_iff hU.ne' hR.ne' hY.ne']
  change (![_,_] : Vec 2)=0 ↔ _
  simp only [funext_iff,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply,
    Matrix.cons_val_fin_one]

theorem gradient_support_zero (j : Fin 3) :
    gradient seedC seedD j ∈ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 := by
  intro z
  rw [sub_zero,objective_zero,sub_zero]
  simpa only [MaxAffine.Family.branch,family,Pi.zero_apply,add_zero] using (family seedC seedD).branch_le j z

theorem zero_not_mem_gradient_hull :
    (0 : Vec 2) ∉ convexHull ℝ (Set.range (gradient seedC seedD)) := by
  intro h
  apply limit_not_stationary
  exact convexHull_min (by rintro _ ⟨j,rfl⟩; exact gradient_support_zero j)
    (ConvexSubdifferential.convex_subdifferential (objective seedC seedD) 0) h

theorem coercive_exact_affine_combination (x : Vec 2) :
    (8/17 : ℝ)*coerciveFamily.branch 0 x+(8/17 : ℝ)*coerciveFamily.branch 1 x+
      (1/17 : ℝ)*coerciveFamily.branch 3 x = -1 := by
  rw [coercive_branch_last]
  change (8/17 : ℝ)*coerciveFamily.branch (0 : Fin 3).castSucc x+
    (8/17 : ℝ)*coerciveFamily.branch (1 : Fin 3).castSucc x+(1/17 : ℝ)*(x 1-17) = -1
  rw [coercive_branch_old,coercive_branch_old]
  norm_num [SeedOrbit.gradient,g0,g1,dot,Fin.sum_univ_two]
  ring

theorem coercive_weights_convex :
    (0 : ℝ)<8/17 ∧ (0 : ℝ)<1/17 ∧ (8/17 : ℝ)+8/17+1/17=1 := by norm_num

end BfgsVerification.DLiteralIdentities
