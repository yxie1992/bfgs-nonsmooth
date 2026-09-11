import BfgsVerification.PlanarBranchGeometry

/-! Uniform control by the actual two gradient rows follows from their
continuity and the genuine nonzero principal determinant at the corner. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarCrossing
open HomogeneousPlanar PlanarCornerCharts

theorem matrixCLM_continuous : Continuous (AffineProjection.matrixCLM : Mat 2 → (Vec 2 →L[ℝ] Vec 2)) := by
  let L : Mat 2 →ₗ[ℝ] (Vec 2 →L[ℝ] Vec 2) := {
    toFun := AffineProjection.matrixCLM
    map_add' := by intro A B; ext v i; simp [AffineProjection.matrixCLM_apply,Matrix.add_mulVec]
    map_smul' := by intro r A; ext v i; simp [AffineProjection.matrixCLM_apply,Matrix.smul_mulVec_assoc] }
  exact L.continuous_of_finiteDimensional

theorem pairMatrix_continuous {a b : Vec 2 → Vec 2} {x : Vec 2}
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) :
    ContinuousAt (fun z => pairMatrix (a z) (b z)) x := by
  apply continuousAt_pi.mpr
  intro i
  by_cases hi : i=0
  · simpa only [pairMatrix,hi,if_true] using ha
  · simpa only [pairMatrix,hi,if_false] using hb

theorem eventually_actual_pair_control {a b : Vec 2 → Vec 2} {x : Vec 2}
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hd : pairDet (a x) (b x)≠0) :
    ∃ A : ℝ, 0<A ∧ ∀ᶠ z in 𝓝 x, pairDet (a z) (b z)≠0 ∧
      ∀ s : Vec 2, ‖s‖≤A*(|dot (a z) s|+|dot (b z) s|) := by
  have hP := pairMatrix_continuous ha hb
  have hdet : (pairMatrix (a x) (b x)).det≠0 := by rwa [pairMatrix_det]
  have hi : ContinuousAt Ring.inverse (pairMatrix (a x) (b x)).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hmi : ContinuousAt (fun z : Vec 2 => (pairMatrix (a z) (b z))⁻¹) x :=
    (continuousAt_matrix_inv _ hi).comp (f := fun z : Vec 2 => pairMatrix (a z) (b z)) hP
  have hc : ContinuousAt (fun z : Vec 2 => AffineProjection.matrixCLM (pairMatrix (a z) (b z))⁻¹) x :=
    matrixCLM_continuous.continuousAt.comp (f := fun z : Vec 2 => (pairMatrix (a z) (b z))⁻¹) hmi
  let A : ℝ := ‖AffineProjection.matrixCLM (pairMatrix (a x) (b x))⁻¹‖+1
  have hA : 0<A := by dsimp [A]; positivity
  have hn : ∀ᶠ z in 𝓝 x, ‖AffineProjection.matrixCLM (pairMatrix (a z) (b z))⁻¹‖<A :=
    hc.norm.eventually (gt_mem_nhds (by dsimp [A]; linarith))
  have hnd : ∀ᶠ z in 𝓝 x, (pairMatrix (a z) (b z)).det≠0 :=
    ((continuous_id.matrix_det : Continuous (fun M : Mat 2 => M.det)).continuousAt.comp
      (f := fun z : Vec 2 => pairMatrix (a z) (b z)) hP).eventually_ne hdet
  refine ⟨A,hA,?_⟩
  filter_upwards [hn,hnd] with z hz hzd
  rw [pairMatrix_det] at hzd
  exact ⟨hzd,fun s => (pair_inverse_bound _ _ _ hzd).trans
    (mul_le_mul_of_nonneg_right hz.le (add_nonneg (abs_nonneg _) (abs_nonneg _)))⟩

/-- Actual C² branch data discharge the local pair-control hypothesis. -/
theorem convexCornerChart_eventually_pair_control {F : Vec 2 → ℝ} {x : Vec 2}
    (c : ConvexCornerChart F x) :
    ∃ A : ℝ, 0<A ∧ ∀ᶠ z in 𝓝 x, ∀ s : Vec 2,
      ‖s‖≤A*(|dot (coordinateGradient (c.branches 0) z) s|+
        |dot (coordinateGradient (c.branches 1) z) s|) := by
  have hg (i : Fin 2) : ContinuousAt (coordinateGradient (c.branches i)) x := by
    have hC : ContDiffAt ℝ 1 (fderiv ℝ (c.branches i)) x :=
      (c.branchesC2 i).fderiv_right (by norm_num)
    apply continuousAt_pi.mpr
    intro j
    exact (hC.clm_apply contDiffAt_const).continuousAt
  obtain ⟨A,hA,hb⟩ := eventually_actual_pair_control (hg 0) (hg 1) c.independent
  exact ⟨A,hA,hb.mono (fun _ h => h.2)⟩

end PlanarCrossing
end BfgsVerification
