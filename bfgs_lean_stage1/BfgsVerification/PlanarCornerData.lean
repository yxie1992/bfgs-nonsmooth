import BfgsVerification.PlanarCornerFiniteness
import BfgsVerification.PlanarSectorCutoffs

/-! Actual objective support and velocity data on the inverse-function corner
curves. Gradient curves and their common rate are derived from the branches. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarCornerCharts
open HomogeneousPlanar ConvexSubdifferential

theorem coordinateGradient_continuousAt_of_contDiffAt {f : Vec 2 → ℝ} {x : Vec 2}
    (hf : ContDiffAt ℝ 2 f x) : ContinuousAt (coordinateGradient f) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  apply continuousAt_pi.mpr
  intro i
  exact (hd.clm_apply contDiffAt_const).continuousAt

/-- All moving corner data used to form the normal sectors come from the
actual local branches of the actual convex objective. -/
theorem exists_regular_corner_motion {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {x : Vec 2} (hx : TwoBranchRegularAt F x) :
    ∃ f : Fin 2 → Vec 2 → ℝ, ∃ p : ℝ → Vec 2,
      p (F x)=x ∧ ContDiffAt ℝ 2 p (F x) ∧ ContDiffAt ℝ 1 (deriv p) (F x) ∧
      (∀ i, ContinuousAt (fun t => coordinateGradient (f i) (p t)) (F x)) ∧
      (∀ᶠ t in 𝓝 (F x), F (p t)=t ∧ ∀ i,
        Homogeneous.Supports F (p t) (coordinateGradient (f i) (p t)) ∧
        dot (coordinateGradient (f i) (p t)) (deriv p t)=1) ∧
      (∀ᶠ z in 𝓝 x, ¬DifferentiableAt ℝ F z → z=p (F z)) := by
  classical
  obtain ⟨f,a,b,hrep,hC,h0,h1,hd,hf0,hf1⟩ := hx
  obtain ⟨p,hp,hpC,hlevel,hinv⟩ := exists_corner_chart hC h0 h1 hd hf0 hf1
  have hpcont : Tendsto p (𝓝 (F x)) (𝓝 x) := by simpa only [ContinuousAt,hp] using hpC.continuousAt
  have hbranch : ∀ᶠ t in 𝓝 (F x), ∀ i, ContDiffAt ℝ 2 (f i) (p t) := by
    apply eventually_all.mpr
    intro i
    exact hpcont.eventually ((hC i).eventually (by norm_num))
  refine ⟨f,p,hp,hpC,curve_velocity_contDiffAt hpC,?_,?_,?_⟩
  · intro i
    change Tendsto _ _ (𝓝 (coordinateGradient (f i) (p (F x))))
    rw [hp]
    exact Filter.Tendsto.comp (coordinateGradient_continuousAt_of_contDiffAt (hC i)) hpcont
  · filter_upwards [hpcont.eventually hrep.eventually,hbranch,
      hpC.eventually (by norm_num),hlevel,hlevel.eventually_nhds] with t htRep htBranch htP htLevel htNear
    have hFt : F (p t)=t := by
      have hm := (local_pair_eq_max htRep).self_of_nhds
      simpa only [htLevel,max_self] using hm
    refine ⟨hFt,?_⟩
    have hf (i : Fin 2) := hasFDerivAt_coordinateGradient ((htBranch i).differentiableAt (by norm_num))
    have hvel := curve_velocity_pairing ((htP.differentiableAt (by norm_num)).hasDerivAt) hf htNear
    intro i
    refine ⟨active_gradient_supports hF htRep hf ?_,hvel i⟩
    exact mem_activeIndices.mpr ((htLevel i).trans hFt.symm)
  · filter_upwards [hrep.eventually,local_pair_eq_max hrep,hinv,
      (hC 0).eventually (by norm_num),(hC 1).eventually (by norm_num)] with z hzRep hzMax hzInv hz0 hz1
    intro hn
    have heq : f 0 z=f 1 z := by
      by_contra he
      exact hn (two_branch_smooth_of_ne hzRep (hz0.differentiableAt (by norm_num))
        (hz1.differentiableAt (by norm_num)) he)
    have hi : ∀ i, f i z=f 0 z := by intro i; fin_cases i; rfl; exact heq.symm
    have hvalue : F z=f 0 z := by simpa only [← heq,max_self] using hzMax
    simpa only [hvalue] using hzInv hi

end PlanarCornerCharts
end BfgsVerification
