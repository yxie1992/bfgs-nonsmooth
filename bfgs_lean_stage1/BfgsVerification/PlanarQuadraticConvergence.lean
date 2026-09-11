import BfgsVerification.PlanarQuadraticCoefficients
import BfgsVerification.PlanarQuadraticHessian
import BfgsVerification.PlanarMaxRegular

/-! C's exact objective-only 1/100 basin, derived from its literal coefficients. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification.PlanarQuadraticExample
open FixedNormal ConvexSubdifferential AffineCriticalObjective PlanarActiveGeometry

theorem gradient_continuous (i : Fin 3) : Continuous (gradient i) := by
  apply continuous_pi
  intro j
  change Continuous (fun x : Vec 2 => linearPart i j+∑ k, hessian i j k*x k)
  fun_prop

theorem coordinateGradient_eq (i : Fin 3) (x : Vec 2) : coordinateGradient (branch i) x=gradient i x :=
  AffineProjection.gradientFunctional_injective
    ((hasFDerivAt_coordinateGradient (branch_hasGradient i x).differentiableAt).unique (branch_hasGradient i x))

theorem affineCorrect_on_box {x : Vec 2} (hx : x∈box) : AffineCorrectAt objective x := by
  have hD := (denominator_pos_on_box hx).ne'
  have hc := local_affine_critical_correctness objective_convex (fun p i => gradient i p) x
    (localFiniteMax x) (Eventually.of_forall (fun p i => branch_hasGradient i p))
    (fun i => (gradient_continuous i).continuousAt) (gradient_affineIndependent hD)
    (coefficients x) (coefficients_pos_on_box hx) (coefficients_sum hD) (coefficients_zero hD)
  intro hcrit
  apply zero_mem_iff_global_minimum.mpr
  apply (mem_of_mem_nhds hc).2.1.mp
  exact (isAffineCritical_iff_coordinate_affineSpan objective x).mp hcrit

theorem regular_on_box {x : Vec 2} (hx : x∈box) (hn : ¬IsAffineCritical objective x) :
    ContDiffAt ℝ 2 objective x ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt objective x := by
  apply PlanarMaxRegular.regular_of_finite_max_independent objective_convex
    isOpen_univ (mem_univ x) (fun i => ⟨branch_convex i,(branch_contDiff i).contDiffOn⟩)
    (localFiniteMax x) _ hn
  simpa only [coordinateGradient_eq] using gradient_affineIndependent (denominator_pos_on_box hx).ne'

/-- Strong convexity forbids every nontrivial segment in every level boundary. -/
theorem strict_contours (level : ℝ) (x y : Vec 2)
    (hseg : segment ℝ x y⊆frontier {z | objective z≤level}) : x=y := by
  let mid : Vec 2 := (1/2 : ℝ) • x+(1/2 : ℝ) • y
  have hm : mid∈segment ℝ x y := ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  have he (z : Vec 2) (hz : z∈segment ℝ x y) : objective z=level :=
    frontier_le_subset_eq (convex_continuous objective_convex) continuous_const (hseg hz)
  have hx := he x (left_mem_segment ℝ x y)
  have hy := he y (right_mem_segment ℝ x y)
  have hmid := he mid hm
  have hs := objective_strongConvex.2 (mem_univ x) (mem_univ y)
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num : (1/2:ℝ)+1/2=1)
  have hsq : sqNorm mid=(sqNorm x+sqNorm y)/2-sqNorm (y-x)/4 := by
    dsimp [mid]
    convert sqNorm_convex_combination x y (1/2) using 1 <;> norm_num <;> ring
  change objective mid-(1/2)*sqNorm mid ≤
    (1/2)*(objective x-(1/2)*sqNorm x)+(1/2)*(objective y-(1/2)*sqNorm y) at hs
  rw [hx,hy,hmid,hsq] at hs
  have hz : sqNorm (y-x)=0 := le_antisymm (by linarith) (sqNorm_nonneg _)
  exact (sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hz)).symm

/-- The exact printed basin, independent of the initial SPD matrix and all
admissible accepted line-search choices. -/
theorem fullBFGS_explicit_basin (R : AdmissibleBFGSRun 2 objective)
    (hstart : objective (R.x 0)<1/100) :
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hv,_,_,hx⟩ := R.planar_convergence_on_sublevel 0 objective_minimum (1/100)
    (sublevel_compact _) hstart.le (fun level _ _ => strict_contours level)
    (fun p hp hn => regular_on_box (small_sublevel_mem_box hp) hn)
    (fun p hp => affineCorrect_on_box (small_sublevel_mem_box hp))
  refine ⟨by simpa only [objective_zero] using hv,hx ?_⟩
  intro x hx
  exact objective_unique_zero x (by simpa only [objective_zero] using hx)

end BfgsVerification.PlanarQuadraticExample
