import BfgsVerification.AffineRankLossGeometry
import BfgsVerification.AffineCriticalObjective
import BfgsVerification.FiniteMaxSubdifferential

/-! Actual convex-subdifferential rank loss in Module A's literal example. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Set Filter Matrix
namespace BfgsVerification
namespace AffineRankLoss
open ConvexSubdifferential AffineCriticalObjective

def affineDistance (x : Vec 2) : ℝ := Metric.infDist (0 : EuclideanSpace ℝ (Fin 2))
  (affineSpan ℝ (range (subgradientFamily objective x)) : Set _)

theorem local_representation (x : Vec 2) : LocalFiniteMax objective branch x := by
  apply Eventually.of_forall
  intro z
  rw [objective_eq_max]
  constructor
  · by_cases h : branch 0 z ≤ branch 1 z
    · exact ⟨1, (max_eq_right h).symm⟩
    · exact ⟨0, (max_eq_left (le_of_not_ge h)).symm⟩
  · rintro a ⟨i,rfl⟩
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem all_active_of_product_zero (x : Vec 2) (hx : x 0*x 1 = 0) :
    activeIndices objective branch x = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  apply mem_activeIndices.mpr
  simp [objective,branch,hx]

theorem axis_subdifferential (x : Vec 2) (hx : x 0*x 1 = 0) :
    subdifferential objective x = convexHull ℝ (range (branchGradient x)) := by
  have he := subdifferential_eq_active_convexHull objective_convex
    (local_representation x) (fun i => branch_hasGradient i x)
  simpa only [all_active_of_product_zero x hx,Finset.coe_univ,image_univ] using he

theorem axis_affine_span (x : Vec 2) (hx : x 0*x 1 = 0) :
    affineSpan ℝ (range (subgradientFamily objective x)) =
      affineSpan ℝ (range (euclideanGradients x)) := by
  have he := affineSpan_subgradientFamily_of_convexHull x _ (axis_subdifferential x hx)
  simpa only [← range_comp] using he

theorem actual_vertical_distance {t : ℝ} (ht : t ≠ 0) : affineDistance ![0,t] = 2*|t| := by
  rw [affineDistance,axis_affine_span _ (by simp)]
  exact vertical_affine_distance ht

theorem actual_horizontal_distance (u : ℝ) : affineDistance ![u,0] = |1+2*u| := by
  rw [affineDistance,axis_affine_span _ (by simp)]
  exact horizontal_affine_distance u

theorem actual_origin_distance : affineDistance 0 = 1 := by
  simpa using actual_horizontal_distance 0

theorem hasGradient_of_positive_product {x : Vec 2} (hx : 0 < x 0*x 1) :
    HasFDerivAt objective (gradientFunctional (branchGradient x 0)) x := by
  have he : objective =ᶠ[𝓝 x] branch 0 := by
    have hc : Continuous (fun z : Vec 2 => z 0*z 1) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hx)] with z hz
    simp [objective,branch,abs_of_pos hz]
  exact (branch_hasGradient 0 x).congr_of_eventuallyEq he

theorem hasGradient_of_negative_product {x : Vec 2} (hx : x 0*x 1 < 0) :
    HasFDerivAt objective (gradientFunctional (branchGradient x 1)) x := by
  have he : objective =ᶠ[𝓝 x] branch 1 := by
    have hc : Continuous (fun z : Vec 2 => z 0*z 1) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (eventually_lt_nhds hx)] with z hz
    simp [objective,branch,abs_of_neg hz]
  exact (branch_hasGradient 1 x).congr_of_eventuallyEq he

/-- Pointwise affine correctness holds globally for the actual objective. -/
theorem globally_affine_correct (x : Vec 2) : AffineCorrectAt objective x := by
  rcases lt_trichotomy (x 0*x 1) 0 with hn | hz | hp
  · exact affineCorrectAt_of_hasFDerivAt objective_convex (hasGradient_of_negative_product hn)
  · intro hc
    have hdist : affineDistance x = 0 := by
      exact Metric.infDist_zero_of_mem hc
    rcases mul_eq_zero.mp hz with hx | hy
    · have he : x = ![0,x 1] := by ext i; fin_cases i <;> simp [hx]
      by_cases hv : x 1 = 0
      · have he0 : x = 0 := by rw [he,hv]; ext i; fin_cases i <;> simp
        rw [he0,actual_origin_distance] at hdist
        norm_num at hdist
      · rw [he,actual_vertical_distance hv] at hdist
        have : |x 1| = 0 := by linarith
        exact (hv (abs_eq_zero.mp this)).elim
    · have he : x = ![x 0,0] := by ext i; fin_cases i <;> simp [hy]
      rw [he,actual_horizontal_distance] at hdist
      have h0 : x 0 = -1/2 := by have := abs_eq_zero.mp hdist; linarith
      have he0 : x = ![-1/2,0] := by rw [he,h0]
      apply zero_mem_iff_global_minimum.mpr
      rw [he0,unique_minimum.1]
      exact unique_minimum.2.1
  · exact affineCorrectAt_of_hasFDerivAt objective_convex (hasGradient_of_positive_product hp)

/-- The actual affine distance tends to zero on the punctured vertical axis,
although its value at the limiting point is one. -/
theorem vertical_distance_tendsto_zero :
    Tendsto (fun t : ℝ => affineDistance ![0,t]) (𝓝[≠] 0) (𝓝 0) := by
  have he : (fun t : ℝ => affineDistance ![0,t]) =ᶠ[𝓝[≠] 0] (fun t => 2*|t|) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact actual_vertical_distance ht
  have hc : Continuous (fun t : ℝ => 2*|t|) := by fun_prop
  apply Tendsto.congr' he.symm
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem vertical_positive_gap_limit :
    Tendsto (fun t : ℝ => objective ![0,t]-objective ![-1/2,0]) (𝓝[≠] 0) (𝓝 (1/4)) := by
  have he : (fun t : ℝ => objective ![0,t]-objective ![-1/2,0]) = fun t => t^2+1/4 := by
    funext t
    norm_num [objective]
  rw [he]
  have hc : Continuous (fun t : ℝ => t^2+1/4) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

end AffineRankLoss
end BfgsVerification
