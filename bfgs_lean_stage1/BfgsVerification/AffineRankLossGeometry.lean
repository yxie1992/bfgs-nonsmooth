import BfgsVerification.AffineCriticalGeometry
import BfgsVerification.QuadraticGaugeConvex

/-! Module A's literal rank-loss gradient geometry. Actual objective and
subdifferential bridges are developed separately, not assumed here. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Set Filter Matrix
namespace BfgsVerification
namespace AffineRankLoss

def objective (x : Vec 2) : ℝ := x 0 + (x 0)^2 + (x 1)^2 + |x 0*x 1|
def branch (i : Fin 2) (x : Vec 2) : ℝ :=
  x 0 + (x 0)^2 + (x 1)^2 + (if i=0 then 1 else -1)*(x 0*x 1)
def branchGradient (x : Vec 2) : Fin 2 → Vec 2 :=
  ![![1+2*x 0+x 1, 2*x 1+x 0], ![1+2*x 0-x 1, 2*x 1-x 0]]
def euclideanGradients (x : Vec 2) : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  fun i => euclideanVector (branchGradient x i)

theorem objective_eq_max (x : Vec 2) : objective x = max (branch 0 x) (branch 1 x) := by
  simp only [objective, branch, Fin.zero_eta, ↓reduceIte, Fin.isValue, one_mul]
  norm_num
  rw [abs_eq_max_neg, ← max_add_add_left]

theorem unique_minimum : objective ![-1/2,0] = -1/4 ∧
    (∀ x : Vec 2, -1/4 ≤ objective x) ∧
    (∀ x : Vec 2, objective x = -1/4 → x = ![-1/2,0]) := by
  refine ⟨by norm_num [objective], ?_, ?_⟩
  · intro x
    dsimp only [objective]
    nlinarith [sq_nonneg (x 0+1/2), sq_nonneg (x 1), abs_nonneg (x 0*x 1)]
  · intro x hx
    have h0 : x 0 = -1/2 := by
      dsimp only [objective] at hx
      nlinarith [sq_nonneg (x 0+1/2), sq_nonneg (x 1), abs_nonneg (x 0*x 1)]
    have h1 : x 1 = 0 := by
      dsimp only [objective] at hx
      nlinarith [sq_nonneg (x 0+1/2), sq_nonneg (x 1), abs_nonneg (x 0*x 1)]
    ext i
    fin_cases i <;> simp [h0,h1]

theorem branch_hasGradient (i : Fin 2) (x : Vec 2) :
    HasFDerivAt (branch i) (gradientFunctional (branchGradient x i)) x := by
  have h0 := (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hd := ((h0.add (h0.mul h0)).add (h1.mul h1)).add
    ((h0.mul h1).const_mul (if i=0 then 1 else -1))
  convert hd using 1
  · funext z
    simp only [branch, ContinuousLinearMap.proj_apply, pow_two]
  · ext v
    fin_cases i <;> simp [gradientFunctional_apply,branchGradient,dot,Fin.sum_univ_two] <;> ring

/-- Each actual branch has a global quadratic support with modulus one. -/
theorem branch_strong_support (i : Fin 2) (x z : Vec 2) :
    dot (branchGradient x i) (z-x) + sqNorm (z-x)/2 ≤ branch i z - branch i x := by
  fin_cases i <;> simp [branch,branchGradient,dot,sqNorm,Fin.sum_univ_two]
  · nlinarith [sq_nonneg ((z 0-x 0)+(z 1-x 1))]
  · nlinarith [sq_nonneg ((z 0-x 0)-(z 1-x 1))]

theorem branch_convex (i : Fin 2) : ConvexOn ℝ univ (branch i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  have hbEq : b = 1-a := by linarith
  have hid : a*branch i x+b*branch i z-branch i (a • x+b • z) =
      a*b*((x 0-z 0)^2+(x 1-z 1)^2+(if i=0 then 1 else -1)*((x 0-z 0)*(x 1-z 1))) := by
    rw [hbEq]
    simp only [branch, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : 0 ≤ (x 0-z 0)^2+(x 1-z 1)^2+
      (if i=0 then 1 else -1)*((x 0-z 0)*(x 1-z 1)) := by
    fin_cases i <;> norm_num
    · nlinarith [sq_nonneg ((x 0-z 0)+(x 1-z 1)),sq_nonneg (x 0-z 0),sq_nonneg (x 1-z 1)]
    · nlinarith [sq_nonneg ((x 0-z 0)-(x 1-z 1)),sq_nonneg (x 0-z 0),sq_nonneg (x 1-z 1)]
  have hnon := mul_nonneg (mul_nonneg ha hb) hq
  change branch i (a • x+b • z) ≤ a*branch i x+b*branch i z
  linarith

theorem objective_convex : ConvexOn ℝ univ objective := by
  have he : objective = fun x => max (branch 0 x) (branch 1 x) := funext objective_eq_max
  rw [he]
  exact (branch_convex 0).sup (branch_convex 1)

theorem objective_continuous : Continuous objective := convex_continuous objective_convex

theorem vertical_affine_candidate_mem {t : ℝ} (ht : t ≠ 0) :
    euclideanVector ![0,2*t] ∈ affineSpan ℝ (range (euclideanGradients ![0,t])) := by
  have hm := AffineMap.lineMap_mem
    ((1+t)/(2*t))
    (mem_affineSpan ℝ (mem_range_self (f := euclideanGradients ![0,t]) 0))
    (mem_affineSpan ℝ (mem_range_self (f := euclideanGradients ![0,t]) 1))
  have he : AffineMap.lineMap (euclideanGradients ![0,t] 0) (euclideanGradients ![0,t] 1)
      ((1+t)/(2*t)) = euclideanVector ![0,2*t] := by
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply_module, euclideanGradients, branchGradient, euclideanVector]
    · field_simp
      <;> ring
    · field_simp
      <;> ring
  rwa [he] at hm

theorem vertical_closest {t : ℝ} (ht : t ≠ 0) :
    AffineCriticalGeometry.closestAffinePoint (euclideanGradients ![0,t]) 0 =
      euclideanVector ![0,2*t] := by
  symm
  apply AffineCriticalGeometry.eq_closest_of_pairings _ _ _ (vertical_affine_candidate_mem ht)
  intro j
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector ![0,2*t])
  rw [hn]
  fin_cases j <;> simp [EuclideanSpace.inner_eq_star_dotProduct, euclideanGradients,
    branchGradient, euclideanVector, dotProduct, sqNorm, Fin.sum_univ_succ] <;> ring

theorem vertical_affine_distance {t : ℝ} (ht : t ≠ 0) :
    Metric.infDist (0 : EuclideanSpace ℝ (Fin 2))
      (affineSpan ℝ (range (euclideanGradients ![0,t])) : Set _) = 2*|t| := by
  rw [AffineCriticalGeometry.infDist_affineSpan_eq_norm_closest _ 0, vertical_closest ht]
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector ![0,2*t])
  simp only [sqNorm, Fin.sum_univ_succ] at hn
  norm_num [euclideanVector] at hn
  change ‖euclideanVector ![0,2*t]‖^2 = (2*t)^2 at hn
  nlinarith [sq_abs t, abs_nonneg t, norm_nonneg (euclideanVector ![0,2*t])]

theorem horizontal_closest (u : ℝ) :
    AffineCriticalGeometry.closestAffinePoint (euclideanGradients ![u,0]) 0 =
      euclideanVector ![1+2*u,0] := by
  symm
  apply AffineCriticalGeometry.eq_closest_of_pairings
  · have hm := AffineMap.lineMap_mem (1/2 : ℝ)
      (mem_affineSpan ℝ (mem_range_self (f := euclideanGradients ![u,0]) 0))
      (mem_affineSpan ℝ (mem_range_self (f := euclideanGradients ![u,0]) 1))
    have he : AffineMap.lineMap (euclideanGradients ![u,0] 0) (euclideanGradients ![u,0] 1)
        (1/2 : ℝ) = euclideanVector ![1+2*u,0] := by
      ext i
      fin_cases i <;> simp [AffineMap.lineMap_apply_module,euclideanGradients,branchGradient,euclideanVector] <;> ring
    rwa [he] at hm
  · intro j
    have hn := FrameNorms.euclidean_norm_sq (euclideanVector ![1+2*u,0])
    rw [hn]
    fin_cases j <;> simp [EuclideanSpace.inner_eq_star_dotProduct,euclideanGradients,
      branchGradient,euclideanVector,dotProduct,sqNorm,Fin.sum_univ_succ] <;> ring

theorem horizontal_affine_distance (u : ℝ) :
    Metric.infDist (0 : EuclideanSpace ℝ (Fin 2))
      (affineSpan ℝ (range (euclideanGradients ![u,0])) : Set _) = |1+2*u| := by
  rw [AffineCriticalGeometry.infDist_affineSpan_eq_norm_closest _ 0,horizontal_closest]
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector ![1+2*u,0])
  simp only [sqNorm,Fin.sum_univ_succ] at hn
  norm_num [euclideanVector] at hn
  change ‖euclideanVector ![1+2*u,0]‖^2 = (1+2*u)^2 at hn
  nlinarith [sq_abs (1+2*u),abs_nonneg (1+2*u),norm_nonneg (euclideanVector ![1+2*u,0])]

theorem origin_affine_distance :
    Metric.infDist (0 : EuclideanSpace ℝ (Fin 2))
      (affineSpan ℝ (range (euclideanGradients 0)) : Set _) = 1 := by
  simpa using horizontal_affine_distance 0

end AffineRankLoss
end BfgsVerification
