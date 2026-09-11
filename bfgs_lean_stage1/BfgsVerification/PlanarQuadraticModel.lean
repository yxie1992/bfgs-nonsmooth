import BfgsVerification.QuadraticGaugeConvex
import BfgsVerification.FixedNormalStrongConvex
import BfgsVerification.FiniteMaxLocalCorrectness
import BfgsVerification.RadialHessian
import BfgsVerification.CertificateGeometry

/-! C's literal three-quadratic objective and its actual analytic data. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.PlanarQuadraticExample
open FixedNormal

def branch (i : Fin 3) (x : Vec 2) : ℝ :=
  ![x 0+(x 0)^2+(x 1)^2/2,
    x 1+(x 0)^2/2+3*(x 1)^2/2,
    -x 0-x 1+3*(x 0)^2/2+(x 1)^2] i

def linearPart (i : Fin 3) : Vec 2 := ![![1,0],![0,1],![-1,-1]] i

def hessianDiagonal (i : Fin 3) : Vec 2 := ![![2,1],![1,3],![3,2]] i

def hessian (i : Fin 3) : Mat 2 := diagonal (hessianDiagonal i)

def gradient (i : Fin 3) (x : Vec 2) : Vec 2 := linearPart i+(hessian i).mulVec x

def objective (x : Vec 2) : ℝ := max (branch 0 x) (max (branch 1 x) (branch 2 x))

theorem branch_quadratic (i : Fin 3) (x : Vec 2) :
    branch i x=metricEnergy (hessian i) x/2+dot (linearPart i) x := by
  fin_cases i <;> simp [branch,hessian,hessianDiagonal,linearPart,metricEnergy,dot,
    Fin.sum_univ_two,Matrix.mulVec,Matrix.mul_apply,dotProduct,Matrix.diagonal] <;> ring

theorem branch_contDiff (i : Fin 3) {N : WithTop ℕ∞} : ContDiff ℝ N (branch i) := by
  fin_cases i
  · change ContDiff ℝ N (fun x : Vec 2 => x 0+(x 0)^2+(x 1)^2/2)
    fun_prop (disch := norm_num)
  · change ContDiff ℝ N (fun x : Vec 2 => x 1+(x 0)^2/2+3*(x 1)^2/2)
    fun_prop (disch := norm_num)
  · change ContDiff ℝ N (fun x : Vec 2 => -x 0-x 1+3*(x 0)^2/2+(x 1)^2)
    fun_prop (disch := norm_num)

theorem branch_hasGradient (i : Fin 3) (x : Vec 2) :
    HasFDerivAt (branch i) (gradientFunctional (gradient i x)) x := by
  have hl : HasFDerivAt (fun z => dot (linearPart i) z) (gradientFunctional (linearPart i)) x := by
    simpa only [gradientFunctional_apply] using (gradientFunctional (linearPart i)).hasFDerivAt (x := x)
  have hq := QuadraticGauge.quadratic_hasGradient (hessian i) (Matrix.isSymm_diagonal _) x
  convert hq.add hl using 1
  · funext z
    exact branch_quadratic i z
  · ext z
    simp only [gradientFunctional_apply,ContinuousLinearMap.add_apply,gradient,dot,Pi.add_apply,
      add_mul,Finset.sum_add_distrib]
    ring

theorem gradient_coordinates (x : Vec 2) :
    gradient 0 x=![1+2*x 0,x 1] ∧ gradient 1 x=![x 0,1+3*x 1] ∧
      gradient 2 x=![-1+3*x 0,-1+2*x 1] := by
  constructor
  · ext j; fin_cases j <;> simp [gradient,hessian,hessianDiagonal,linearPart,Matrix.mulVec_diagonal]
  constructor
  · ext j; fin_cases j <;> simp [gradient,hessian,hessianDiagonal,linearPart,Matrix.mulVec_diagonal]
  · ext j; fin_cases j <;> simp [gradient,hessian,hessianDiagonal,linearPart,Matrix.mulVec_diagonal]

theorem hessian_bounds (i : Fin 3) : (hessian i-1).PosSemidef ∧ ((3 : ℝ) • (1 : Mat 2)-hessian i).PosSemidef := by
  have he : hessian i-1=diagonal (fun j => hessianDiagonal i j-1) := by ext j k; simp [hessian,Matrix.diagonal,Matrix.one_apply]; split_ifs <;> ring
  have he' : (3 : ℝ) • (1 : Mat 2)-hessian i=diagonal (fun j => 3-hessianDiagonal i j) := by
    ext j k; simp [hessian,Matrix.diagonal,Matrix.one_apply]; split_ifs <;> ring
  rw [he,he']
  constructor <;> apply Matrix.posSemidef_diagonal_iff.mpr <;> intro j
  all_goals fin_cases i <;> fin_cases j <;> norm_num [hessianDiagonal]

theorem branch_convex (i : Fin 3) : ConvexOn ℝ univ (branch i) := by
  have hQ : (hessian i).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [hessianDiagonal]
  apply ((QuadraticGauge.quadratic_convex (hessian i) hQ).add
    ((gradientFunctional (linearPart i)).toLinearMap.convexOn convex_univ)).congr
  intro x hx
  simp only [Pi.add_apply,ContinuousLinearMap.coe_coe,gradientFunctional_apply]
  exact (branch_quadratic i x).symm

theorem branch_strongConvex (i : Fin 3) : EuclideanStrongConvexOn univ 1 (branch i) := by
  apply ((QuadraticGauge.quadratic_convex (hessian i-1) (hessian_bounds i).1).add
    ((gradientFunctional (linearPart i)).toLinearMap.convexOn convex_univ)).congr
  intro x hx
  simp only [Pi.add_apply,ContinuousLinearMap.coe_coe,gradientFunctional_apply]
  rw [branch_quadratic]
  simp [metricEnergy,dot,sqNorm,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,
    Finset.sum_sub_distrib,mul_sub,pow_two]
  ring

theorem branch_le_objective (i : Fin 3) (x : Vec 2) : branch i x ≤ objective x := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem objective_isGreatest (x : Vec 2) : IsGreatest (range (fun i => branch i x)) (objective x) := by
  refine ⟨?_,?_⟩
  · by_cases h0 : max (branch 1 x) (branch 2 x) ≤ branch 0 x
    · exact ⟨0,(max_eq_left h0).symm⟩
    · by_cases h1 : branch 2 x ≤ branch 1 x
      · exact ⟨1,by rw [objective,max_eq_right (le_of_not_ge h0),max_eq_left h1]⟩
      · exact ⟨2,by rw [objective,max_eq_right (le_of_not_ge h0),max_eq_right (le_of_not_ge h1)]⟩
  · rintro v ⟨i,rfl⟩
    exact branch_le_objective i x

theorem localFiniteMax (x : Vec 2) : ConvexSubdifferential.LocalFiniteMax objective branch x :=
  Eventually.of_forall objective_isGreatest

theorem objective_convex : ConvexOn ℝ univ objective :=
  (branch_convex 0).sup ((branch_convex 1).sup (branch_convex 2))

theorem objective_strongConvex : EuclideanStrongConvexOn univ 1 objective := by
  apply ((branch_strongConvex 0).sup ((branch_strongConvex 1).sup (branch_strongConvex 2))).congr
  intro x hx
  simp only [Pi.sup_apply,sup_eq_max,objective,max_sub_sub_right]

theorem branch_average (x : Vec 2) : (∑ i : Fin 3, branch i x)/3=sqNorm x := by
  simp [Fin.sum_univ_succ,branch,sqNorm,Fin.sum_univ_two]
  ring

theorem objective_lower (x : Vec 2) : sqNorm x ≤ objective x := by
  have h0 := branch_le_objective 0 x
  have h1 := branch_le_objective 1 x
  have h2 := branch_le_objective 2 x
  have he := branch_average x
  norm_num [Fin.sum_univ_succ] at he
  nlinarith

theorem objective_zero : objective 0=0 := by norm_num [objective,branch,Matrix.cons_val_two]

theorem objective_nonneg (x : Vec 2) : 0 ≤ objective x := (sqNorm_nonneg x).trans (objective_lower x)

theorem objective_unique_zero (x : Vec 2) (hx : objective x=0) : x=0 := by
  exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp (le_antisymm (hx ▸ objective_lower x) (sqNorm_nonneg x))

theorem objective_minimum (x : Vec 2) : objective 0 ≤ objective x := by rw [objective_zero]; exact objective_nonneg x

theorem sublevel_compact (b : ℝ) : IsCompact {x | objective x≤b} :=
  Localization.sublevel_compact objective_convex 0 objective_minimum
    (fun x hx => objective_unique_zero x (by simpa only [objective_zero] using hx)) b

end BfgsVerification.PlanarQuadraticExample
