import BfgsVerification.PlanarQuadraticModel

/-! C's exact affine coefficients and literal rational box bounds. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.PlanarQuadraticExample

def denominator (x : Vec 2) : ℝ := 3*(1+x 1-x 0*x 1)
def numerator (x : Vec 2) : Vec 3 :=
  ![1-4*x 0+3*x 1-7*x 0*x 1,
    1+2*x 0-3*x 1-x 0*x 1,
    1+2*x 0+3*x 1+5*x 0*x 1]
def coefficients (x : Vec 2) : Vec 3 := fun i => numerator x i/denominator x

def box : Set (Vec 2) := {x | |x 0|≤1/10 ∧ |x 1|≤1/10}

theorem coefficient_box_bounds {x : Vec 2} (hx : x ∈ box) :
    267/100 ≤ denominator x ∧ 23/100 ≤ numerator x 0 ∧
      49/100 ≤ numerator x 1 ∧ 45/100 ≤ numerator x 2 := by
  have hprod : |x 0*x 1|≤1/100 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hx.1 hx.2 (abs_nonneg (x 1)) (show (0:ℝ)≤1/10 by norm_num)]
  obtain ⟨hu0,hu1⟩ := abs_le.mp hx.1
  obtain ⟨hv0,hv1⟩ := abs_le.mp hx.2
  obtain ⟨huv0,huv1⟩ := abs_le.mp hprod
  dsimp [denominator,numerator]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem denominator_pos_on_box {x : Vec 2} (hx : x∈box) : 0<denominator x := by
  have h := (coefficient_box_bounds hx).1
  linarith

theorem coefficients_pos_on_box {x : Vec 2} (hx : x∈box) (i : Fin 3) : 0<coefficients x i := by
  apply div_pos _ (denominator_pos_on_box hx)
  have h := coefficient_box_bounds hx
  fin_cases i
  · change 0<numerator x 0
    linarith [h.2.1]
  · change 0<numerator x 1
    linarith [h.2.2.1]
  · change 0<numerator x 2
    linarith [h.2.2.2]

theorem coefficients_sum {x : Vec 2} (hD : denominator x ≠ 0) :
    (∑ i : Fin 3, coefficients x i)=1 := by
  norm_num [Fin.sum_univ_succ,coefficients,numerator]
  field_simp
  dsimp [denominator]
  ring

theorem coefficients_zero {x : Vec 2} (hD : denominator x ≠ 0) :
    (∑ i : Fin 3, coefficients x i • gradient i x)=0 := by
  ext j
  fin_cases j <;> norm_num [Fin.sum_univ_succ,coefficients,numerator,gradient,hessian,
    hessianDiagonal,linearPart,Matrix.mulVec_diagonal,Finset.sum_apply]
  all_goals field_simp
  all_goals ring

theorem gradient_affineIndependent {x : Vec 2} (hD : denominator x ≠ 0) :
    AffineIndependent ℝ (fun i : Fin 3 => gradient i x) := by
  apply (affineIndependent_iff_of_fintype ℝ _).mpr
  intro w hs hw i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hs] at hw
  have hu := congrArg (fun z : Vec 2 => z 0) hw
  have hv := congrArg (fun z : Vec 2 => z 1) hw
  norm_num [Fin.sum_univ_succ,gradient,hessian,hessianDiagonal,linearPart,
    Matrix.mulVec_diagonal,Finset.sum_apply] at hu hv
  norm_num [Fin.sum_univ_succ] at hs
  have he0 : (2-x 0)*w 0+(1-2*x 0)*w 1=0 := by
    linear_combination hu-(-1+3*x 0)*hs
  have he1 : (1-x 1)*w 0+(2+x 1)*w 1=0 := by
    linear_combination hv-(-1+2*x 1)*hs
  have hp0 : denominator x*w 0=0 := by
    dsimp [denominator]
    linear_combination (2+x 1)*he0-(1-2*x 0)*he1
  have hp1 : denominator x*w 1=0 := by
    dsimp [denominator]
    linear_combination (2-x 0)*he1-(1-x 1)*he0
  have hw0 : w 0=0 := (mul_eq_zero.mp hp0).resolve_left hD
  have hw1 : w 1=0 := (mul_eq_zero.mp hp1).resolve_left hD
  fin_cases i
  · exact hw0
  · exact hw1
  · change w 2=0
    linarith

/-- The printed formulas are the unique actual affine representation of zero. -/
theorem coefficients_unique {x : Vec 2} (hD : denominator x ≠ 0) (w : Vec 3)
    (hs : ∑ i, w i=1) (hw : ∑ i, w i • gradient i x=0) : w=coefficients x := by
  have hs' : (∑ i, w i)=(∑ i, coefficients x i) := hs.trans (coefficients_sum hD).symm
  have hw' : (∑ i, w i • gradient i x)=(∑ i, coefficients x i • gradient i x) :=
    hw.trans (coefficients_zero hD).symm
  ext i
  exact (gradient_affineIndependent hD).eq_of_sum_eq_sum hs' hw' i (Finset.mem_univ i)

theorem initial_gradients : gradient 0 0=![1,0] ∧ gradient 1 0=![0,1] ∧ gradient 2 0=![-1,-1] := by
  simpa using gradient_coordinates (0 : Vec 2)

theorem initial_coefficients : coefficients (0 : Vec 2)=![1/3,1/3,1/3] := by
  ext i
  fin_cases i <;> norm_num [coefficients,numerator,denominator,Matrix.cons_val_two]

theorem initial_active : ∀ i : Fin 3, branch i 0=objective 0 := by
  intro i
  fin_cases i <;> norm_num [branch,objective_zero,Matrix.cons_val_two]

theorem small_sublevel_mem_box {x : Vec 2} (hx : objective x≤1/100) : x∈box := by
  have hsq : (x 0)^2+(x 1)^2≤1/100 := by
    simpa only [sqNorm,Fin.sum_univ_two] using (objective_lower x).trans hx
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (show (0:ℝ)≤1/10 by norm_num)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 1)]
  · apply (sq_le_sq₀ (abs_nonneg _) (show (0:ℝ)≤1/10 by norm_num)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 0)]

end BfgsVerification.PlanarQuadraticExample
