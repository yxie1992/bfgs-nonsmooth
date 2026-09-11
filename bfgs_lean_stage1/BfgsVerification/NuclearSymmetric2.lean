import BfgsVerification.FiniteMaxRadialObstruction
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import BfgsVerification.FixedNormalStrongConvex

/-! The actual nuclear norm of a real symmetric 2×2 matrix, defined from its
Hermitian eigenvalues before deriving the source's closed coordinate formulas. -/
noncomputable section
open scoped BigOperators Topology Matrix
open Set Filter
namespace BfgsVerification.NuclearSymmetric2

def nuclear (A : Mat 2) (hA : A.IsHermitian) : ℝ := ∑ i, |hA.eigenvalues i|

theorem nuclear_nonneg (A : Mat 2) (hA : A.IsHermitian) : 0 ≤ nuclear A hA :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

theorem trace_eq_sum_eigenvalues {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    Matrix.trace A = ∑ i, hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal]

theorem abs_add_eq_max (x y : ℝ) : |x|+|y| = max |x+y| |x-y| := by
  apply le_antisymm
  · rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx,abs_of_nonneg hy]
      exact (le_abs_self _).trans (le_max_left _ _)
    · rw [abs_of_nonneg hx,abs_of_nonpos hy]
      exact (le_abs_self _).trans (le_max_right _ _)
    · rw [abs_of_nonpos hx,abs_of_nonneg hy]
      have h := (neg_le_abs (x-y)).trans (le_max_right |x+y| |x-y|)
      linarith
    · rw [abs_of_nonpos hx,abs_of_nonpos hy]
      have h := (neg_le_abs (x+y)).trans (le_max_left |x+y| |x-y|)
      linarith
  · exact max_le (abs_add x y) (abs_sub x y)

/-- Closed nuclear norm formula derived from the actual two eigenvalues,
their trace and determinant. No external eigensolver computation is used. -/
theorem nuclear_eq_max (A : Mat 2) (hA : A.IsHermitian) :
    nuclear A hA = max |A 0 0+A 1 1|
      (Real.sqrt ((A 0 0-A 1 1)^2+4*(A 0 1)^2)) := by
  have htr := trace_eq_sum_eigenvalues A hA
  simp only [Matrix.trace,Fin.sum_univ_two] at htr
  change A 0 0+A 1 1 = hA.eigenvalues 0+hA.eigenvalues 1 at htr
  have hdet := hA.det_eq_prod_eigenvalues
  simp only [Matrix.det_fin_two,Fin.prod_univ_two] at hdet
  have hsym : A 1 0 = A 0 1 := by simpa using hA.apply 0 1
  rw [hsym] at hdet
  change A 0 0*A 1 1-A 0 1*A 0 1 = hA.eigenvalues 0*hA.eigenvalues 1 at hdet
  have hdisc : (A 0 0-A 1 1)^2+4*(A 0 1)^2 =
      (hA.eigenvalues 0-hA.eigenvalues 1)^2 := by
    calc
      _ = (A 0 0+A 1 1)^2-4*(A 0 0*A 1 1-A 0 1*A 0 1) := by ring
      _ = (hA.eigenvalues 0+hA.eigenvalues 1)^2-4*(hA.eigenvalues 0*hA.eigenvalues 1) := by rw [htr,hdet]
      _ = _ := by ring
  rw [hdisc,Real.sqrt_sq_eq_abs]
  simp only [nuclear,Fin.sum_univ_two]
  rw [abs_add_eq_max,htr]


/-- Orthonormal coordinates on the real symmetric matrices. -/
def matrix (x : Vec 3) : Mat 2 :=
  !![x 0, x 1 / Real.sqrt 2; x 1 / Real.sqrt 2, x 2]

def coordinates (A : Mat 2) : Vec 3 := ![A 0 0, Real.sqrt 2 * A 0 1, A 1 1]

def frobenius (A B : Mat 2) : ℝ := ∑ i, ∑ j, A i j * B i j

theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem matrix_hermitian (x : Vec 3) : (matrix x).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.conjTranspose_apply]

theorem coordinates_matrix (x : Vec 3) : coordinates (matrix x) = x := by
  ext i
  fin_cases i <;> simp [coordinates, matrix, ne_of_gt sqrt_two_pos]
  field_simp

theorem matrix_coordinates (A : Mat 2) (hA : A.IsHermitian) : matrix (coordinates A) = A := by
  have hsym : A 1 0 = A 0 1 := by simpa using hA.apply 0 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinates, matrix, ne_of_gt sqrt_two_pos, hsym]

theorem frobenius_matrix (x z : Vec 3) : frobenius (matrix x) (matrix z) = dot x z := by
  simp [frobenius, matrix, dot, Fin.sum_univ_two, Fin.sum_univ_three]
  field_simp
  nlinarith [sqrt_two_sq]

theorem matrix_sub (x z : Vec 3) : matrix (x-z) = matrix x-matrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, sub_div]

theorem matrix_smul (a : ℝ) (x : Vec 3) : matrix (a • x) = a • matrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix] <;> ring

def nuclearCoords (x : Vec 3) : ℝ := nuclear (matrix x) (matrix_hermitian x)

def discr (x : Vec 3) : ℝ := (x 0-x 2)^2 + 2*(x 1)^2

theorem discr_nonneg (x : Vec 3) : 0 ≤ discr x := by
  unfold discr
  positivity

theorem nuclearCoords_eq (x : Vec 3) :
    nuclearCoords x = max |x 0+x 2| (Real.sqrt (discr x)) := by
  rw [nuclearCoords, nuclear_eq_max]
  simp only [matrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_two]
  congr 3
  field_simp
  nlinarith [sqrt_two_sq]

def discrMap : Vec 3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := !₂[x 0-x 2, Real.sqrt 2*x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

theorem discrMap_norm (x : Vec 3) : ‖discrMap x‖ = Real.sqrt (discr x) := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  congr 1
  simp [discrMap, discr, mul_pow, sqrt_two_sq]

theorem nuclearCoords_convex : ConvexOn ℝ univ nuclearCoords := by
  have ht : ConvexOn ℝ univ (fun x : Vec 3 => |x 0+x 2|) := by
    have h := (convexOn_norm (E := ℝ) convex_univ).comp_linearMap
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 +
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).toLinearMap)
    simpa [Real.norm_eq_abs] using h
  have hd : ConvexOn ℝ univ (fun x : Vec 3 => Real.sqrt (discr x)) := by
    have h := (convexOn_norm (E := EuclideanSpace ℝ (Fin 2)) convex_univ).comp_linearMap discrMap
    simpa only [Set.preimage_univ, Function.comp_def, discrMap_norm] using h
  convert ht.sup hd using 1
  ext x
  exact nuclearCoords_eq x


def center : Vec 3 := ![2,0,0]
def minimizer : Vec 3 := ![1,0,0]
def smooth (x : Vec 3) : ℝ := sqNorm (x-center)/2
def objective (x : Vec 3) : ℝ := smooth x+nuclearCoords x

theorem objective_frobenius (x : Vec 3) :
    objective x = frobenius (matrix x-matrix center) (matrix x-matrix center)/2 +
      nuclear (matrix x) (matrix_hermitian x) := by
  rw [← matrix_sub, frobenius_matrix]
  simp [objective, smooth, nuclearCoords, dot, sqNorm, pow_two]

theorem nuclearCoords_ge_first (x : Vec 3) : x 0 ≤ nuclearCoords x := by
  have ht : x 0+x 2 ≤ nuclearCoords x := by
    rw [nuclearCoords_eq]
    exact (le_abs_self _).trans (le_max_left _ _)
  have hd : x 0-x 2 ≤ nuclearCoords x := by
    rw [nuclearCoords_eq]
    have hs : |x 0-x 2| ≤ Real.sqrt (discr x) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      unfold discr
      nlinarith [sq_nonneg (x 1)]
    exact (le_abs_self _).trans (hs.trans (le_max_right _ _))
  linarith

theorem objective_minimizer_value : objective minimizer = 3/2 := by
  norm_num [objective, smooth, sqNorm, center, minimizer, nuclearCoords_eq, discr,
    Fin.sum_univ_three, Matrix.cons_val_two]

theorem objective_gap (x : Vec 3) :
    sqNorm (x-minimizer)/2 ≤ objective x-objective minimizer := by
  have h := nuclearCoords_ge_first x
  rw [objective_minimizer_value]
  simp only [objective, smooth, sqNorm, Fin.sum_univ_three, Pi.sub_apply,
    center, minimizer, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two]
  nlinarith

theorem objective_minimum (x : Vec 3) : objective minimizer ≤ objective x := by
  have h := objective_gap x
  have hpos := sqNorm_nonneg (x-minimizer)
  linarith

theorem objective_unique (x : Vec 3) (hx : objective x=objective minimizer) : x=minimizer := by
  have h := objective_gap x
  rw [hx,sub_self] at h
  have hs : sqNorm (x-minimizer)=0 := le_antisymm (by linarith) (sqNorm_nonneg _)
  ext i
  have hb : ((x-minimizer) i)^2 ≤ sqNorm (x-minimizer) :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((x-minimizer) j)) (Finset.mem_univ i)
  rw [hs] at hb
  simp only [Pi.sub_apply] at hb
  nlinarith [sq_nonneg (x i-minimizer i)]

/-- Strong convexity in the Euclidean/Frobenius norm, with modulus exactly one. -/
theorem objective_strongConvex : FixedNormal.EuclideanStrongConvexOn univ 1 objective := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  have hc := nuclearCoords_convex.2 hx hz ha hb hab
  have hb' : b=1-a := by linarith
  subst b
  simp only [objective, smooth, sqNorm, Fin.sum_univ_three, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, center,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two] at hc ⊢
  nlinarith

theorem objective_convex : ConvexOn ℝ univ objective := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  have hc := objective_strongConvex.2 hx hz ha hb hab
  have hsq := FixedNormal.sqNorm_convex_combination x z b
  have ha' : a=1-b := by linarith
  rw [← ha'] at hsq
  have hp : 0 ≤ b*a*sqNorm (z-x) := mul_nonneg (mul_nonneg hb ha) (sqNorm_nonneg _)
  simp only [smul_eq_mul] at hc ⊢
  rw [hsq] at hc
  nlinarith

theorem objective_sublevel_compact (b : ℝ) : IsCompact {x | objective x ≤ b} :=
  Localization.sublevel_compact objective_convex minimizer objective_minimum objective_unique b

theorem smooth_hasGradient (x : Vec 3) :
    HasFDerivAt smooth (gradientFunctional (x-center)) x := by
  let P (i : Fin 3) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i
  have h0 := (P 0).hasFDerivAt (x := x)
  have h1 := (P 1).hasFDerivAt (x := x)
  have h2 := (P 2).hasFDerivAt (x := x)
  have h := ((((h0.sub_const 2).mul (h0.sub_const 2)).add (h1.mul h1)).add
    (h2.mul h2)).const_mul (1/2:ℝ)
  convert h using 1
  · ext w
    simp [smooth, sqNorm, center, Fin.sum_univ_three, P, Matrix.cons_val_two]
    ring
  · ext v
    simp [gradientFunctional_apply, dot, Fin.sum_univ_three, P, center, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    ring

theorem discr_hasGradient (x : Vec 3) :
    HasFDerivAt discr (gradientFunctional ![2*(x 0-x 2),4*x 1,-2*(x 0-x 2)]) x := by
  let P (i : Fin 3) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i
  have h0 := (P 0).hasFDerivAt (x := x)
  have h1 := (P 1).hasFDerivAt (x := x)
  have h2 := (P 2).hasFDerivAt (x := x)
  have h := ((h0.sub h2).mul (h0.sub h2)).add ((h1.mul h1).const_mul 2)
  convert h using 1
  · ext w; simp [discr, P]; ring
  · ext v; simp [gradientFunctional_apply, dot, Fin.sum_univ_three, P]; ring

theorem trace_hasGradient (x : Vec 3) :
    HasFDerivAt (fun w : Vec 3 => w 0+w 2) (gradientFunctional ![1,0,1]) x := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt
    (x := x)).add ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt
    (x := x))
  convert h using 1
  ext v
  simp [gradientFunctional_apply, dot, Fin.sum_univ_three]


theorem nuclearCoords_hasGradient_pos {x : Vec 3}
    (hx : Real.sqrt (discr x) < x 0+x 2) :
    HasFDerivAt nuclearCoords (gradientFunctional ![1,0,1]) x := by
  apply (trace_hasGradient x).congr_of_eventuallyEq
  have hc : Continuous (fun w : Vec 3 => Real.sqrt (discr w)) := by unfold discr; fun_prop
  have ht : Continuous (fun w : Vec 3 => w 0+w 2) := by fun_prop
  filter_upwards [(isOpen_lt hc ht).mem_nhds hx] with w hw
  rw [nuclearCoords_eq, abs_of_pos (lt_of_le_of_lt (Real.sqrt_nonneg _) hw),
    max_eq_left hw.le]

theorem nuclearCoords_hasGradient_indef {x : Vec 3}
    (hx : |x 0+x 2| < Real.sqrt (discr x)) :
    HasFDerivAt nuclearCoords
      ((1/(2*Real.sqrt (discr x))) •
        gradientFunctional ![2*(x 0-x 2),4*x 1,-2*(x 0-x 2)]) x := by
  have hpos : 0 < Real.sqrt (discr x) := lt_of_le_of_lt (abs_nonneg _) hx
  have hn : discr x ≠ 0 := by intro he; rw [he,Real.sqrt_zero] at hpos; linarith
  apply ((discr_hasGradient x).sqrt hn).congr_of_eventuallyEq
  have hc : Continuous (fun w : Vec 3 => Real.sqrt (discr w)) := by unfold discr; fun_prop
  have ht : Continuous (fun w : Vec 3 => |w 0+w 2|) := by fun_prop
  filter_upwards [(isOpen_lt ht hc).mem_nhds hx] with w hw
  rw [nuclearCoords_eq,max_eq_right hw.le]


theorem matrix_add (x z : Vec 3) : matrix (x+z)=matrix x+matrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,add_div]

theorem matrix_center : matrix center=!![2,0;0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix,center,Matrix.cons_val_two]

theorem matrix_minimizer : matrix minimizer=!![1,0;0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix,minimizer,Matrix.cons_val_two]

theorem matrix_det (x : Vec 3) :
    (matrix x).det=((x 0+x 2)^2-discr x)/4 := by
  simp [Matrix.det_fin_two,matrix,discr]
  field_simp
  ring_nf

theorem matrix_eigenvalues_nonzero {x : Vec 3} (hx : (matrix x).det ≠ 0) :
    ∀ i, (matrix_hermitian x).eigenvalues i ≠ 0 := by
  have hd := (matrix_hermitian x).det_eq_prod_eigenvalues
  change (matrix x).det=∏ i, (matrix_hermitian x).eigenvalues i at hd
  have hp : ∏ i, (matrix_hermitian x).eigenvalues i ≠ 0 := by
    intro he
    apply hx
    simpa only [he] using hd
  exact fun i => Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)

theorem nuclear_minimizer_value : nuclearCoords minimizer=1 := by
  norm_num [nuclearCoords_eq,minimizer,discr,Matrix.cons_val_two]

/-- The report's actual nuclear-norm subgradient at diag(1,0). -/
theorem nuclear_minimizer_support : Homogeneous.Supports nuclearCoords minimizer minimizer := by
  intro z
  have h := nuclearCoords_ge_first z
  rw [nuclear_minimizer_value]
  simpa [dot,minimizer,Fin.sum_univ_three,Matrix.cons_val_two] using sub_le_sub_right h 1

/-- The literal strong-convexity inequality uses the symmetric matrices'
Frobenius norm, with modulus one and no ambient-Pi norm substitution. -/
theorem objective_frobenius_strong (x z : Vec 3) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    objective (a • x+b • z) ≤ a*objective x+b*objective z -
      a*b/2*frobenius (matrix z-matrix x) (matrix z-matrix x) := by
  have hc := objective_strongConvex.2 (mem_univ x) (mem_univ z) ha hb hab
  have hsq := FixedNormal.sqNorm_convex_combination x z b
  have ha' : a=1-b := by linarith
  rw [← ha'] at hsq
  rw [← matrix_sub,frobenius_matrix]
  have hd : dot (z-x) (z-x)=sqNorm (z-x) := by simp [dot,sqNorm,pow_two]
  rw [hd]
  simp only [smul_eq_mul] at hc
  rw [hsq] at hc
  nlinarith


/-- The source objective on every actual symmetric matrix, using the inverse
coordinate map rather than assuming that the matrix was supplied as coordinates. -/
theorem objective_on_symmetric (A : Mat 2) (hA : A.IsHermitian) :
    objective (coordinates A)=frobenius (A-matrix center) (A-matrix center)/2+nuclear A hA := by
  have h := objective_frobenius (coordinates A)
  simpa only [matrix_coordinates A hA] using h

theorem gradientFunctional_frobenius (g v : Vec 3) :
    gradientFunctional g v=frobenius (matrix g) (matrix v) := by
  rw [gradientFunctional_apply,frobenius_matrix]

theorem minimizer_gradient_cancellation : minimizer-center+minimizer=0 := by
  ext i
  fin_cases i <;> norm_num [minimizer,center,Matrix.cons_val_two]

end BfgsVerification.NuclearSymmetric2





