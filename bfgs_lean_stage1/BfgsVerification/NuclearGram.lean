import BfgsVerification.CenteredSpectral
import BfgsVerification.FrameNorms
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual rectangular Gram spectral data and zero-safe normalization. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm InnerProductSpace
open Matrix
namespace BfgsVerification.RectangularNuclear

variable {m n : ℕ}

/-- Frobenius pairing on the actual rectangular matrix space. -/
def pairing (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ := Matrix.trace (Aᵀ * B)

theorem pairing_eq_sum (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing A B = ∑ i : Fin n, ∑ j : Fin m, A j i * B j i := rfl

theorem pairing_add_left (A B C : Matrix (Fin m) (Fin n) ℝ) :
    pairing (A+B) C = pairing A C+pairing B C := by
  simp only [pairing,transpose_add,Matrix.add_mul,trace_add]

theorem pairing_smul_left (t : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing (t • A) B=t*pairing A B := by
  simp only [pairing,transpose_smul,smul_mul,trace_smul,smul_eq_mul]

theorem pairing_right_orthogonal (A B : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : V*Vᵀ=1) :
    pairing (A*V) (B*V)=pairing A B := by
  unfold pairing
  rw [transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Aᵀ,
    Matrix.trace_mul_comm Vᵀ,Matrix.mul_assoc,hV,Matrix.mul_one]

/-- Eigenvalues of the actual Gram matrix, counted with multiplicity. -/
def gramEigenvalues (A : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  (Matrix.isHermitian_transpose_mul_self A).eigenvalues

/-- Singular values are nonnegative square roots of the actual Gram eigenvalues. -/
def singularValues (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (gramEigenvalues A i)

/-- The nuclear norm is defined literally as the sum of actual singular values. -/
def nuclear (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, singularValues A i

def rightFrame (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.isHermitian_transpose_mul_self A).eigenvectorUnitary

theorem gramEigenvalues_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    0 ≤ gramEigenvalues A i := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i

theorem singularValues_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    0 ≤ singularValues A i := Real.sqrt_nonneg _

theorem singularValues_sq (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    singularValues A i ^ 2 = gramEigenvalues A i :=
  Real.sq_sqrt (gramEigenvalues_nonneg A i)

theorem nuclear_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ nuclear A :=
  Finset.sum_nonneg (fun i _ => singularValues_nonneg A i)

theorem rightFrame_transpose_mul (A : Matrix (Fin m) (Fin n) ℝ) :
    (rightFrame A)ᵀ * rightFrame A=1 := by
  simpa only [rightFrame,star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial] using
    unitary.coe_star_mul_self (Matrix.isHermitian_transpose_mul_self A).eigenvectorUnitary

theorem rightFrame_mul_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    rightFrame A * (rightFrame A)ᵀ=1 := by
  simpa only [rightFrame,star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial] using
    unitary.coe_mul_star_self (Matrix.isHermitian_transpose_mul_self A).eigenvectorUnitary

theorem rightFrame_gram (A : Matrix (Fin m) (Fin n) ℝ) :
    (A*rightFrame A)ᵀ*(A*rightFrame A)=Matrix.diagonal (gramEigenvalues A) := by
  have h := (Matrix.isHermitian_transpose_mul_self A).star_mul_self_mul_eq_diagonal
  simpa only [rightFrame,gramEigenvalues,star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq,
    transpose_mul,Matrix.mul_assoc] using h

/-- Quadratic contraction criterion for actual rectangular Euclidean operator norms. -/
theorem opNorm_le_one_of_gram (A : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ x : Vec n, dot x ((Aᵀ*A).mulVec x) ≤ sqNorm x) : ‖A‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [FrameNorms.euclidean_norm_sq,FrameNorms.euclidean_norm_sq]
  change sqNorm (A.mulVec (fun i => x i)) ≤ sqNorm (fun i => x i)
  convert h (fun i => x i) using 1
  change _ = (fun i => x i) ⬝ᵥ (Aᵀ*A).mulVec (fun i => x i)
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
    dotProduct_comm]
  simp only [sqNorm,dotProduct,pow_two]

theorem orthogonal_opNorm_le_one (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : Vᵀ*V=1) : ‖V‖ ≤ 1 := by
  apply opNorm_le_one_of_gram
  intro x
  rw [hV,Matrix.one_mulVec]
  exact le_of_eq (by simp only [dot,sqNorm,pow_two])

/-- Zero-safe inverse singular-value scaling; zero columns are retained. -/
def normalizedColumns (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  A * rightFrame A * Matrix.diagonal (fun i => (singularValues A i)⁻¹)

theorem normalizedColumns_gram (A : Matrix (Fin m) (Fin n) ℝ) :
    (normalizedColumns A)ᵀ * normalizedColumns A =
      Matrix.diagonal (fun i => if singularValues A i=0 then 0 else 1) := by
  unfold normalizedColumns
  rw [transpose_mul,diagonal_transpose,Matrix.mul_assoc,
    ← Matrix.mul_assoc (A*rightFrame A)ᵀ,rightFrame_gram,
    ← Matrix.mul_assoc,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  rw [← singularValues_sq]
  by_cases h : singularValues A i=0
  · simp [h]
  · simp [h,pow_two,← mul_assoc]

theorem normalizedColumns_opNorm_le_one (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖normalizedColumns A‖ ≤ 1 := by
  apply opNorm_le_one_of_gram
  intro x
  rw [normalizedColumns_gram]
  unfold dot sqNorm
  simp only [Matrix.mulVec_diagonal]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : singularValues A i=0
  · simpa only [h,ite_true,mul_zero,zero_mul] using sq_nonneg (x i)
  · simp [h,pow_two]

end BfgsVerification.RectangularNuclear
