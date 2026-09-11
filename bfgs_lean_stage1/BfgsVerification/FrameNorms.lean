import BfgsVerification.FrameBounds
import BfgsVerification.SmoothSubspace

/-! Representation bridges for Module M frame bounds: the actual Euclidean
operator norm and orthonormal matrices for arbitrary finite-dimensional subspaces. -/

noncomputable section
open scoped BigOperators Matrix.L2OpNorm InnerProductSpace
open Matrix

namespace BfgsVerification.FrameNorms

/-- The operator norm of the actual matrix map on Euclidean space, avoiding
any default matrix or finite-Pi norm convention. -/
def euclideanOpNorm {r : ℕ} (T : Mat r) : ℝ := ‖Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ) T‖

theorem euclidean_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = sqNorm (fun i => x i) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, sqNorm]

/-- For real matrices, transpose has exactly the same Euclidean operator norm. -/
theorem euclideanOpNorm_transpose {r : ℕ} (T : Mat r) :
    euclideanOpNorm Tᵀ = euclideanOpNorm T := by
  unfold euclideanOpNorm
  rw [← Matrix.cstar_norm_def, ← Matrix.cstar_norm_def]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose T

/-- Squared operator norm is characterized by its actual action on every vector. -/
theorem continuous_operator_sq_le_iff {r : ℕ}
    (A : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (a : ℝ) (ha : 0 ≤ a) :
    ‖A‖ ^ 2 ≤ a ↔ ∀ v, ‖A v‖ ^ 2 ≤ a * ‖v‖ ^ 2 := by
  constructor
  · intro h v
    calc
      ‖A v‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (A.le_opNorm v)
      _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
      _ ≤ a * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
  · intro h
    have hn : ‖A‖ ≤ Real.sqrt a := by
      apply A.opNorm_le_bound (Real.sqrt_nonneg _)
      intro v
      apply (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt ha]
      exact h v
    have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn
    rwa [Real.sq_sqrt ha] at hs

/-- The formal quadratic transport bound is equivalent to the ordinary squared
Euclidean operator norm bound, including zero-dimensional frames. -/
theorem operatorSqBound_iff_opNorm_sq {r : ℕ} (T : Mat r) (a : ℝ) (ha : 0 ≤ a) :
    FrameBounds.OperatorSqBound T a ↔ euclideanOpNorm T ^ 2 ≤ a := by
  rw [← euclideanOpNorm_transpose T]
  unfold euclideanOpNorm
  rw [continuous_operator_sq_le_iff _ a ha]
  constructor
  · intro h v
    rw [euclidean_norm_sq, euclidean_norm_sq]
    exact h (fun i => v i)
  · intro h v
    have hv := h ((WithLp.equiv 2 (Vec r)).symm v)
    rw [euclidean_norm_sq, euclidean_norm_sq] at hv
    exact hv

theorem euclidean_sum_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (∑ j, v j) i = ∑ j, v j i := by
  change ((WithLp.linearEquiv 2 ℝ (Vec n)) (∑ j, v j)) i = _
  rw [map_sum, Finset.sum_apply]
  rfl

/-- Every subspace of real finite-dimensional Euclidean space admits an actual
orthonormal-column matrix, with its column range exactly the given subspace.
No nonzero dimension or nontriviality of the subspace is required. -/
theorem orthonormal_matrix_for_subspace {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ U : Matrix (Fin n) (Fin (Module.finrank ℝ S)) ℝ,
      Uᵀ * U = 1 ∧ ∀ x : EuclideanSpace ℝ (Fin n),
        x ∈ S ↔ ∃ a : Vec (Module.finrank ℝ S), U.mulVec a = (fun i => x i) := by
  let b := stdOrthonormalBasis ℝ S
  let U : Matrix (Fin n) (Fin (Module.finrank ℝ S)) ℝ := fun i j => (b j : EuclideanSpace ℝ (Fin n)) i
  refine ⟨U, ?_, ?_⟩
  · ext i j
    have ho := (orthonormal_iff_ite.mp b.orthonormal) i j
    change dotProduct (fun k => (b i : EuclideanSpace ℝ (Fin n)) k)
      (fun k => (b j : EuclideanSpace ℝ (Fin n)) k) = _
    change ⟪(b i : EuclideanSpace ℝ (Fin n)), (b j : EuclideanSpace ℝ (Fin n))⟫_ℝ =
      (if i = j then 1 else 0) at ho
    rw [dotProduct_comm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.one_apply] using ho
  · intro x
    constructor
    · intro hx
      refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
      ext i
      have hi := congrArg (fun z : S => (z : EuclideanSpace ℝ (Fin n)) i)
        (b.sum_repr ⟨x, hx⟩)
      simpa [Matrix.mulVec, dotProduct, U, euclidean_sum_apply, mul_comm] using hi
    · rintro ⟨a, ha⟩
      have hx : (∑ j, a j • (b j : EuclideanSpace ℝ (Fin n))) = x := by
        ext i
        have hi := congrFun ha i
        simpa [Matrix.mulVec, dotProduct, U, euclidean_sum_apply, mul_comm] using hi
      rw [← hx]
      exact S.sum_mem (fun j _ => S.smul_mem (a j) (b j).property)

end BfgsVerification.FrameNorms
