import BfgsVerification.Definitions

/-!
# Principal determinants as coefficients and invariance under conjugation

All sums here use actual principal submatrix determinants. The coefficient
identity is proved by determinant multilinearity, without spectral surrogates.
-/

noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace BfgsVerification.PrincipalInvariance

/-- Selecting rows from `M` on `I` and from the identity outside `I` leaves
exactly the principal determinant on `I`. -/
theorem det_piecewise_one {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (I : Finset ι) (M : Matrix ι ι R) :
    Matrix.det (I.piecewise M (1 : Matrix ι ι R)) =
      Matrix.det (M.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))) := by
  classical
  let e := Equiv.Set.sumCompl (I : Set ι)
  have hm : Matrix.submatrix (I.piecewise M (1 : Matrix ι ι R)) e e =
      Matrix.fromBlocks
        (M.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι)))
        (M.submatrix (fun i : I => (i : ι)) (fun i : ↥((I : Set ι)ᶜ) => (i : ι)))
        0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · change (I.piecewise M (1 : Matrix ι ι R)) (i : ι) (j : ι) = M i j
      simp [Finset.piecewise, i.property]
    · change (I.piecewise M (1 : Matrix ι ι R)) (i : ι) (j : ι) = M i j
      simp [Finset.piecewise, i.property]
    · have hne : (i : ι) ≠ (j : ι) := by
        intro heq
        exact i.property (heq ▸ j.property)
      have hi : (i : ι) ∉ I := i.property
      change (I.piecewise M (1 : Matrix ι ι R)) (i : ι) (j : ι) = 0
      simp [Finset.piecewise, hi, Matrix.one_apply, hne]
    · have hi : (i : ι) ∉ I := i.property
      change (I.piecewise M (1 : Matrix ι ι R)) (i : ι) (j : ι) =
        (1 : Matrix ↥((I : Set ι)ᶜ) ↥((I : Set ι)ᶜ) R) i j
      simp [Finset.piecewise, hi, Matrix.one_apply, Subtype.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self e, hm, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

/-- Expanding in all rows writes `det(1+M)` as a sum of actual principal minors. -/
theorem det_one_add_eq_sum_principal {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι R) :
    Matrix.det (1 + M) = ∑ I : Finset ι,
      Matrix.det (M.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))) := by
  rw [add_comm]
  change Matrix.detRowAlternating.toMultilinearMap (M + (1 : Matrix ι ι R)) = _
  rw [MultilinearMap.map_add_univ]
  apply Finset.sum_congr rfl
  intro I _
  change Matrix.det (I.piecewise M (1 : Matrix ι ι R)) = _
  exact det_piecewise_one I M


/-- Scalar polynomial expansion of the determinant in actual principal minors. -/
theorem det_one_add_smul_eq_sum_principal {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (t : R) (M : Matrix ι ι R) :
    Matrix.det (1 + t • M) = ∑ I : Finset ι, t ^ I.card *
      Matrix.det (M.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))) := by
  rw [det_one_add_eq_sum_principal]
  apply Finset.sum_congr rfl
  intro I _
  rw [Matrix.submatrix_smul]
  change Matrix.det (t • M.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))) = _
  rw [Matrix.det_smul]
  simp

/-- `det(I + X H)` is a genuine polynomial attached to the actual matrix. -/
def principalPolynomial {n : ℕ} (H : Mat n) : ℝ[X] :=
  Matrix.det (1 + (Polynomial.X : ℝ[X]) • H.map Polynomial.C)

/-- The degree-`j` coefficient equals the sum of all actual `j`-principal
submatrix determinants, including the empty and out-of-range cases. -/
theorem principalPolynomial_coeff {n : ℕ} (H : Mat n) (j : ℕ) :
    (principalPolynomial H).coeff j = principalSum H j := by
  classical
  unfold principalPolynomial principalSum
  rw [det_one_add_smul_eq_sum_principal, Polynomial.finset_sum_coeff]
  have hmap (I : Finset (Fin n)) :
      Matrix.det ((H.map Polynomial.C).submatrix (fun i : I => (i : Fin n))
        (fun i : I => (i : Fin n))) = Polynomial.C
        (Matrix.det (H.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n)))) := by
    rw [Matrix.submatrix_map]
    exact (Polynomial.C.map_det _).symm
  simp_rw [hmap]
  simp_rw [mul_comm (Polynomial.X ^ _) (Polynomial.C _), Polynomial.coeff_C_mul_X_pow]
  rw [Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  simp only [eq_comm]


/-- Determinant generating functions are invariant under ordinary similarity. -/
theorem det_one_add_smul_conjugate {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (t : R) (U V H : Matrix ι ι R) (hUV : U * V = 1) :
    Matrix.det (1 + t • (U * H * V)) = Matrix.det (1 + t • H) := by
  have hi : 1 + t • (U * H * V) = U * (1 + t • H) * V := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hUV]
  rw [hi, Matrix.det_mul_right_comm, hUV, one_mul]

/-- Similarity invariance at the polynomial level, before taking coefficients. -/
theorem principalPolynomial_conjugate {n : ℕ} (U V H : Mat n) (hUV : U * V = 1) :
    principalPolynomial (U * H * V) = principalPolynomial H := by
  unfold principalPolynomial
  rw [Matrix.map_mul, Matrix.map_mul]
  apply det_one_add_smul_conjugate
  rw [← Matrix.map_mul, hUV]
  exact Matrix.map_one Polynomial.C Polynomial.C.map_zero Polynomial.C.map_one

/-- Similarity preserves sums of actual principal determinants in every degree. -/
theorem principalSum_conjugate {n : ℕ} (U V H : Mat n) (hUV : U * V = 1) (j : ℕ) :
    principalSum (U * H * V) j = principalSum H j := by
  rw [← principalPolynomial_coeff, ← principalPolynomial_coeff,
    principalPolynomial_conjugate U V H hUV]


/-- The orthogonal change-of-basis form used by the principal-minor hierarchy. -/
theorem principalSum_orthogonal_conjugate {n : ℕ} (Q H : Mat n)
    (hQ : Q * Q.transpose = 1) (j : ℕ) :
    principalSum (Q.transpose * H * Q) j = principalSum H j :=
  principalSum_conjugate Q.transpose Q H (Matrix.mul_eq_one_comm.mp hQ) j

end BfgsVerification.PrincipalInvariance
