import BfgsVerification.CompressionDeterminant
import BfgsVerification.BFGSUpdate
import BfgsVerification.GramSchur
import BfgsVerification.CompressionAlgebra

/-!
# Compression of the actual projected inverse-BFGS matrix

All matrix identities use arbitrary rectangular compression matrices. The
determinant identities are supplied separately by `CompressionDeterminant`.
-/

noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace BfgsVerification.BFGSCompression

theorem transpose_outer {n : ℕ} (a b : Vec n) : (outer a b)ᵀ = outer b a := by
  ext i j
  simp [outer, mul_comm]

theorem mul_outer {n : ℕ} (A : Mat n) (a b : Vec n) :
    A * outer a b = outer (A.mulVec a) b := by
  ext i j
  simp only [Matrix.mul_apply, outer, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem outer_mul {n : ℕ} (A : Mat n) (a b : Vec n) :
    outer a b * A = outer a (Aᵀ.mulVec b) := by
  ext i j
  simp only [Matrix.mul_apply, outer, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem outer_mul_outer {n : ℕ} (a b c d : Vec n) :
    outer a b * outer c d = dot b c • outer a d := by
  ext i j
  simp only [Matrix.mul_apply, outer, Matrix.smul_apply, smul_eq_mul, dot, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem congruence_outer {n m : ℕ} (Z : Matrix (Fin n) (Fin m) ℝ) (a b : Vec n) :
    Zᵀ * outer a b * Z = outer (Zᵀ.mulVec a) (Zᵀ.mulVec b) := by
  ext i j
  simp only [Matrix.mul_apply, outer, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem projection_expansion {n : ℕ} (H : Mat n) (v y : Vec n) (κ : ℝ)
    (hsym : H.IsSymm) :
    (1 - κ⁻¹ • outer v y) * H * (1 - κ⁻¹ • outer v y)ᵀ =
      H - κ⁻¹ • (outer v (H.mulVec y) + outer (H.mulVec y) v) +
        (dot y (H.mulVec y) / κ ^ 2) • outer v v := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, transpose_outer]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [outer_mul, hsym.eq, mul_outer, outer_mul_outer]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, outer]
  rw [dot]
  have hswap : (∑ i, (H.mulVec y) i * y i) = dot y (H.mulVec y) := by
    simp [dot, mul_comm]
  rw [hswap]
  ring

theorem projected_compression {n m : ℕ} (H : Mat n) (Z : Matrix (Fin n) (Fin m) ℝ)
    (v y : Vec n) (κ : ℝ) (hsym : H.IsSymm) :
    Zᵀ * ((1 - κ⁻¹ • outer v y) * H * (1 - κ⁻¹ • outer v y)ᵀ) * Z =
      CompressionDeterminant.compression (Zᵀ * H * Z)
        (Zᵀ.mulVec v) (Zᵀ.mulVec (H.mulVec y)) κ (dot y (H.mulVec y)) := by
  rw [projection_expansion H v y κ hsym]
  simp only [CompressionDeterminant.compression, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, congruence_outer]

/-- Compress the actual, unmodified inverse-BFGS update. The two scalar
    nonzero assumptions are exactly those required by its denominators. -/
theorem inverseBFGS_compression {n m : ℕ} (H : Mat n) (Z : Matrix (Fin n) (Fin m) ℝ)
    (g y : Vec n) (α : ℝ) (hsym : H.IsSymm) (hα : α ≠ 0)
    (hq : metricEnergy H g ≠ 0)
    (hβ : -dot y (H.mulVec g) / metricEnergy H g ≠ 0) :
    let q := metricEnergy H g
    let β := -dot y (H.mulVec g) / q
    Zᵀ * inverseBFGS H (bfgsStep H g α) y * Z =
      CompressionDeterminant.compression (Zᵀ * H * Z)
        (Zᵀ.mulVec (H.mulVec g)) (Zᵀ.mulVec (H.mulVec y))
        (-β * q) (dot y (H.mulVec y)) +
      (α / (β * q)) • outer (Zᵀ.mulVec (H.mulVec g)) (Zᵀ.mulVec (H.mulVec g)) := by
  dsimp only
  let q := metricEnergy H g
  let β := -dot y (H.mulVec g) / q
  let v := H.mulVec g
  change Zᵀ * inverseBFGS H (bfgsStep H g α) y * Z =
    CompressionDeterminant.compression (Zᵀ * H * Z)
      (Zᵀ.mulVec v) (Zᵀ.mulVec (H.mulVec y)) (-β * q) (dot y (H.mulVec y)) +
      (α / (β * q)) • outer (Zᵀ.mulVec v) (Zᵀ.mulVec v)
  have hupdate := inverseBFGS_projection_form H g y α hα hq hβ
  change inverseBFGS H (bfgsStep H g α) y =
    (1 + (β * q)⁻¹ • outer v y) * H * (1 + (β * q)⁻¹ • outer y v) +
      (α / (β * q)) • outer v v at hupdate
  rw [hupdate, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    congruence_outer]
  congr 1
  simpa only [neg_mul, inv_neg, neg_smul, sub_neg_eq_add, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_smul, transpose_outer] using
    projected_compression H Z v y (-β * q) hsym

/-- The complete single-compression inequality for the actual full inverse-BFGS
    matrix. The larger Gram matrices may be singular, and all determinant
    identities and inequalities used here are proved from the matrix hypotheses. -/
theorem compressed_inverseBFGS_bound {n m : ℕ} (H : Mat n)
    (Z : Matrix (Fin n) (Fin m) ℝ) (g y : Vec n) (α : ℝ)
    (hH : H.PosDef) (hZ : Function.Injective Z.mulVec) (hα : 0 < α)
    (hq : 0 < metricEnergy H g)
    (hβ : 0 < -dot y (H.mulVec g) / metricEnergy H g) :
    let q := metricEnergy H g
    let β := -dot y (H.mulVec g) / q
    (metricGram (inverseBFGS H (bfgsStep H g α) y) Z).det ≤
      (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y) Z)).det / (β ^ 2 * q) +
        α / β * (metricGram H Z).det := by
  dsimp only
  let q := metricEnergy H g
  let β := -dot y (H.mulVec g) / q
  let A := metricGram H Z
  let a := Zᵀ.mulVec (H.mulVec g)
  let b := Zᵀ.mulVec (H.mulVec y)
  let κ := -β * q
  let r := metricEnergy H y
  let u := dot a (A⁻¹.mulVec a)
  let w := dot a (A⁻¹.mulVec b)
  let z := dot b (A⁻¹.mulVec b)
  let D := (CompressionDeterminant.compression A a b κ r).det
  let Dy := (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y) Z)).det
  let Dgy := (metricGram H (Matrix.fromCols (fun i k => ![g i, y i] k) Z)).det
  have hsymH : H.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.eq
  have hAPos : A.PosDef := metricGram_posDef hH hZ
  have hsymA : A.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hAPos.isHermitian.eq
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hAPos.det_pos)
  have hκ : κ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hβ)) (ne_of_gt hq)
  have hk : dot g (H.mulVec y) = κ := by
    have hs : dot g (H.mulVec y) = dot y (H.mulVec g) := by
      change g ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ g)
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymH.eq, dotProduct_comm]
    rw [hs]
    dsimp only [κ, β, q]
    field_simp [ne_of_gt hq]
  have hcomp : κ ^ 2 * D = A.det * ((κ - w) ^ 2 + u * (r - z)) :=
    CompressionDeterminant.compression_det A a b κ r hAunit hsymA hκ
  have hy : Dy = A.det * (r - z) := metricGram_det_append_one hH y Z hZ
  have hgy : Dgy = A.det * ((q - u) * (r - z) - (κ - w) ^ 2) := by
    have h := metricGram_det_append_two hH g y Z hZ
    change Dgy = A.det * ((q - u) * (r - z) - (dot g (H.mulVec y) - w) ^ 2) at h
    rwa [hk] at h
  have hid := CompressionAlgebra.compression_from_gram_relations
    A.det q u r z κ w D Dy Dgy hcomp hy hgy
  have hκsq : κ ^ 2 = β ^ 2 * q ^ 2 := by dsimp only [κ]; ring
  rw [hκsq] at hid
  have hupdate : (metricGram (inverseBFGS H (bfgsStep H g α) y) Z).det =
      D + α / (β * q) * A.det * u := by
    have h := inverseBFGS_compression H Z g y α hsymH
      (ne_of_gt hα) (ne_of_gt hq) (ne_of_gt hβ)
    change metricGram (inverseBFGS H (bfgsStep H g α) y) Z =
      CompressionDeterminant.compression A a b κ r + (α / (β * q)) • outer a a at h
    rw [h, CompressionDeterminant.compression_add_rank_one_det A a b κ r
      (α / (β * q)) hAunit hsymA]
  exact CompressionAlgebra.compressed_update_bound α β q A.det u D Dy Dgy
    (metricGram (inverseBFGS H (bfgsStep H g α) y) Z).det hα.le hβ hq hAPos.det_pos.le
    (compressed_energy_le hH g Z hZ)
    (metricGram_det_nonneg hH.posSemidef _ ) hid hupdate

/-- Reindexing compressed columns reindexes the actual Gram matrix. -/
theorem metricGram_submatrix_columns {n : ℕ} {ι κ : Type*}
    (H : Mat n) (Z : Matrix (Fin n) ι ℝ) (f : κ → ι) :
    metricGram H (Z.submatrix id f) = (metricGram H Z).submatrix f f := rfl

theorem metricGram_det_reindex {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (H : Mat n) (Z : Matrix (Fin n) ι ℝ) (e : κ ≃ ι) :
    (metricGram H (Z.submatrix id e)).det = (metricGram H Z).det := by
  rw [metricGram_submatrix_columns, Matrix.det_submatrix_equiv_self]

/-- The single-compression theorem for any finite coordinate index type,
    including the subtype of a principal-coordinate subset. -/
theorem compressed_inverseBFGS_bound_generic {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (H : Mat n) (Z : Matrix (Fin n) ι ℝ)
    (g y : Vec n) (α : ℝ) (hH : H.PosDef) (hZ : Function.Injective Z.mulVec)
    (hα : 0 < α) (hq : 0 < metricEnergy H g)
    (hβ : 0 < -dot y (H.mulVec g) / metricEnergy H g) :
    let q := metricEnergy H g
    let β := -dot y (H.mulVec g) / q
    (metricGram (inverseBFGS H (bfgsStep H g α) y) Z).det ≤
      (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y) Z)).det / (β ^ 2 * q) +
        α / β * (metricGram H Z).det := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Z' := Z.submatrix id e
  have hZ' : Function.Injective Z'.mulVec := by
    intro x y h
    have hxy : Z.mulVec (x ∘ e.symm) = Z.mulVec (y ∘ e.symm) := by
      simpa only [Z', Matrix.submatrix_mulVec_equiv, Function.comp_id] using h
    have hfun := hZ hxy
    funext i
    have hi := congrFun hfun (e i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi
  have hc : Matrix.fromCols (Matrix.replicateCol Unit y) Z' =
      (Matrix.fromCols (Matrix.replicateCol Unit y) Z).submatrix id
        (Equiv.sumCongr (Equiv.refl Unit) e) := by
    ext i j
    cases j <;> rfl
  have h := compressed_inverseBFGS_bound H Z' g y α hH hZ' hα hq hβ
  dsimp only at h ⊢
  rw [hc, metricGram_det_reindex] at h
  simpa only [Z', metricGram_det_reindex] using h

end BfgsVerification.BFGSCompression
