import BfgsVerification.PrincipalMinors

/-!
# Actual Gram matrices and Schur determinants

The larger Gram matrix is allowed to be singular. Only the compression on the
independent columns is inverted.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification

/-- Gram matrix in the metric specified by a real matrix. -/
def metricGram {n : ℕ} {ι : Type*} (H : Mat n) (X : Matrix (Fin n) ι ℝ) :
    Matrix ι ι ℝ := Xᵀ * H * X

/-- No independence hypothesis is needed for positive semidefiniteness. -/
theorem metricGram_posSemidef {n : ℕ} {ι : Type*} [Fintype ι]
    {H : Mat n} (hH : H.PosSemidef) (X : Matrix (Fin n) ι ℝ) :
    (metricGram H X).PosSemidef := by
  simpa only [metricGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.conjTranspose_mul_mul_same X

/-- An SPD metric remains SPD on independent columns, in arbitrary dimensions. -/
theorem metricGram_posDef {n : ℕ} {ι : Type*} [Fintype ι]
    {H : Mat n} (hH : H.PosDef) {X : Matrix (Fin n) ι ℝ}
    (hX : Function.Injective X.mulVec) : (metricGram H X).PosDef := by
  simpa only [metricGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.conjTranspose_mul_mul_same hX

/-- All actual Gram determinants, including singular ones, are nonnegative. -/
theorem metricGram_det_nonneg {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Mat n} (hH : H.PosSemidef) (X : Matrix (Fin n) ι ℝ) :
    0 ≤ (metricGram H X).det :=
  det_nonneg_of_posSemidef (metricGram_posSemidef hH X)

/-- The exact Schur determinant formula for appended columns. No inverse of the
full Gram matrix or the Schur complement occurs. -/
theorem metricGram_det_append {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {H : Mat n} (hH : H.PosDef) (Y : Matrix (Fin n) ι ℝ)
    (Z : Matrix (Fin n) κ ℝ) (hZ : Function.Injective Z.mulVec) :
    (metricGram H (Matrix.fromCols Y Z)).det =
      (metricGram H Z).det *
        (metricGram H Y - (Yᵀ * H * Z) * (metricGram H Z)⁻¹ * (Zᵀ * H * Y)).det := by
  letI : Invertible (Zᵀ * H * Z) := (metricGram_posDef hH hZ).isUnit.invertible
  unfold metricGram
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]

/-- The exact one-column Schur determinant identity, written with the actual
Gram matrix of the appended vector. -/
theorem metricGram_det_append_one {n j : ℕ} {H : Mat n} (hH : H.PosDef)
    (y : Vec n) (Z : Matrix (Fin n) (Fin j) ℝ)
    (hZ : Function.Injective Z.mulVec) :
    (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y) Z)).det =
      (metricGram H Z).det *
        (metricEnergy H y - dot (Zᵀ *ᵥ (H *ᵥ y))
          ((metricGram H Z)⁻¹ *ᵥ (Zᵀ *ᵥ (H *ᵥ y)))) := by
  rw [metricGram_det_append hH _ _ hZ]
  congr 1
  rw [Matrix.det_unique]
  have hs : Hᵀ = H := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using hH.isHermitian.eq
  let b := Zᵀ *ᵥ (H *ᵥ y)
  have hc : Zᵀ * H * Matrix.replicateCol Unit y = Matrix.replicateCol Unit b := by
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, ← Matrix.replicateCol_mulVec]
  have hr : (Matrix.replicateCol Unit y)ᵀ * H * Z = Matrix.replicateRow Unit b := by
    rw [← Matrix.transpose_replicateCol]
    rw [← hc]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  rw [hc, hr, Matrix.sub_apply]
  change ((Matrix.replicateCol Unit y)ᵀ * H * Matrix.replicateCol Unit y) () () -
    (Matrix.replicateRow Unit b * (metricGram H Z)⁻¹ * Matrix.replicateCol Unit b) () () = _
  simp only [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
    Matrix.transpose_replicateCol, Matrix.replicateRow_mul_replicateCol_apply]
  simp only [Matrix.replicateCol_apply, ← Matrix.mulVec_mulVec,
    Matrix.replicateRow_mulVec_eq_const]
  rfl

theorem metricGram_det_append_one_generic {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Mat n} (hH : H.PosDef)
    (y : Vec n) (Z : Matrix (Fin n) ι ℝ)
    (hZ : Function.Injective Z.mulVec) :
    (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y) Z)).det =
      (metricGram H Z).det *
        (metricEnergy H y - dotProduct (Zᵀ *ᵥ (H *ᵥ y))
          ((metricGram H Z)⁻¹ *ᵥ (Zᵀ *ᵥ (H *ᵥ y)))) := by
  rw [metricGram_det_append hH _ _ hZ]
  congr 1
  rw [Matrix.det_unique]
  have hs : Hᵀ = H := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using hH.isHermitian.eq
  let b := Zᵀ *ᵥ (H *ᵥ y)
  have hc : Zᵀ * H * Matrix.replicateCol Unit y = Matrix.replicateCol Unit b := by
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, ← Matrix.replicateCol_mulVec]
  have hr : (Matrix.replicateCol Unit y)ᵀ * H * Z = Matrix.replicateRow Unit b := by
    rw [← Matrix.transpose_replicateCol]
    rw [← hc]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  rw [hc, hr, Matrix.sub_apply]
  change ((Matrix.replicateCol Unit y)ᵀ * H * Matrix.replicateCol Unit y) () () -
    (Matrix.replicateRow Unit b * (metricGram H Z)⁻¹ * Matrix.replicateCol Unit b) () () = _
  simp only [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
    Matrix.transpose_replicateCol, Matrix.replicateRow_mul_replicateCol_apply]
  simp only [Matrix.replicateCol_apply, ← Matrix.mulVec_mulVec,
    Matrix.replicateRow_mulVec_eq_const]
  rfl

/-- Entries of the actual metric Gram matrix are the expected bilinear forms. -/
theorem metricGram_apply {n : ℕ} {ι : Type*} (H : Mat n)
    (X : Matrix (Fin n) ι ℝ) (i j : ι) :
    metricGram H X i j =
      dot (fun k => X k i) (H *ᵥ (fun k => X k j)) := by
  unfold metricGram
  rw [Matrix.mul_assoc]
  rfl

/-- The energy captured by independent compressed coordinates never exceeds
its energy in the full metric. This is derived from a possibly singular Gram. -/
theorem compressed_energy_le {n j : ℕ} {H : Mat n} (hH : H.PosDef)
    (g : Vec n) (Z : Matrix (Fin n) (Fin j) ℝ)
    (hZ : Function.Injective Z.mulVec) :
    dot (Zᵀ *ᵥ (H *ᵥ g)) ((metricGram H Z)⁻¹ *ᵥ (Zᵀ *ᵥ (H *ᵥ g))) ≤
      metricEnergy H g := by
  have hnon := metricGram_det_nonneg hH.posSemidef
    (Matrix.fromCols (Matrix.replicateCol Unit g) Z)
  rw [metricGram_det_append_one hH g Z hZ] at hnon
  have hpos := (metricGram_posDef hH hZ).det_pos
  nlinarith

/-- Entrywise version of the Schur complement in an actual Gram matrix. -/
theorem metricGram_schur_entry {n j : ℕ} {ι : Type*} [Fintype ι]
    {H : Mat n} (hH : H.PosDef) (Y : Matrix (Fin n) ι ℝ)
    (Z : Matrix (Fin n) (Fin j) ℝ) (i k : ι) :
    (metricGram H Y - (Yᵀ * H * Z) * (metricGram H Z)⁻¹ * (Zᵀ * H * Y)) i k =
      dot (fun l => Y l i) (H *ᵥ (fun l => Y l k)) -
        dot (Zᵀ *ᵥ (H *ᵥ (fun l => Y l i)))
          ((metricGram H Z)⁻¹ *ᵥ (Zᵀ *ᵥ (H *ᵥ (fun l => Y l k)))) := by
  have hs : Hᵀ = H := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using hH.isHermitian.eq
  have hcross : Yᵀ * H * Z = (Zᵀ * H * Y)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  rw [hcross, Matrix.sub_apply, metricGram_apply]
  congr 1
  change metricGram (metricGram H Z)⁻¹ (Zᵀ * H * Y) i k = _
  rw [metricGram_apply, Matrix.mul_assoc]
  rfl

/-- Two appended columns give exactly the two-by-two Schur determinant. -/
theorem metricGram_det_append_two {n j : ℕ} {H : Mat n} (hH : H.PosDef)
    (g y : Vec n) (Z : Matrix (Fin n) (Fin j) ℝ)
    (hZ : Function.Injective Z.mulVec) :
    let a := Zᵀ *ᵥ (H *ᵥ g)
    let b := Zᵀ *ᵥ (H *ᵥ y)
    let A := metricGram H Z
    (metricGram H (Matrix.fromCols (fun i k => ![g i, y i] k) Z)).det =
      A.det * ((metricEnergy H g - dot a (A⁻¹ *ᵥ a)) *
        (metricEnergy H y - dot b (A⁻¹ *ᵥ b)) -
          (dot g (H *ᵥ y) - dot a (A⁻¹ *ᵥ b)) ^ 2) := by
  dsimp only
  rw [metricGram_det_append hH _ _ hZ, Matrix.det_fin_two]
  simp only [metricGram_schur_entry hH, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_fin_one]
  have hs : Hᵀ = H := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using hH.isHermitian.eq
  have hsA : (metricGram H Z)⁻¹.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (metricGram_posDef hH hZ).inv.isHermitian.eq
  have hsym (M : Mat n) (hM : M.IsSymm) (v w : Vec n) :
      dot v (M *ᵥ w) = dot w (M *ᵥ v) := by
    change v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ v)
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]
  have hsymA (v w : Vec j) :
      dot v ((metricGram H Z)⁻¹ *ᵥ w) = dot w ((metricGram H Z)⁻¹ *ᵥ v) := by
    change v ⬝ᵥ ((metricGram H Z)⁻¹ *ᵥ w) = w ⬝ᵥ ((metricGram H Z)⁻¹ *ᵥ v)
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsA, dotProduct_comm]
  rw [hsym H hs y g, hsymA (Zᵀ *ᵥ (H *ᵥ y)) (Zᵀ *ᵥ (H *ᵥ g))]
  simp only [metricEnergy, pow_two]

end BfgsVerification
