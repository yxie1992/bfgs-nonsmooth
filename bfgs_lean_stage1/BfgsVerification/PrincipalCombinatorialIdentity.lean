import BfgsVerification.PrincipalHierarchy

noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification

/-- Exact insertion/erasure identity, with no sign assumption on the factors. -/
theorem insert_product_sum_eq {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) (k : Fin n) :
    (∑ I ∈ ((Finset.univ : Finset (Fin n)).powersetCard j).filter (fun I => k ∉ I),
      lam k * ∏ i ∈ I, lam i) =
    ∑ J ∈ ((Finset.univ : Finset (Fin n)).powersetCard (j + 1)).filter (fun J => k ∈ J),
      ∏ i ∈ J, lam i := by
  classical
  let T := ((Finset.univ : Finset (Fin n)).powersetCard j).filter (fun I => k ∉ I)
  have hinj : ∀ I ∈ T, ∀ J ∈ T, insert k I = insert k J → I = J := by
    intro I hI J hJ heq
    have hi := (Finset.mem_filter.mp hI).2
    have hj := (Finset.mem_filter.mp hJ).2
    have := congrArg (fun L : Finset (Fin n) => L.erase k) heq
    simpa [Finset.erase_insert hi, Finset.erase_insert hj] using this
  have himage : T.image (insert k) =
      ((Finset.univ : Finset (Fin n)).powersetCard (j + 1)).filter (fun J => k ∈ J) := by
    ext J
    constructor
    · intro hJ
      obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
      have hi := Finset.mem_filter.mp hI
      exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_not_mem hi.2,
          (Finset.mem_powersetCard.mp hi.1).2]⟩, Finset.mem_insert_self _ _⟩
    · intro hJ
      have hj := Finset.mem_filter.mp hJ
      refine Finset.mem_image.mpr ⟨J.erase k, ?_, Finset.insert_erase hj.2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hj.2,
          (Finset.mem_powersetCard.mp hj.1).2]; omega⟩, Finset.not_mem_erase _ _⟩
  calc
    _ = ∑ I ∈ T, ∏ i ∈ insert k I, lam i := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [Finset.prod_insert (Finset.mem_filter.mp hI).2]
    _ = ∑ J ∈ T.image (insert k), ∏ i ∈ J, lam i :=
      (Finset.sum_image (f := fun J : Finset (Fin n) => ∏ i ∈ J, lam i) hinj).symm
    _ = _ := by rw [himage]

/-- The literal double-sum equality displayed in Module M94–99. -/
theorem principal_product_augmented_sum_eq {n : ℕ} (lam : Fin n → ℝ)
    (y : Vec n) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (∏ i ∈ I, lam i) * ∑ k ∈ Finset.univ \ I, lam k * y k ^ 2) =
    ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j + 1),
      (∏ i ∈ J, lam i) * ∑ k ∈ J, y k ^ 2 := by
  classical
  have hleft (I : Finset (Fin n)) :
      (∏ i ∈ I, lam i) * (∑ k ∈ Finset.univ \ I, lam k * y k ^ 2) =
      ∑ k : Fin n, if k ∉ I then y k ^ 2 * (lam k * ∏ i ∈ I, lam i) else 0 := by
    rw [Finset.mul_sum]
    have hf : (Finset.univ : Finset (Fin n)) \ I = Finset.univ.filter (fun k => k ∉ I) := by
      ext k; simp
    rw [hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  have hright (J : Finset (Fin n)) :
      (∏ i ∈ J, lam i) * (∑ k ∈ J, y k ^ 2) =
      ∑ k : Fin n, if k ∈ J then y k ^ 2 * (∏ i ∈ J, lam i) else 0 := by
    rw [Finset.mul_sum]
    have hf : J = Finset.univ.filter (fun k : Fin n => k ∈ J) := by ext k; simp
    conv_lhs => arg 1; rw [hf]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  simp_rw [hleft, hright]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin n)).powersetCard (j+1))]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun t : ℝ => y k ^ 2 * t) (insert_product_sum_eq lam j k)
  simpa only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero] using h

/-- Actual augmented principal Gram determinants equal the source's weighted
elementary-product sum, for every dimension and degree. -/
theorem diagonal_coordinate_gram_sum_eq {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (y : Vec n) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (metricGram (Matrix.diagonal lam)
        (Matrix.fromCols (Matrix.replicateCol Unit y) (coordinateMatrix I))).det) =
    ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
      (∏ i ∈ J, lam i) * ∑ k ∈ J, y k ^ 2 := by
  classical
  simp_rw [diagonal_coordinate_gram_det lam hlam y]
  exact principal_product_augmented_sum_eq lam y j

/-- The equality for actual Gram matrices in the original matrix coordinates,
using an actual orthogonal diagonalization rather than assumed scalar data. -/
theorem orthogonal_coordinate_gram_sum_eq {n : ℕ} (H U : Mat n) (lam : Vec n)
    (hU : U * Uᵀ = 1) (hdiag : Uᵀ * H * U = Matrix.diagonal lam)
    (hlam : ∀ i, 0 < lam i) (y : Vec n) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
        (U * coordinateMatrix I))).det) =
    ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
      (∏ i ∈ J, lam i) * ∑ k ∈ J, (Uᵀ.mulVec y) k ^ 2 := by
  classical
  simp_rw [metricGram_append_orthogonal H U hU y, hdiag]
  exact diagonal_coordinate_gram_sum_eq lam hlam (Uᵀ.mulVec y) j

/-- Literal Module M eigenbasis identity, with the eigenbasis constructed from
the actual SPD matrix and no scalar or determinant identity hypothesis. -/
def PrincipalGramSumIdentityTarget : Prop := ∀ {n : ℕ} (H : Mat n), H.PosDef →
  ∃ (U : Mat n) (lam : Vec n), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
    Uᵀ * H * U = Matrix.diagonal lam ∧ (∀ i, 0 < lam i) ∧
    ∀ (y : Vec n) (j : ℕ),
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
          (U * coordinateMatrix I))).det) =
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
        (∏ i ∈ J, lam i) * ∑ k ∈ J, (Uᵀ.mulVec y) k ^ 2

theorem principalGramSumIdentity : PrincipalGramSumIdentityTarget := by
  intro n H hH
  obtain ⟨U,lam,hUL,hUR,hdiag,hlam⟩ := posDef_orthogonal_diagonalization hH
  exact ⟨U,lam,hUL,hUR,hdiag,hlam,orthogonal_coordinate_gram_sum_eq H U lam hUR hdiag hlam⟩

end BfgsVerification
