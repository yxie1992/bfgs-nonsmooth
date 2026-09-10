import BfgsVerification.Definitions

noncomputable section
open scoped BigOperators
namespace BfgsVerification

/-- Inserting a fixed missing index embeds degree-j products into the next
principal-product sum. All omitted terms are nonnegative. -/
theorem insert_product_sum_le {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (j : ℕ) (k : Fin n) :
    (∑ I ∈ ((Finset.univ : Finset (Fin n)).powersetCard j).filter (fun I => k ∉ I),
      lam k * ∏ i ∈ I, lam i) ≤
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j + 1), ∏ i ∈ J, lam i := by
  classical
  let T := ((Finset.univ : Finset (Fin n)).powersetCard j).filter (fun I => k ∉ I)
  have hinj : ∀ I ∈ T, ∀ J ∈ T, insert k I = insert k J → I = J := by
    intro I hI J hJ heq
    have hi := (Finset.mem_filter.mp hI).2
    have hj := (Finset.mem_filter.mp hJ).2
    have := congrArg (fun L : Finset (Fin n) => L.erase k) heq
    simpa [Finset.erase_insert hi, Finset.erase_insert hj] using this
  have hsub : T.image (insert k) ⊆ (Finset.univ : Finset (Fin n)).powersetCard (j + 1) := by
    intro J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    have hi := Finset.mem_filter.mp hI
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_not_mem hi.2,
      (Finset.mem_powersetCard.mp hi.1).2]⟩
  calc
    _ = ∑ I ∈ T, ∏ i ∈ insert k I, lam i := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [Finset.prod_insert (Finset.mem_filter.mp hI).2]
    _ = ∑ J ∈ T.image (insert k), ∏ i ∈ J, lam i :=
      (Finset.sum_image (f := fun J : Finset (Fin n) => ∏ i ∈ J, lam i) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun J _ _ => Finset.prod_nonneg (fun i _ => hlam i))

/-- The eigenbasis combinatorial estimate, in arbitrary finite dimension. -/
theorem principal_product_augmented_sum_le {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (y : Vec n) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (∏ i ∈ I, lam i) * ∑ k ∈ Finset.univ \ I, lam k * y k ^ 2) ≤
      sqNorm y *
        ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j + 1), ∏ i ∈ J, lam i := by
  classical
  have hinner (I : Finset (Fin n)) :
      (∏ i ∈ I, lam i) * (∑ k ∈ Finset.univ \ I, lam k * y k ^ 2) =
        ∑ k : Fin n, if k ∉ I then y k ^ 2 * (lam k * ∏ i ∈ I, lam i) else 0 := by
    rw [Finset.mul_sum]
    have hf : (Finset.univ : Finset (Fin n)) \ I = Finset.univ.filter (fun k => k ∉ I) := by
      ext k
      simp
    rw [hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  simp_rw [hinner]
  rw [Finset.sum_comm]
  unfold sqNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  calc
    _ = y k ^ 2 *
        ∑ I ∈ ((Finset.univ : Finset (Fin n)).powersetCard j).filter (fun I => k ∉ I),
          lam k * ∏ i ∈ I, lam i := by
      rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ _ := mul_le_mul_of_nonneg_left (insert_product_sum_le lam hlam j k) (sq_nonneg _)

end BfgsVerification
