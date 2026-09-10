import Mathlib

/-!
# Scalar algebra in the principal-minor compression proof

STATUS: compiler-checked scalar algebra.
These are real-algebra lemmas. The actual determinant identities and their use
for BFGS matrices are proved separately in `CompressionDeterminant.lean`,
`GramSchur.lean`, and `BFGSCompression.lean`.
-/

noncomputable section
open scoped BigOperators

namespace BfgsVerification.CompressionAlgebra

/-- The scalar cancellation relating the two Schur-complement expressions. -/
theorem gram_numerator_identity (Δ q u r z κ w : ℝ) :
    q * (Δ * (r - z)) -
        Δ * ((q - u) * (r - z) - (κ - w) ^ 2) =
      Δ * ((κ - w) ^ 2 + u * (r - z)) := by
  ring

/-- The same cancellation after division by the squared denominator. -/
theorem compression_scalar_identity (Δ q u r z κ w : ℝ) :
    Δ / κ ^ 2 * ((κ - w) ^ 2 + u * (r - z)) =
      (q * (Δ * (r - z)) -
        Δ * ((q - u) * (r - z) - (κ - w) ^ 2)) / κ ^ 2 := by
  simp only [div_eq_mul_inv]
  ring

/-- The cross-multiplied form avoids cancellation at an unspecified denominator. -/
theorem compression_from_gram_relations
    (Δ q u r z κ w D Dy Dgy : ℝ)
    (hcompression : κ ^ 2 * D = Δ * ((κ - w) ^ 2 + u * (r - z)))
    (hDy : Dy = Δ * (r - z))
    (hDgy : Dgy = Δ * ((q - u) * (r - z) - (κ - w) ^ 2)) :
    κ ^ 2 * D = q * Dy - Dgy := by
  rw [hcompression, hDy, hDgy]
  ring

/-- Dropping a nonnegative larger Gram determinant gives the compression bound. -/
theorem compression_upper_bound
    (q β D Dy Dgy : ℝ)
    (hq : 0 < q) (hβ : 0 < β) (hDgy : 0 ≤ Dgy)
    (hid : β ^ 2 * q ^ 2 * D = q * Dy - Dgy) :
    D ≤ Dy / (β ^ 2 * q) := by
  apply (le_div_iff₀ (by positivity : 0 < β ^ 2 * q)).2
  have hnum : q * (D * (β ^ 2 * q)) ≤ q * Dy := by
    nlinarith [hid]
  exact (mul_le_mul_left hq).mp hnum

/-- An explicit positivity assumption on alpha is required for this bound. -/
theorem rank_one_increment_upper_bound
    (α β q Δ u : ℝ)
    (hα : 0 ≤ α) (hβ : 0 < β) (hq : 0 < q)
    (hΔ : 0 ≤ Δ) (hu : u ≤ q) :
    α / (β * q) * Δ * u ≤ α / β * Δ := by
  calc
    α / (β * q) * Δ * u ≤ α / (β * q) * Δ * q :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = α / β * Δ := by
      field_simp [ne_of_gt hβ, ne_of_gt hq]
      <;> ring

/-- One compressed determinant bound, once the matrix identities are supplied. -/
theorem compressed_update_bound
    (α β q Δ u D Dy Dgy Dplus : ℝ)
    (hα : 0 ≤ α) (hβ : 0 < β) (hq : 0 < q)
    (hΔ : 0 ≤ Δ) (hu : u ≤ q) (hDgy : 0 ≤ Dgy)
    (hid : β ^ 2 * q ^ 2 * D = q * Dy - Dgy)
    (hupdate : Dplus = D + α / (β * q) * Δ * u) :
    Dplus ≤ Dy / (β ^ 2 * q) + α / β * Δ := by
  rw [hupdate]
  exact add_le_add
    (compression_upper_bound q β D Dy Dgy hq hβ hDgy hid)
    (rank_one_increment_upper_bound α β q Δ u hα hβ hq hΔ hu)

/-- Finite summation step. The spectral/principal-minor identification is NOT
    assumed to have been proved by this scalar lemma. -/
theorem sum_compressed_bounds
    {ι : Type*} [Fintype ι]
    (Dplus Dy Δ : ι → ℝ) (α β q normY2 eNext eCurrent : ℝ)
    (hβ : 0 < β) (hq : 0 < q)
    (hpoint : ∀ i, Dplus i ≤ Dy i / (β ^ 2 * q) + α / β * Δ i)
    (hgram : (∑ i, Dy i) ≤ normY2 * eNext)
    (hprincipal : (∑ i, Δ i) = eCurrent) :
    (∑ i, Dplus i) ≤ normY2 / (β ^ 2 * q) * eNext + α / β * eCurrent := by
  calc
    (∑ i, Dplus i) ≤ ∑ i, (Dy i / (β ^ 2 * q) + α / β * Δ i) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i, Dy i) / (β ^ 2 * q) + α / β * eCurrent := by
      simp only [Finset.sum_add_distrib, Finset.sum_div,
        ← Finset.mul_sum, hprincipal]
    _ ≤ (normY2 * eNext) / (β ^ 2 * q) + α / β * eCurrent := by
      exact add_le_add_right
        (div_le_div_of_nonneg_right hgram (by positivity)) _
    _ = normY2 / (β ^ 2 * q) * eNext + α / β * eCurrent := by ring

end BfgsVerification.CompressionAlgebra
