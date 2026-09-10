import BfgsVerification.Definitions
import BfgsVerification.ScalarHierarchy
import BfgsVerification.ReciprocalGrowth
import BfgsVerification.PrincipalMinors
import BfgsVerification.QuantitativeGrowth

/-!
Matrix estimates used in normalizing Module M. The modular implications here
are instantiated with the proved principal-minor theorem in `EndToEnd.lean`.
-/

noncomputable section
open scoped BigOperators
open Matrix Filter

namespace BfgsVerification

theorem sqNorm_nonneg {n : ℕ} (g : Vec n) : 0 ≤ sqNorm g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqNorm_sub_le {n : ℕ} (g h : Vec n) :
    sqNorm (g - h) ≤ 2 * sqNorm g + 2 * sqNorm h := by
  unfold sqNorm
  simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (g i + h i)]

/-- The energy/trace estimate follows from a PSD square root and finite
Cauchy--Schwarz. It imposes no uniform spectral bound on the matrix. -/
theorem metricEnergy_le_sqNorm_mul_trace {n : ℕ} (H : Mat n) (g : Vec n)
    (hH : H.PosSemidef) : metricEnergy H g ≤ sqNorm g * H.trace := by
  obtain ⟨B, rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hH
  have he : metricEnergy (Bᴴ * B) g = ∑ i, (∑ j, B i j * g j) ^ 2 := by
    unfold metricEnergy dot
    change g ⬝ᵥ ((Bᴴ * B) *ᵥ g) = _
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]
    simp only [vecMul_conjTranspose, star_trivial]
    simp only [dotProduct, Matrix.mulVec, pow_two]
  have ht : (Bᴴ * B).trace = ∑ i, ∑ j, (B i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, star_trivial, pow_two]
    exact Finset.sum_comm
  rw [he, ht]
  calc
    (∑ i, (∑ j, B i j * g j) ^ 2) ≤
        ∑ i, (∑ j, (B i j) ^ 2) * sqNorm g := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (B i) g
    _ = sqNorm g * ∑ i, ∑ j, (B i j) ^ 2 := by
      rw [← Finset.sum_mul, mul_comm]

theorem FullBFGSRun.dimension_pos {n : ℕ} (R : FullBFGSRun n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  have h := R.energy_pos 0
  simpa [metricEnergy, dot] using h

theorem FullBFGSRun.d_pos {n : ℕ} (R : FullBFGSRun n) (k : ℕ) : 0 < R.d k :=
  mul_pos (R.alpha_pos k) (R.energy_pos k)

/-- Modular normalization on actual matrices. `EndToEnd.lean` supplies the
matrix-hierarchy premise using the proved `principalMinorHierarchy`. -/
theorem normalizedHierarchy_of_principalMinorHierarchy
    (hminor : PrincipalMinorHierarchyTarget)
    {n : ℕ} (R : FullBFGSRun n) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (hβ : ∀ k, c ≤ R.beta k) :
    ScalarHierarchy.NormalizedHierarchy n (fun k => principalSum (R.H k))
      R.q (fun k => R.d k / c) (4 * G ^ 2 / c ^ 2) (G ^ 2) := by
  have hn := R.dimension_pos
  refine ⟨hn, R.energy_pos, by positivity, by positivity,
    fun k => principalSum_nonneg (R.positive_definite k).posSemidef,
    fun k => principalSum_one_pos (R.positive_definite k) hn,
    fun k => principalSum_terminal (R.H k), ?_, ?_⟩
  · intro k
    rw [principalSum_one]
    exact (metricEnergy_le_sqNorm_mul_trace (R.H k) (R.g k)
      (R.positive_definite k).posSemidef).trans
        (mul_le_mul_of_nonneg_right (hg k) (trace_pos_of_posDef
          (R.positive_definite k) hn).le)
  · intro k j hj hjn
    have hq : 0 < R.q k := R.energy_pos k
    have hb : 0 < R.beta k := hc.trans_le (hβ k)
    have hy : sqNorm (R.g (k + 1) - R.g k) ≤ 4 * G ^ 2 := by
      have := sqNorm_sub_le (R.g (k + 1)) (R.g k)
      linarith [hg (k + 1), hg k]
    have he := principalSum_nonneg (R.positive_definite k).posSemidef
    have hh := hminor n (R.H k) (R.g k) (R.g (k + 1) - R.g k)
      (R.α k) (R.positive_definite k) (R.alpha_pos k) hq hb j hj hjn
    change principalSum (inverseBFGS (R.H k)
      (bfgsStep (R.H k) (R.g k) (R.α k)) (R.g (k + 1) - R.g k)) j ≤
      sqNorm (R.g (k + 1) - R.g k) / ((R.beta k) ^ 2 * R.q k) *
        principalSum (R.H k) (j + 1) +
      R.α k / R.beta k * principalSum (R.H k) j at hh
    rw [← R.update k] at hh
    have ha : sqNorm (R.g (k + 1) - R.g k) / (R.beta k) ^ 2 ≤
        4 * G ^ 2 / c ^ 2 := by
      have hsq : c ^ 2 ≤ (R.beta k) ^ 2 := by nlinarith [hβ k]
      exact (div_le_div_of_nonneg_right hy (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 * G ^ 2)
          (by positivity : 0 < c ^ 2) hsq)
    have hd : R.d k / R.beta k ≤ R.d k / c :=
      div_le_div_of_nonneg_left (R.d_pos k).le hc (hβ k)
    calc
      R.q k * principalSum (R.H (k + 1)) j ≤ R.q k *
          (sqNorm (R.g (k + 1) - R.g k) / ((R.beta k) ^ 2 * R.q k) *
            principalSum (R.H k) (j + 1) +
          R.α k / R.beta k * principalSum (R.H k) j) :=
        mul_le_mul_of_nonneg_left hh hq.le
      _ = (sqNorm (R.g (k + 1) - R.g k) / (R.beta k) ^ 2) *
          principalSum (R.H k) (j + 1) +
          (R.d k / R.beta k) * principalSum (R.H k) j := by
        unfold FullBFGSRun.d
        field_simp
        <;> ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right ha (he (j + 1)))
        (mul_le_mul_of_nonneg_right hd (he j))

/-- Modular implication; the matrix premise is discharged in `EndToEnd.lean`. -/
theorem reciprocalGrowth_of_principalMinorHierarchy
    (hminor : PrincipalMinorHierarchyTarget) : ReciprocalGrowthTarget := by
  intro n R G c hG hc hg hβ hd
  apply ReciprocalGrowth.hierarchy_reciprocal_growth
    (normalizedHierarchy_of_principalMinorHierarchy hminor R G c hG hc hg hβ)
  apply ScalarHierarchy.upperNull_of_tendsto
  simpa using hd.div_const c

/-- Modular summable-budget conclusion, instantiated in `EndToEnd.lean`. -/
theorem superquadraticGrowth_of_principalMinorHierarchy
    (hminor : PrincipalMinorHierarchyTarget) : SuperquadraticReciprocalTarget := by
  intro n R G c hG hc hg hβ hd
  exact QuantitativeGrowth.hierarchy_superquadratic_growth
    (normalizedHierarchy_of_principalMinorHierarchy hminor R G c hG hc hg hβ)
    (fun k => (div_pos (R.d_pos k) hc).le) (hd.div_const c)

/-- The source's finite-horizon bound, with actual matrices and the actual tail
budget. The block length is `m+1`, so `0<m` is exactly the source's length ≥2.
The matrix-hierarchy premise is discharged in the exported `finiteHorizon`. -/
theorem finiteHorizon_of_principalMinorHierarchy
    (hminor : PrincipalMinorHierarchyTarget)
    {n : ℕ} (R : FullBFGSRun n) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (hβ : ∀ k, c ≤ R.beta k)
    (hd : Summable R.d) (J m : ℕ) (hm : 0 < m) (η : ℝ) (hη : 0 < η) :
    let D := ∑' i : ℕ, R.d (J + i)
    let V := ScalarHierarchy.weightedPotential n ((4 * G ^ 2 / c ^ 2) / η)
      (principalSum (R.H J))
    ((m + 1 : ℕ) : ℝ) * (G ^ 2 * V) ^ (-1 / ((m + 1 : ℕ) : ℝ)) *
      (η + D / (c * (m : ℝ))) ^ (-(m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range (m + 1), (R.q (J + i))⁻¹ := by
  dsimp only
  have htail : Summable (fun i => R.d (J + i)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff J).2 hd
  have hbudget : (∑ i ∈ Finset.range m, R.d (J + i) / c) ≤
      (∑' i : ℕ, R.d (J + i)) / c := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (htail.sum_le_tsum _ (fun i _ => (R.d_pos (J + i)).le)) hc.le
  have hD : 0 ≤ (∑' i : ℕ, R.d (J + i)) / c :=
    div_nonneg (tsum_nonneg (fun i => (R.d_pos (J + i)).le)) hc.le
  have h := QuantitativeGrowth.hierarchy_finite_horizon_rpow
    (normalizedHierarchy_of_principalMinorHierarchy hminor R G c hG hc hg hβ)
    (fun k => (div_pos (R.d_pos k) hc).le) J m hm η _ hη hD hbudget
  simpa only [div_div] using h

end BfgsVerification
