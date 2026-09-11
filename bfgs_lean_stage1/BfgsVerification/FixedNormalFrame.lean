import BfgsVerification.FixedNormalProjection
import BfgsVerification.ResidualFrames

/-! The exact fixed-normal cutoff frame and its zero-safe transport residual.
The normal column is written first, a fixed permutation of the source frame. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix

namespace BfgsVerification
namespace FixedNormal

def cutoffFrame {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (a : Vec n)
    (t : ℝ) : Matrix (Fin n) (Fin (r + 1)) ℝ :=
  fun i => Fin.cons (t * a i) (U i)

def cutoffSlope (τ : ℝ → ℝ) (u v : ℝ) : ℝ :=
  if v = u then 0 else (τ v - τ u) / (v - u)

def normalCoefficient {r : ℕ} (β : ℝ) : Vec (r + 1) := Pi.single 0 β

def cutoffResidual {n r : ℕ} (a s : Vec n) (β : ℝ) :
    Matrix (Fin n) (Fin (r + 1)) ℝ :=
  EnergyIdentities.rectOuter (tangentProjection a s) (normalCoefficient (-β))

theorem cutoffSlope_mul (τ : ℝ → ℝ) (u v : ℝ) :
    cutoffSlope τ u v * (v - u) = τ v - τ u := by
  by_cases h : v = u
  · simp [cutoffSlope, h]
  · simp [cutoffSlope, h, sub_ne_zero.mpr h]

theorem abs_cutoffSlope_le {τ : ℝ → ℝ} {L : ℝ≥0} (hτ : LipschitzWith L τ) (u v : ℝ) :
    |cutoffSlope τ u v| ≤ L := by
  by_cases h : v = u
  · simp [cutoffSlope, h]
  · rw [cutoffSlope, if_neg h, abs_div]
    apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr h))).mpr
    simpa only [Real.norm_eq_abs] using hτ.norm_sub_le v u

theorem cutoffFrame_pairing {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (a g : Vec n) (t : ℝ) :
    sqNorm ((cutoffFrame U a t)ᵀ.mulVec g) = sqNorm (Uᵀ.mulVec g) + t ^ 2 * (dot a g) ^ 2 := by
  have he : (cutoffFrame U a t)ᵀ.mulVec g =
      Fin.cons (t * dot a g) (Uᵀ.mulVec g) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Matrix.mulVec, dotProduct, transpose_apply, cutoffFrame, Fin.cons_zero,
        dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [Matrix.mulVec, dotProduct, transpose_apply, cutoffFrame, Fin.cons_succ]
  rw [he]
  simp only [sqNorm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_pow]
  ring

theorem cutoffResidual_frobSq {n r : ℕ} (a s : Vec n) (β : ℝ) :
    SmoothSubspace.frobSq (cutoffResidual (r := r) a s β) =
      β ^ 2 * sqNorm (tangentProjection a s) := by
  simp only [SmoothSubspace.frobSq, cutoffResidual, EnergyIdentities.rectOuter,
    normalCoefficient, Fin.sum_univ_succ, Pi.single_eq_same,
    Pi.single_eq_of_ne (Fin.succ_ne_zero _), mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, mul_pow, neg_sq, sqNorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact source transport formula, including pairs with zero normal increment. -/
theorem cutoffFrame_transport {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (a x z : Vec n) (b : ℝ) (τ : ℝ → ℝ) :
    let β := cutoffSlope τ (dot a x - b) (dot a z - b)
    cutoffFrame U a (τ (dot a z - b)) =
      cutoffFrame U a (τ (dot a x - b)) * (1 : Mat (r + 1)) +
      EnergyIdentities.rectOuter (z - x) (normalCoefficient β) +
      cutoffResidual a (z - x) β := by
  dsimp only
  let β := cutoffSlope τ (dot a x - b) (dot a z - b)
  have hd : β * dot a (z - x) = τ (dot a z - b) - τ (dot a x - b) := by
    have h := cutoffSlope_mul τ (dot a x - b) (dot a z - b)
    change β * ((dot a z - b) - (dot a x - b)) = _ at h
    change β * dotProduct a (z - x) = _
    rw [dotProduct_sub]
    simp only [dot, dotProduct] at h ⊢
    convert h using 1 <;> ring
  ext i j
  rw [Matrix.mul_one]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Matrix.add_apply, cutoffFrame, Fin.cons_zero, EnergyIdentities.rectOuter,
      normalCoefficient, Pi.single_eq_same, cutoffResidual, tangentProjection,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hi := congrArg (fun v : ℝ => v * a i) hd
    dsimp only [β] at hi
    nlinarith
  · simp only [Matrix.add_apply, cutoffFrame, Fin.cons_succ, EnergyIdentities.rectOuter,
      normalCoefficient, Pi.single_eq_of_ne (Fin.succ_ne_zero _), cutoffResidual,
      mul_zero, add_zero]

/-- Every residual column lies in the actual fixed tangent subspace. -/
theorem cutoffResidual_tangential {n r : ℕ} {a : Vec n} (ha : sqNorm a = 1)
    (U : Matrix (Fin n) (Fin r) ℝ)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = tangentProjection a v)
    (s : Vec n) (β : ℝ) :
    (U * Uᵀ) * cutoffResidual (r := r) a s β = cutoffResidual a s β := by
  ext i j
  have hfix := hproj (tangentProjection a s)
  rw [tangentProjection_eq_self (tangentProjection_normal_zero ha s)] at hfix
  have hi := congrFun hfix i
  change (∑ k, (U * Uᵀ) i k *
    (tangentProjection a s k * normalCoefficient (r := r) (-β) j)) =
      tangentProjection a s i * normalCoefficient (-β) j
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  exact congrArg (fun t : ℝ => t * normalCoefficient (r := r) (-β) j) hi

/-- The Lipschitz cutoff and the actual tangential displacement give the source
Frobenius residual bound; no metric-growth or energy premise occurs. -/
theorem cutoffResidual_bound {n r : ℕ} {a : Vec n} (ha : sqNorm a = 1)
    {τ : ℝ → ℝ} {L : ℝ≥0} (hτ : LipschitzWith L τ) (x z : Vec n) (b : ℝ) :
    SmoothSubspace.frobSq (cutoffResidual (r := r) a (z - x)
      (cutoffSlope τ (dot a x - b) (dot a z - b))) ≤
      (L : ℝ) ^ 2 * sqNorm (z - x) := by
  rw [cutoffResidual_frobSq]
  have hb : (cutoffSlope τ (dot a x - b) (dot a z - b)) ^ 2 ≤ (L : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr
      (abs_cutoffSlope_le hτ _ _)
  exact mul_le_mul hb (sqNorm_tangentProjection_le ha _) (sqNorm_nonneg _) (sq_nonneg _)

end FixedNormal
end BfgsVerification
