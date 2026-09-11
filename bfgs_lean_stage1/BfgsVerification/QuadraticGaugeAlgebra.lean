import BfgsVerification.AffineImageLifting
import BfgsVerification.HomogeneousCardinality

/-! Exact finite-coordinate splitting and quadratic algebra for F's gauge rate. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace QuadraticGauge

def left {m p : ℕ} (x : Vec (m + p)) : Vec m := fun i => x (Fin.castAdd p i)
def right {m p : ℕ} (x : Vec (m + p)) : Vec p := fun i => x (Fin.natAdd m i)

def objective {m p : ℕ} (Q : Mat m) (γ : Vec p → ℝ) (x : Vec (m + p)) : ℝ :=
  metricEnergy Q (left x) / 2 + γ (right x)

@[simp] theorem left_append {m p : ℕ} (u : Vec m) (v : Vec p) : left (Fin.append u v) = u := by
  ext i
  exact Fin.append_left u v i
@[simp] theorem right_append {m p : ℕ} (u : Vec m) (v : Vec p) : right (Fin.append u v) = v := by
  ext i
  exact Fin.append_right u v i
@[simp] theorem left_sub {m p : ℕ} (x y : Vec (m + p)) : left (x - y) = left x - left y := rfl
@[simp] theorem right_sub {m p : ℕ} (x y : Vec (m + p)) : right (x - y) = right x - right y := rfl

theorem dot_split {m p : ℕ} (x y : Vec (m + p)) :
    dot x y = dot (left x) (left y) + dot (right x) (right y) := by
  unfold dot
  exact Fin.sum_univ_add _

theorem quadratic_hasGradient {m : ℕ} (Q : Mat m) (hQ : Q.IsSymm) (x : Vec m) :
    HasFDerivAt (fun z => metricEnergy Q z / 2) (gradientFunctional (Q.mulVec x)) x := by
  have hcoord (i : Fin m) : HasFDerivAt (fun z : Vec m => z i * (Q.mulVec z) i)
      (x i • (ContinuousLinearMap.proj i).comp (AffineProjection.matrixCLM Q) +
        (Q.mulVec x) i • ContinuousLinearMap.proj i) x := by
    have h1 : HasFDerivAt (fun z : Vec m => z i) (ContinuousLinearMap.proj i) x :=
      (ContinuousLinearMap.proj i : Vec m →L[ℝ] ℝ).hasFDerivAt
    have h2 : HasFDerivAt (fun z : Vec m => (Q.mulVec z) i)
        ((ContinuousLinearMap.proj i).comp (AffineProjection.matrixCLM Q)) x := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, AffineProjection.matrixCLM_apply] using
        (ContinuousLinearMap.proj i : Vec m →L[ℝ] ℝ).hasFDerivAt.comp x
          (AffineProjection.matrixCLM Q).hasFDerivAt
    exact h1.mul h2
  have h := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => hcoord i)).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext z
    unfold metricEnergy dot
    ring
  · ext v
    simp only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, AffineProjection.matrixCLM_apply, smul_eq_mul,
      gradientFunctional_apply, Finset.sum_add_distrib]
    change dot (Q.mulVec x) v = (1 / 2 : ℝ) * (dot x (Q.mulVec v) + dot (Q.mulVec x) v)
    rw [← AffineProjection.dot_transpose_mulVec Q x v, hQ.eq]
    ring

theorem metricEnergy_nonneg {m : ℕ} {Q : Mat m} (hQ : Q.PosSemidef) (x : Vec m) :
    0 ≤ metricEnergy Q x := by
  simpa only [metricEnergy, dot, dotProduct, star_trivial] using hQ.2 x

/-- PSD Cauchy–Schwarz for the actual quadratic form. -/
theorem metric_cauchy_schwarz {m : ℕ} {Q : Mat m} (hQ : Q.PosSemidef) (x y : Vec m) :
    (dot (Q.mulVec x) y) ^ 2 ≤ metricEnergy Q x * metricEnergy Q y := by
  obtain ⟨A, hA⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hQ
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hA
  rw [hA]
  have he (v : Vec m) : metricEnergy (Aᵀ * A) v = sqNorm (A.mulVec v) := by
    unfold metricEnergy
    rw [← Matrix.mulVec_mulVec, show dot v (Aᵀ.mulVec (A.mulVec v)) =
      dot (Aᵀ.mulVec (A.mulVec v)) v from dotProduct_comm _ _, AffineProjection.dot_transpose_mulVec]
    simp only [dot, sqNorm, pow_two]
  rw [he, he, ← Matrix.mulVec_mulVec, AffineProjection.dot_transpose_mulVec]
  exact dot_sq_le_sqNorm_mul_sqNorm _ _

/-- Two-term weighted Cauchy–Schwarz, including either zero weight. -/
theorem weighted_square_bound {a b ξ ζ U W : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hξ : ξ ^ 2 ≤ a * U) (hζ : ζ ^ 2 ≤ b * W) :
    (ξ + ζ) ^ 2 ≤ (a + b) * (U + W) := by
  by_cases ha0 : a = 0
  · have hξ0 : ξ = 0 := by rw [ha0] at hξ; nlinarith [sq_nonneg ξ]
    rw [ha0, hξ0]
    nlinarith [mul_nonneg hb hU]
  by_cases hb0 : b = 0
  · have hζ0 : ζ = 0 := by rw [hb0] at hζ; nlinarith [sq_nonneg ζ]
    rw [hb0, hζ0]
    nlinarith [mul_nonneg ha hW]
  have hab : 0 < a * b := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0))
  apply (mul_le_mul_left hab).mp
  have h1 := mul_le_mul_of_nonneg_left hξ (mul_nonneg hb (add_nonneg ha hb))
  have h2 := mul_le_mul_of_nonneg_left hζ (mul_nonneg ha (add_nonneg ha hb))
  nlinarith [sq_nonneg (b * ξ - a * ζ)]

end QuadraticGauge
end BfgsVerification
