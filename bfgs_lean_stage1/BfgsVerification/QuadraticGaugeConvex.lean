import BfgsVerification.QuadraticGaugeDerivatives

/-! The source model is itself finite convex whenever its gauge is finite convex.
This independently supplies the objective convexity in the actual run definition. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace QuadraticGauge

theorem metricEnergy_gram {m : ℕ} (A : Mat m) (v : Vec m) :
    metricEnergy (Aᵀ * A) v = sqNorm (A.mulVec v) := by
  unfold metricEnergy
  rw [← Matrix.mulVec_mulVec, show dot v (Aᵀ.mulVec (A.mulVec v)) =
    dot (Aᵀ.mulVec (A.mulVec v)) v from dotProduct_comm _ _, AffineProjection.dot_transpose_mulVec]
  simp only [dot, sqNorm, pow_two]

theorem quadratic_convex {m : ℕ} (Q : Mat m) (hQ : Q.PosSemidef) :
    ConvexOn ℝ univ (fun u => metricEnergy Q u / 2) := by
  obtain ⟨A, hA⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hQ
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hA
  rw [hA]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hcoord (i : Fin m) :
      (a * (A.mulVec x) i + b * (A.mulVec y) i) ^ 2 ≤
        a * (A.mulVec x) i ^ 2 + b * (A.mulVec y) i ^ 2 := by
    have hid (t u : ℝ) :
        (a * t + b * u) ^ 2 + a * b * (t - u) ^ 2 =
          (a + b) * (a * t ^ 2 + b * u ^ 2) := by ring
    have hi := hid ((A.mulVec x) i) ((A.mulVec y) i)
    rw [hab, one_mul] at hi
    nlinarith only [hi, mul_nonneg (mul_nonneg ha hb)
      (sq_nonneg ((A.mulVec x) i - (A.mulVec y) i))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [metricEnergy_gram, sqNorm, Matrix.mulVec_add, Matrix.mulVec_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Convexity of the actual split objective follows from PSD Q and finite convex γ. -/
theorem objective_convex {m p : ℕ} (Q : Mat m) (hQ : Q.PosSemidef)
    (γ : Vec p → ℝ) (hγ : ConvexOn ℝ univ γ) :
    ConvexOn ℝ univ (objective Q γ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hu := (quadratic_convex Q hQ).2 (mem_univ (left x)) (mem_univ (left y)) ha hb hab
  have hv := hγ.2 (mem_univ (right x)) (mem_univ (right y)) ha hb hab
  have hl : left (a • x + b • y) = a • left x + b • left y := rfl
  have hr : right (a • x + b • y) = a • right x + b • right y := rfl
  simp only [smul_eq_mul] at hu hv
  simp only [objective, hl, hr, smul_eq_mul]
  linarith

/-- The concrete source assumptions alone derive every compact sublevel. -/
theorem coerciveGauge_sublevel_compact {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hγ : ConvexOn ℝ univ γ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ : ℝ) (hμ : 0 < μ) (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v) (a : ℝ) :
    IsCompact {x | objective Q γ x ≤ a} :=
  sublevel_compact Q hQ γ hh (objective_convex Q hQ.posSemidef γ hγ) μ hμ hlower a

end QuadraticGauge
end BfgsVerification
