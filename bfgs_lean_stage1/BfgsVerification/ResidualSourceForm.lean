import BfgsVerification.ResidualFrames

/-!
# Source-form residual contradiction without sign assumptions on budget constants

Nonnegativity of the smooth-direction, target-gradient, and residual-size
constants follows from their displayed bounds and positive actual curvature or
predicted decrease. The transport constant is enlarged to its maximum with zero.
All matrix, projection, and frame hypotheses are retained unchanged.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Module M's arbitrary-tail residual contradiction, without additional sign
premises on its four upper-bound constants. -/
theorem residual_frames_on_tail_incompatible_source {r p : ℕ} (J : ℕ)
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hs : Summable R.d) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (L m C₀ C_T C_R : ℝ) (hm : 0 < m)
    (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec ((R.shift J).gradientChange k)) ≤
      L * (R.shift J).curvature k)
    (V Z : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (hpair : ∀ k, m ≤ sqNorm ((V k)ᵀ.mulVec ((R.shift J).g k)))
    (hchange : ∀ k, sqNorm ((V (k + 1))ᵀ.mulVec ((R.shift J).gradientChange k)) ≤
      C₀ * (R.shift J).curvature k)
    (htransport : ∀ k, V (k + 1) = V k * T k +
      EnergyIdentities.rectOuter ((R.shift J).displacement k) (b k) + Z k)
    (hT : ∀ k, FrameBounds.OperatorSqBound (T k) (1 + C_T * (R.shift J).d k))
    (hZ : ∀ k, (U * Uᵀ) * Z k = Z k)
    (hsize : ∀ k, SmoothSubspace.frobSq (Z k) ≤ C_R * (R.shift J).d k) : False := by
  have hL : 0 ≤ L := nonneg_of_mul_nonneg_left
    ((sqNorm_nonneg _).trans (hsmooth 0)) ((R.shift J).curvature_pos 0)
  have hC₀ : 0 ≤ C₀ := nonneg_of_mul_nonneg_left
    ((sqNorm_nonneg _).trans (hchange 0)) ((R.shift J).curvature_pos 0)
  have hCR : 0 ≤ C_R := nonneg_of_mul_nonneg_left
    ((SmoothSubspace.frobSq_nonneg _).trans (hsize 0)) ((R.shift J).d_pos 0)
  have hT' : ∀ k, FrameBounds.OperatorSqBound (T k)
      (1 + max C_T 0 * (R.shift J).d k) := by
    intro k v
    apply (hT k v).trans
    apply mul_le_mul_of_nonneg_right _ (sqNorm_nonneg v)
    exact add_le_add_left
      (mul_le_mul_of_nonneg_right (le_max_left C_T 0) ((R.shift J).d_pos k).le) 1
  exact R.residual_frames_on_tail_incompatible J G hG hg hs U hU
    L m C₀ (max C_T 0) C_R hL hm hC₀ (le_max_right C_T 0) hCR
    hsmooth V Z T b hpair hchange htransport hT' hZ hsize

end BfgsVerification.AdmissibleBFGSRun
