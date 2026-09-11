import BfgsVerification.AffineWhiteningSquareRoot
import BfgsVerification.OrthogonalCoordinates
import BfgsVerification.QuadraticGaugeConvex
import BfgsVerification.FixedNormalStrongConvex

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection
variable {n : ℕ}

def minEigenvalue [NeZero n] (H : Mat n) (hH : H.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hH.eigenvalues

def maxEigenvalue [NeZero n] (H : Mat n) (hH : H.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hH.eigenvalues

theorem minEigenvalue_le [NeZero n] (H : Mat n) (hH : H.IsHermitian) (i : Fin n) :
    minEigenvalue H hH≤ hH.eigenvalues i := Finset.inf'_le _ (Finset.mem_univ i)

theorem le_maxEigenvalue [NeZero n] (H : Mat n) (hH : H.IsHermitian) (i : Fin n) :
    hH.eigenvalues i≤ maxEigenvalue H hH := Finset.le_sup' _ (Finset.mem_univ i)

theorem minEigenvalue_pos [NeZero n] (H : Mat n) (hH : H.PosDef) :
    0< minEigenvalue H hH.1 := by
  exact (Finset.lt_inf'_iff _).mpr (fun i _ => hH.eigenvalues_pos i)

theorem maxEigenvalue_pos [NeZero n] (H : Mat n) (hH : H.PosDef) :
    0< maxEigenvalue H hH.1 := (hH.eigenvalues_pos 0).trans_le (le_maxEigenvalue H hH.1 0)

theorem spectral_metric_bounds (H : Mat n) (hH : H.IsHermitian) (a b : ℝ)
    (hl : ∀i,a≤ hH.eigenvalues i) (hu : ∀i,hH.eigenvalues i≤ b) (x : Vec n) :
    a*sqNorm x≤ metricEnergy H x ∧ metricEnergy H x≤ b*sqNorm x := by
  let U : Mat n := hH.eigenvectorUnitary
  have hUU : U*Uᵀ=1 := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hd : Uᵀ*H*U=Matrix.diagonal hH.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id,Function.id_comp] using hH.star_mul_self_mul_eq_diagonal
  have he : metricEnergy H x=metricEnergy (Matrix.diagonal hH.eigenvalues) (Uᵀ.mulVec x) := by
    have hp := project_energy Uᵀ H (Uᵀ.mulVec x)
    simpa only [Matrix.transpose_transpose,Matrix.mulVec_mulVec,hUU,Matrix.one_mulVec,
      compress,hd] using hp
  have hn := sqNorm_orthogonal_coordinates U hUU x
  rw [he,← hn]
  have heq (y : Vec n) : metricEnergy (Matrix.diagonal hH.eigenvalues) y=
      ∑i,hH.eigenvalues i*(y i)^2 := by
    simp only [metricEnergy,dot,Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  constructor
  · rw [sqNorm,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hl i) (sq_nonneg _))
  · rw [sqNorm,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hu i) (sq_nonneg _))

theorem actual_extreme_metric_bounds [NeZero n] (H : Mat n) (hH : H.IsHermitian) (x : Vec n) :
    minEigenvalue H hH*sqNorm x≤ metricEnergy H x ∧
      metricEnergy H x≤ maxEigenvalue H hH*sqNorm x :=
  spectral_metric_bounds H hH _ _ (minEigenvalue_le H hH) (le_maxEigenvalue H hH) x

theorem squareRoot_sqNorm (H : Mat n) (hH : H.PosDef) (x : Vec n) :
    sqNorm ((squareRoot H hH).mulVec x)=metricEnergy H x := by
  rw [← QuadraticGauge.metricEnergy_gram,squareRoot_transpose,squareRoot_square]

theorem squareRoot_norm_bounds [NeZero n] (H : Mat n) (hH : H.PosDef) (x : Vec n) :
    minEigenvalue H hH.1*sqNorm x≤ sqNorm ((squareRoot H hH).mulVec x) ∧
      sqNorm ((squareRoot H hH).mulVec x)≤ maxEigenvalue H hH.1*sqNorm x := by
  rw [squareRoot_sqNorm]
  exact actual_extreme_metric_bounds H hH.1 x

end BfgsVerification.AffineWhitening
