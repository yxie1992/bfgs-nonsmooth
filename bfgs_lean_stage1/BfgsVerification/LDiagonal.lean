import BfgsVerification.StableOrbitTargets
import BfgsVerification.LNormalizedReturn
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open scoped Topology
namespace BfgsVerification.LBlockSplitting

def diagonalMap {n : ℕ} (d : Vec n) : Vec n →L[ℝ] Vec n :=
  ContinuousLinearMap.pi (fun i => d i • ContinuousLinearMap.proj i)
@[simp] theorem diagonalMap_apply {n : ℕ} (d x : Vec n) (i : Fin n) :
    diagonalMap d x i=d i*x i := rfl

def diagonalEquiv {n : ℕ} (d : Vec n) (hd : ∀ i, d i≠0) : Vec n ≃L[ℝ] Vec n :=
  ContinuousLinearEquiv.equivOfInverse (diagonalMap d) (diagonalMap fun i => (d i)⁻¹)
    (by intro x; ext i; simp [hd i]) (by intro x; ext i; simp [hd i])

@[simp] theorem diagonalEquiv_apply {n : ℕ} (d : Vec n) (hd : ∀ i, d i≠0) (x : Vec n) :
    diagonalEquiv d hd x=diagonalMap d x := rfl
@[simp] theorem diagonalEquiv_symm_apply {n : ℕ} (d : Vec n) (hd : ∀ i, d i≠0) (x : Vec n) :
    (diagonalEquiv d hd).symm x=diagonalMap (fun i => (d i)⁻¹) x := rfl

theorem diagonalMap_norm_bound {n : ℕ} (d : Vec n) {r : ℝ} (hr : 0≤r)
    (hd : ∀ i, |d i|≤r) : ‖diagonalMap d‖≤r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hr (norm_nonneg x))).2
  intro i
  rw [diagonalMap_apply,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul (hd i) (norm_le_pi_norm x i) (norm_nonneg _) hr

theorem stable_diagonal_contraction {ls rho : ℝ} (hs0 : 0<ls) (hs1 : ls<1)
    (hr0 : 0<rho) (hr1 : rho<1) : ‖diagonalMap ![ls,rho]‖<1 := by
  have hh := diagonalMap_norm_bound ![ls,rho] (r:=max ls rho) (le_max_of_le_left hs0.le)
    (fun i => by fin_cases i <;> simp [abs_of_pos hs0,abs_of_pos hr0,le_max_left,le_max_right])
  exact hh.trans_lt (max_lt hs1 hr1)

theorem unstable_diagonal_inverse_contraction {rho lu : ℝ} (hr0 : 0<rho) (hr1 : rho<1)
    (hu : 1<lu) (hd : ∀ i, (![rho⁻¹,rho⁻¹,lu] : Vec 3) i≠0) :
    ‖(diagonalEquiv ![rho⁻¹,rho⁻¹,lu] hd).symm.toContinuousLinearMap‖<1 := by
  have hpos : 0<lu := lt_trans zero_lt_one hu
  have hh := diagonalMap_norm_bound (fun i : Fin 3 => (![rho⁻¹,rho⁻¹,lu] i)⁻¹)
    (le_max_of_le_left hr0.le)
    (r:=max rho lu⁻¹) (fun i => by fin_cases i <;>
      simp [abs_of_pos hr0,abs_of_pos (inv_pos.mpr hpos),le_max_left,le_max_right])
  have hlt : lu⁻¹<1 := by exact inv_lt_one_of_one_lt₀ hu
  exact hh.trans_lt (max_lt hr1 hlt)

end BfgsVerification.LBlockSplitting
