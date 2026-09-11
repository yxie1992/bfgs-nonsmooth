import BfgsVerification.HomogeneousBlockTransport
import BfgsVerification.HomogeneousBlockAlgebra

/-! The finite-value branch with all accepted gradients on one fixed line.
The slope coordinate tends to zero from the actual finite gradient alphabet;
the exact BFGS lift then derives convergence of all actual iterates. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace HomogeneousBlock

def lineMatrix {n : ℕ} (a : Vec n) : Matrix (Fin 1) (Fin n) ℝ := fun _ => a

theorem lineMatrix_mulVec {n : ℕ} (a x : Vec n) :
    (lineMatrix a).mulVec x = fun _ => dot a x := by rfl

theorem lineMatrix_transpose_mulVec {n : ℕ} (a : Vec n) (v : Vec 1) :
    (lineMatrix a)ᵀ.mulVec v = v 0 • a := by
  ext i
  simp [lineMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem lineMatrix_fullRowRank {n : ℕ} (a : Vec n) (ha : a ≠ 0) :
    AffineProjection.FullRowRank (lineMatrix a) := by
  intro u v h
  rw [lineMatrix_transpose_mulVec, lineMatrix_transpose_mulVec] at h
  have hc : u 0 = v 0 := (smul_left_injective ℝ ha) h
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using hc

/-- A finite nonzero alphabet on a fixed nonzero line yields a uniform inverse
slope multiplier bound; no lower bound on actual values is added. -/
theorem finite_line_pairing_bound {n : ℕ} (A : Finset (Vec n)) (a : Vec n) (ha : a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ A, g ≠ 0 → (∃ c : ℝ, g = c • a) →
      ∀ x, |dot a x| ≤ C * |dot g x| := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  let C : ℝ := ∑ g ∈ A, |a i / g i|
  refine ⟨C, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro g hg hg0 hc x
  obtain ⟨c, hc⟩ := hc
  have hc0 : c ≠ 0 := by intro h; rw [h, zero_smul] at hc; exact hg0 hc
  have hgi : g i ≠ 0 := by simpa [hc] using mul_ne_zero hc0 hi
  have he : dot a x = (a i / g i) * dot g x := by
    rw [hc, dot_smul_first]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [he, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact Finset.single_le_sum (s := A) (f := fun g => |a i / g i|) (fun _ _ => abs_nonneg _) hg

end HomogeneousBlock
namespace AdmissibleBFGSRun
open Homogeneous HomogeneousBlock AffineProjection

/-- H.7.4's final fixed-line case in arbitrary ambient dimension. The actual
finite alphabet supplies the nonvanishing slope coordinate, and full BFGS
supplies its fixed lift through the initial metric. -/
theorem maxLinear_fixed_line_convergence {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA)) (a : Vec n) (ha : a ≠ 0)
    (hg : ∀ k, ∃ c : ℝ, R.g k = c • a)
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    Tendsto R.x atTop (𝓝 (fiberPoint (lineMatrix a) (R.H 0) (R.x 0) 0)) := by
  classical
  obtain ⟨C, _, hC⟩ := finite_line_pairing_bound A a ha
  have hcoord : Tendsto (fun k => dot a (R.x k)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) (by simpa using hv.abs.const_mul C)
    simpa only [R.homogeneous_euler (finiteMaxLinear_homogeneous A hA)] using
      hC (R.g k) (R.maxLinear_gradient_mem A hA k) (R.gradient_nonzero k) (hg k) (R.x k)
  choose c hc using hg
  have hgbar (k : ℕ) : (lineMatrix a)ᵀ.mulVec (fun _ => c k) = R.g k := by
    rw [lineMatrix_transpose_mulVec]
    exact (hc k).symm
  have hz : Tendsto (fun k => (lineMatrix a).mulVec (R.x k)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hcoord
  exact R.affine_limit_lift (lineMatrix a) (lineMatrix_fullRowRank a ha) (fun k _ => c k) hgbar 0 hz

/-- The fixed-line conclusion holds after an arbitrary finite prefix, with
its actual current metric and point. -/
theorem maxLinear_fixed_line_tail_convergence {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA)) (J : ℕ) (a : Vec n) (ha : a ≠ 0)
    (hg : ∀ k, ∃ c : ℝ, R.g (J+k) = c • a)
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    Tendsto R.x atTop (𝓝 (fiberPoint (lineMatrix a) (R.H J) (R.x J) 0)) := by
  have hs := (R.shift J).maxLinear_fixed_line_convergence A hA a ha hg
    (hv.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat J))
  apply (tendsto_add_atTop_iff_nat J).mp
  simpa only [shift, Nat.add_zero, Nat.add_comm] using hs

end AdmissibleBFGSRun
end BfgsVerification
