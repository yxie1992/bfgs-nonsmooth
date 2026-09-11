import BfgsVerification.AffineProjection
import Mathlib.Topology.Instances.Matrix

/-! Module A's actual Gram left inverse and local positivity of barycentric
solutions. No rank persistence or continuity of a pseudoinverse is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineBarycentric

def gram {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Mat m := Aᵀ*A

def leftInverse {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  (gram A)⁻¹*Aᵀ

def coefficients {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Vec n) : Vec m :=
  (leftInverse A).mulVec b

theorem gram_posDef {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : Function.Injective A.mulVec) : (gram A).PosDef := by
  simpa only [metricGram, Matrix.mul_one, gram] using
    metricGram_posDef (H := (1 : Mat n)) Matrix.PosDef.one hA

theorem leftInverse_mul {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : (gram A).det ≠ 0) : leftInverse A * A = 1 := by
  rw [leftInverse, Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ hA.isUnit

theorem injective_of_gram_det_ne_zero {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : (gram A).det ≠ 0) : Function.Injective A.mulVec := by
  intro u v he
  have h := congrArg (leftInverse A).mulVec he
  simpa only [Matrix.mulVec_mulVec, leftInverse_mul A hA, Matrix.one_mulVec] using h

/-- Every actual solution equals the actual Gram formula; no least-squares
residual is substituted for the equality constraint. -/
theorem solution_eq_coefficients {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : (gram A).det ≠ 0) (b : Vec n) (w : Vec m) (hw : A.mulVec w = b) :
    w = coefficients A b := by
  rw [coefficients, ← hw, Matrix.mulVec_mulVec, leftInverse_mul A hA, Matrix.one_mulVec]

theorem gram_continuous {n m : ℕ} : Continuous (gram : Matrix (Fin n) (Fin m) ℝ → Mat m) :=
  continuous_id.matrix_transpose.matrix_mul continuous_id

/-- The concrete coefficient formula is continuous at every full-rank matrix. -/
theorem coefficients_continuousAt {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : (gram A).det ≠ 0) (b : Vec n) : ContinuousAt (fun B => coefficients B b) A := by
  have hi : ContinuousAt (fun B : Matrix (Fin n) (Fin m) ℝ => (gram B)⁻¹) A :=
    (continuousAt_matrix_inv (gram A) (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hA)).comp
      gram_continuous.continuousAt
  have hb : Continuous (fun B : Matrix (Fin n) (Fin m) ℝ => Bᵀ.mulVec b) :=
    continuous_id.matrix_transpose.matrix_mulVec continuous_const
  have hm : Continuous (fun p : Mat m × Vec m => p.1.mulVec p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have h := hm.continuousAt.comp (hi.prodMk_nhds hb.continuousAt)
  simpa only [coefficients, leftInverse, ← Matrix.mulVec_mulVec] using h

/-- Full column rank persists nearby because the actual Gram determinant is
continuous and nonzero. -/
theorem eventually_full_column_rank {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (A : X → Matrix (Fin n) (Fin m) ℝ) (x : X) (hc : ContinuousAt A x)
    (hA : Function.Injective (A x).mulVec) :
    ∀ᶠ p in 𝓝 x, Function.Injective (A p).mulVec := by
  have hd := (gram_posDef (A x) hA).det_pos.ne'
  have ht : ContinuousAt (fun p => (gram (A p)).det) x :=
    gram_continuous.matrix_det.continuousAt.comp hc
  filter_upwards [ht.eventually (eventually_ne_nhds hd)] with p hp
  exact injective_of_gram_det_ne_zero _ hp

/-- Module A's barycentric stability: every nearby solvable augmented system
has the unique strictly positive solution, and rank persistence is derived.
The theorem allows unsolvable nearby systems rather than assuming solvability. -/
theorem positive_solutions_eventually {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (A : X → Matrix (Fin n) (Fin m) ℝ) (x : X) (hc : ContinuousAt A x)
    (hA : Function.Injective (A x).mulVec) (b : Vec n) (w0 : Vec m)
    (hw0 : (A x).mulVec w0 = b) (hpos : ∀ i, 0 < w0 i) :
    ∀ᶠ p in 𝓝 x, Function.Injective (A p).mulVec ∧
      ∀ w : Vec m, (A p).mulVec w = b → w = coefficients (A p) b ∧ ∀ i, 0 < w i := by
  have hd := (gram_posDef (A x) hA).det_pos.ne'
  have he := solution_eq_coefficients (A x) hd b w0 hw0
  have ht : ContinuousAt (fun p => coefficients (A p) b) x :=
    (coefficients_continuousAt (A x) hd b).comp hc
  have hp : ∀ᶠ p in 𝓝 x, ∀ i, 0 < coefficients (A p) b i := by
    apply eventually_all.mpr
    intro i
    have hc0 : 0 < coefficients (A x) b i := by rw [← he]; exact hpos i
    exact ((continuous_apply i).continuousAt.comp ht).eventually (eventually_gt_nhds hc0)
  have htD : ContinuousAt (fun p => (gram (A p)).det) x :=
    gram_continuous.matrix_det.continuousAt.comp hc
  filter_upwards [hp, htD.eventually (eventually_ne_nhds hd)] with p hposp hdetp
  refine ⟨injective_of_gram_det_ne_zero _ hdetp, ?_⟩
  intro w hw
  have heq := solution_eq_coefficients (A p) hdetp b w hw
  exact ⟨heq, fun i => by rw [heq]; exact hposp i⟩

end AffineBarycentric
end BfgsVerification
