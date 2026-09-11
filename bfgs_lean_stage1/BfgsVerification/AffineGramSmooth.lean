import BfgsVerification.AffineDistanceContinuity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix

noncomputable section
open scoped BigOperators Topology ContDiff InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification.ConstantRankFields
open AffineBarycentric AffineDistance AffineCriticalGeometry
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {d n m : ℕ} {k : WithTop ℕ∞} {x : Vec d}

theorem matrix_det_contDiffAt {A : Vec d → Mat m} (hA : ContDiffAt ℝ k A x) :
    ContDiffAt ℝ k (fun z => (A z).det) x := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact (contDiffAt_pi.mp ((contDiffAt_pi.mp hA) (σ i))) i

theorem matrix_adjugate_contDiffAt {A : Vec d → Mat m} (hA : ContDiffAt ℝ k A x) :
    ContDiffAt ℝ k (fun z => (A z).adjugate) x := by
  classical
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply matrix_det_contDiffAt
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  by_cases ha : a=j
  · subst a
    simpa using (contDiffAt_const : ContDiffAt ℝ k (fun _ : Vec d => (Pi.single i 1 : Vec m) b) x)
  · simpa [Matrix.updateRow_apply,ha] using ((contDiffAt_pi.mp ((contDiffAt_pi.mp hA) a)) b)

theorem matrix_inverse_contDiffAt {A : Vec d → Mat m} (hA : ContDiffAt ℝ k A x)
    (hdet : (A x).det≠0) : ContDiffAt ℝ k (fun z => (A z)⁻¹) x := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv']
  exact ((matrix_det_contDiffAt hA).inv hdet).smul (matrix_adjugate_contDiffAt hA)

theorem augmented_contDiffAt {g : Vec d → Fin m → Vec n}
    (hg : ∀i,ContDiffAt ℝ k (fun z => g z i) x) :
    ContDiffAt ℝ k (fun z => augmented (g z)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  refine Fin.cases ?_ (fun a => ?_) i
  · exact contDiffAt_const
  · exact (contDiffAt_pi.mp (hg j)) a

theorem gram_contDiffAt {A : Vec d → Matrix (Fin n) (Fin m) ℝ}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun z => gram (A z)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [gram,Matrix.mul_apply,Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro a _
  exact ((contDiffAt_pi.mp ((contDiffAt_pi.mp hA) a)) i).mul
    ((contDiffAt_pi.mp ((contDiffAt_pi.mp hA) a)) j)

theorem formulaPoint_contDiffAt (g : Vec d → Fin m → Vec n) (i : Fin m)
    (hc : ∀j,ContDiffAt ℝ k (fun p => g p j) x) (hg : AffineIndependent ℝ (g x)) :
    ContDiffAt ℝ k (fun p => formulaPoint (g p)) x := by
  have hK := gram_contDiffAt (augmented_contDiffAt hc)
  have hd := (gram_posDef (augmented (g x)) ((affineIndependent_iff_augmented_injective _).mp hg)).det_pos.ne'
  have hi := matrix_inverse_contDiffAt hK hd
  have hv : ContDiffAt ℝ k (fun p => inverseOnes (g p)) x := by
    apply contDiffAt_pi.mpr
    intro j
    simp only [inverseOnes,Matrix.mulVec,dotProduct,mul_one]
    apply ContDiffAt.sum
    intro a _
    exact (contDiffAt_pi.mp ((contDiffAt_pi.mp hi) j)) a
  have hden : ContDiffAt ℝ k (fun p => denominator (g p)) x := by
    simp only [denominator]
    apply ContDiffAt.sum
    intro j _
    exact (contDiffAt_pi.mp hv) j
  have hw : ContDiffAt ℝ k (fun p => weights (g p)) x :=
    (hden.inv (denominator_pos (g x) i hg).ne').smul hv
  have heuc : ContDiff ℝ k (euclideanVector : Vec n → EuclideanSpace ℝ (Fin n)) :=
    (WithLp.linearEquiv 2 ℝ (Vec n)).symm.toContinuousLinearEquiv.contDiff
  unfold formulaPoint
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffAt_pi.mp hw) j).smul (heuc.contDiffAt.comp x (hc j))

end BfgsVerification.ConstantRankFields
