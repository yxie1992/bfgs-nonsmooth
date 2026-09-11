import BfgsVerification.AffineBarycentricAlgebra
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Analysis.Convex.Combination

/-! Augmented actual gradient columns encode affine combinations, including
all missing-index coefficients. The first row is the affine weight sum. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineBarycentric

def augmented {n m : ℕ} (g : Fin m → Vec n) : Matrix (Fin (n+1)) (Fin m) ℝ :=
  fun i j => Fin.cases (1 : ℝ) (g j) i

def affineTarget (n : ℕ) : Vec (n+1) := Pi.single 0 1

theorem augmented_mulVec_zero_row {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) :
    (augmented g).mulVec w 0 = ∑ j, w j := by
  simp [augmented, Matrix.mulVec, dotProduct]

theorem augmented_mulVec_succ_row {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) (i : Fin n) :
    (augmented g).mulVec w i.succ = (∑ j, w j • g j) i := by
  simp [augmented, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem augmented_mulVec_eq_zero_iff {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) :
    (augmented g).mulVec w = 0 ↔ (∑ j, w j) = 0 ∧ (∑ j, w j • g j) = 0 := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · simpa only [augmented_mulVec_zero_row, Pi.zero_apply] using congrFun he 0
    · ext i
      simpa only [augmented_mulVec_succ_row, Pi.zero_apply] using congrFun he i.succ
  · rintro ⟨hw, hg⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [augmented_mulVec_zero_row, Pi.zero_apply] using hw
    · simpa only [augmented_mulVec_succ_row, Pi.zero_apply] using congrFun hg j

/-- The actual augmented system is precisely affine weights representing zero. -/
theorem augmented_equation_iff {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) :
    (augmented g).mulVec w = affineTarget n ↔ (∑ j, w j) = 1 ∧ (∑ j, w j • g j) = 0 := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · simpa [augmented_mulVec_zero_row, affineTarget] using congrFun he 0
    · ext i
      simpa [augmented_mulVec_succ_row, affineTarget] using congrFun he i.succ
  · rintro ⟨hw, hg⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [augmented_mulVec_zero_row, affineTarget] using hw
    · simpa [augmented_mulVec_succ_row, affineTarget] using congrFun hg j

theorem weightedVSub_eq_sum_of_sum_zero {n m : ℕ} (g : Fin m → Vec n) (w : Vec m)
    (hw : (∑ j, w j) = 0) : Finset.univ.weightedVSub g w = ∑ j, w j • g j := by
  exact Finset.weightedVSub_eq_linear_combination Finset.univ hw

/-- Source affine independence is exactly full column rank of the augmented
actual gradient matrix, rather than an added independent rank certificate. -/
theorem affineIndependent_iff_augmented_injective {n m : ℕ} (g : Fin m → Vec n) :
    AffineIndependent ℝ g ↔ Function.Injective (augmented g).mulVec := by
  constructor
  · intro hg u v huv
    have hz : (augmented g).mulVec (u-v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    obtain ⟨hw, hvec⟩ := (augmented_mulVec_eq_zero_iff g (u-v)).mp hz
    have hvs : Finset.univ.weightedVSub g (u-v) = (0 : Vec n) := by
      rw [weightedVSub_eq_sum_of_sum_zero g (u-v) hw]
      exact hvec
    have hzero := (affineIndependent_iff_of_fintype ℝ g).mp hg (u-v) hw hvs
    exact sub_eq_zero.mp (funext hzero)
  · intro hinj
    apply (affineIndependent_iff_of_fintype ℝ g).mpr
    intro w hw hvs i
    have hv : (∑ j, w j • g j) = 0 := by
      rwa [weightedVSub_eq_sum_of_sum_zero g w hw] at hvs
    have hm := (augmented_mulVec_eq_zero_iff g w).mpr ⟨hw, hv⟩
    have hz : w = 0 := hinj (by simpa only [Matrix.mulVec_zero] using hm)
    exact congrFun hz i

/-- Positive solutions of the augmented system are genuine convex combinations. -/
theorem zero_mem_convexHull_of_positive_augmented_solution {n m : ℕ}
    (g : Fin m → Vec n) (w : Vec m) (hw : ∀ i, 0 < w i)
    (he : (augmented g).mulVec w = affineTarget n) :
    (0 : Vec n) ∈ convexHull ℝ (Set.range g) := by
  obtain ⟨hs, hv⟩ := (augmented_equation_iff g w).mp he
  exact mem_convexHull_of_exists_fintype w g (fun i => (hw i).le) hs (fun i => mem_range_self i) hv

/-- Continuity of the actual gradient family implies continuity of its
augmented matrix; no full-matrix regularity premise is added. -/
theorem augmented_continuous {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (hc : ∀ j, Continuous (fun x => g x j)) :
    Continuous (fun x => augmented (g x)) := by
  apply continuous_matrix
  intro i j
  refine Fin.cases ?_ (fun k => ?_) i
  · exact continuous_const
  · exact (continuous_apply k).comp (hc j)

end AffineBarycentric
end BfgsVerification
