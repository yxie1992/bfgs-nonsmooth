import BfgsVerification.AffineCriticalWitness
import BfgsVerification.GeneralCoordinateProjection

noncomputable section
open Set MvPolynomial
namespace BfgsVerification.RealAlgebraicGeometry
open AffineCriticalObjective

/-- Actual global supporting vectors are definable from the actual graph of F.
The general finite-coordinate projection theorem is proved, not assumed. -/
theorem supportGraph_semialgebraic {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraicObjective F) : IsSemialgebraic (supportGraph F) :=
  supportGraph_semialgebraic_of_projection hF
    (fun _ hS => coordinate_projection_semialgebraic hS)

/-- The genuine affine-critical set is a finite union of actual projections
of the bounded signed-affine supporting-vector witness sets. -/
theorem affineCritical_set_semialgebraic {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraicObjective F) : IsSemialgebraic {x | IsAffineCritical F x} := by
  classical
  rw [affineCritical_set_eq_finite_projection_union]
  have h := isSemialgebraic_finset_union (Finset.univ : Finset (Fin (n+2)))
    (fun m => coordinateProjection (affineWitnessSet F m.val))
    (fun m _ => coordinate_projection_semialgebraic
      (affineWitnessSet_semialgebraic (supportGraph_semialgebraic hF) m.val))
  simpa only [Finset.mem_univ, iUnion_true] using h

/-- The lifted critical graph keeps both the path and its objective coordinate.
A smooth path in this set will control both derivatives in the value argument. -/
def affineCriticalGraph {n : ℕ} (F : Vec n → ℝ) : Set (Option (Fin n) → ℝ) :=
  {v | v ∈ objectiveGraph F ∧ IsAffineCritical F (fun i => v (some i))}

theorem affineCriticalGraph_semialgebraic {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraicObjective F) : IsSemialgebraic (affineCriticalGraph F) := by
  have h := (affineCritical_set_semialgebraic hF).polynomial_preimage
    (fun i : Fin n => (X (some i) : MvPolynomial (Option (Fin n)) ℝ))
  have h' := hF.inter h
  convert h' using 1
  ext v
  simp only [affineCriticalGraph, mem_setOf_eq, mem_inter_iff, mem_preimage,
    MvPolynomial.eval_X]

end BfgsVerification.RealAlgebraicGeometry

namespace BfgsVerification
open RealAlgebraicGeometry AffineCriticalObjective

def AffineCriticalSemialgebraicTarget : Prop := ∀ {n : ℕ} (F : Vec n → ℝ),
  IsSemialgebraicObjective F → IsSemialgebraic (supportGraph F) ∧
    IsSemialgebraic {x | IsAffineCritical F x} ∧ IsSemialgebraic (affineCriticalGraph F)

theorem affineCriticalSemialgebraic : AffineCriticalSemialgebraicTarget :=
  fun _ hF => ⟨supportGraph_semialgebraic hF, affineCritical_set_semialgebraic hF,
    affineCriticalGraph_semialgebraic hF⟩

end BfgsVerification
