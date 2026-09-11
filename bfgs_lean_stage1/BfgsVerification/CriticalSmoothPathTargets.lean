import BfgsVerification.CriticalSmoothPathValues

noncomputable section
open Set
open scoped Topology
namespace BfgsVerification
open RealAlgebraicGeometry AffineCriticalObjective

def CriticalSmoothPathValuesTarget : Prop := ∀ {n : ℕ} (F : Vec n → ℝ),
    ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    (piecewiseSmoothComponent {z | IsAffineCritical F z} '' {z | IsAffineCritical F z}).Finite ∧
    (∀ x, IsSemialgebraic (piecewiseSmoothComponent {z | IsAffineCritical F z} x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent {z | IsAffineCritical F z} x) ∧
      ∀ p ∈ piecewiseSmoothComponent {z | IsAffineCritical F z} x,
        ∀ q ∈ piecewiseSmoothComponent {z | IsAffineCritical F z} x, F p = F q) ∧
    (∀ (x y : Vec n) (p : PiecewiseSmoothPath {z | IsAffineCritical F z} x y),
      (∀ t ∈ Icc (0 : ℝ) 1, F (p.curve t) = F x) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u => F (p.curve u)) 0 t)

theorem criticalSmoothPathValues : CriticalSmoothPathValuesTarget := by
  intro n F hF hSA
  obtain ⟨hfin,hcomp⟩ := semialgebraic_affine_critical_smooth_components hF hSA
  refine ⟨hfin,hcomp,fun x y p => ⟨?_,?_⟩⟩
  · exact semialgebraic_affine_critical_path_constant hF hSA p
  · intro t ht
    exact semialgebraic_affine_critical_path_hasDerivAt_zero hF hSA p ht

end BfgsVerification
