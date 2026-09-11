import BfgsVerification.SmoothCylindricalConnectivity
import BfgsVerification.AffineCriticalDefinability
import BfgsVerification.AffineCriticalPathCover

/-! Projecting an actual lifted objective-graph path gives both required
derivatives. No differentiability of the objective is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
open AffineSupportPath AffineCriticalObjective

def objectiveLift {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Option (Fin n) → ℝ :=
  fun i => Option.elim i (F x) x

theorem objectiveLift_mem_graph {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    objectiveLift F x ∈ objectiveGraph F := rfl

theorem lifted_graph_piecewiseDifferentiablePath {n : ℕ} {F : Vec n → ℝ}
    {S : Set (Vec n)} {T : Set (Option (Fin n) → ℝ)}
    {u v : Option (Fin n) → ℝ}
    (hT : ∀ z ∈ T, z none = F (fun i => z (some i)) ∧ (fun i => z (some i)) ∈ S)
    (hp : PiecewiseSmoothPathIn T u v) :
    PiecewiseDifferentiablePathIn F S (fun i => u (some i)) (fun i => v (some i)) := by
  obtain ⟨p⟩ := hp
  let q : ℝ → Vec n := fun t i => p.curve t (some i)
  have hqc : ContinuousOn q (Icc 0 1) := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply (some i)).comp_continuousOn p.continuousOn
  refine ⟨q, hqc, ?_, ?_, ?_, p.exceptions, ?_⟩
  · funext i
    exact congrArg (fun z => z (some i)) p.source
  · funext i
    exact congrArg (fun z => z (some i)) p.target
  · intro t ht
    exact (hT _ (p.mapsTo ht)).2
  · intro t ht he
    have hd := (p.smoothAt t ht he).differentiableAt (by simp)
    constructor
    · exact differentiableAt_pi.mpr (fun i => differentiableAt_pi.mp hd (some i))
    · have hv := differentiableAt_pi.mp hd none
      apply hv.congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      exact (hT _ (p.mapsTo hs)).1.symm

theorem affineCriticalGraph_path_project {n : ℕ} {F : Vec n → ℝ}
    {u v : Option (Fin n) → ℝ}
    (hp : PiecewiseSmoothPathIn (affineCriticalGraph F) u v) :
    PiecewiseDifferentiablePathIn F {x | IsAffineCritical F x}
      (fun i => u (some i)) (fun i => v (some i)) :=
  lifted_graph_piecewiseDifferentiablePath (fun _ hz => hz) hp

theorem objective_eq_of_smooth_criticalGraph_path {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x y : Vec n}
    (hp : PiecewiseSmoothPathIn (affineCriticalGraph F) (objectiveLift F x) (objectiveLift F y)) :
    F x = F y :=
  value_eq_of_affineCritical_path hF (fun _ hx => hx) (affineCriticalGraph_path_project hp)

end RealAlgebraicGeometry
end BfgsVerification
