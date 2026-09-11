import BfgsVerification.SmoothObjectiveGraphPaths

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
open RealAlgebraicGeometry AffineSupportPath

def SmoothPathCompositionTarget : Prop := ∀ {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {x y z : E},
    PiecewiseSmoothPathIn S x y → PiecewiseSmoothPathIn S y z → PiecewiseSmoothPathIn S x z

theorem smoothPathComposition : SmoothPathCompositionTarget := PiecewiseSmoothPathIn.trans

def SmoothPathMappingTarget : Prop := ∀ {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} {x y : E}, PiecewiseSmoothPathIn S x y →
    ∀ {G : E → F}, ContDiffOn ℝ ∞ G S → MapsTo G S T → PiecewiseSmoothPathIn T (G x) (G y)

theorem smoothPathMapping : SmoothPathMappingTarget := PiecewiseSmoothPathIn.map

def SmoothCylindersTarget : Prop := ∀ {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}, PiecewiseSmoothConnected S →
    (∀ f : E → ℝ, ContDiffOn ℝ ∞ f S →
      PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ z.2 = f z.1}) ∧
    (∀ a b : E → ℝ, ContDiffOn ℝ ∞ a S → ContDiffOn ℝ ∞ b S →
      (∀ x ∈ S, a x < b x) →
      PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ a z.1 < z.2 ∧ z.2 < b z.1}) ∧
    (∀ a : E → ℝ, ContDiffOn ℝ ∞ a S →
      PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ a z.1 < z.2}) ∧
    (∀ b : E → ℝ, ContDiffOn ℝ ∞ b S →
      PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ z.2 < b z.1}) ∧
    PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S}

theorem smoothCylinders : SmoothCylindersTarget := fun hS =>
  ⟨fun _ hf => hS.graph hf, fun _ _ ha hb hab => hS.open_band ha hb hab,
    fun _ ha => hS.upper_band ha, fun _ hb => hS.lower_band hb, hS.full_cylinder⟩

def LiftedObjectivePathTarget : Prop := ∀ {n : ℕ} {F : Vec n → ℝ}
    {S : Set (Vec n)} {T : Set (Option (Fin n) → ℝ)} {u v : Option (Fin n) → ℝ},
    (∀ z ∈ T, z none = F (fun i => z (some i)) ∧ (fun i => z (some i)) ∈ S) →
    PiecewiseSmoothPathIn T u v →
    PiecewiseDifferentiablePathIn F S (fun i => u (some i)) (fun i => v (some i))

theorem liftedObjectivePath : LiftedObjectivePathTarget := lifted_graph_piecewiseDifferentiablePath

end BfgsVerification
