import BfgsVerification.AffineCriticalPathCover

noncomputable section
open scoped Topology BigOperators
open Set Filter
open BfgsVerification BfgsVerification.AffineSupportPath
open BfgsVerification.AffineCriticalObjective BfgsVerification.ConvexSubdifferential

def BoundedSupportContract : Prop := ∀ {n : ℕ} (F : Vec n → ℝ) (x : Vec n),
  IsAffineCritical F x ↔ ∃ m : ℕ, 0 < m ∧ m ≤ n+1 ∧ ∃ g : Fin m → Vec n,
    ∃ w : Fin m → ℝ, (∀ i, Homogeneous.Supports F x (g i)) ∧
      (∑ i, w i)=1 ∧ (∑ i, w i • g i)=0

def PathConstancyContract : Prop := ∀ {n : ℕ} {F : Vec n → ℝ},
  ConvexOn ℝ univ F → ∀ {p : ℝ → Vec n} {a b : ℝ} (s : Finset ℝ),
    ContinuousOn p (Icc a b) → (∀ t ∈ Ioo a b, IsAffineCritical F (p t)) →
      (∀ t ∈ Ioo a b, t ∉ s → DifferentiableAt ℝ p t) →
      (∀ t ∈ Ioo a b, t ∉ s → DifferentiableAt ℝ (F ∘ p) t) →
      ∀ t ∈ Icc a b, F (p t)=F (p a)

def ConditionalGapContract : Prop := ∀ {n m : ℕ} {F : Vec n → ℝ},
  ConvexOn ℝ univ F → ∀ C : Fin m → Set (Vec n),
    {p | IsAffineCritical F p} = ⋃ i, C i →
    (∀ i, ∀ x ∈ C i, ∀ y ∈ C i, PiecewiseDifferentiablePathIn F (C i) x y) →
    ∀ star : Vec n, (∀ x, F star ≤ F x) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ p, F p < F star+ε →
        IsAffineCritical F p → (0 : Vec n) ∈ subdifferential F p

open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.AffineSupportPath.isAffineCritical_iff_bounded_supports, `BoundedSupportContract),
    (`BfgsVerification.AffineSupportPath.objective_constant_on_piecewise_differentiable_path, `PathConstancyContract),
    (`BfgsVerification.AffineSupportPath.low_level_affine_correct_of_finite_path_cover, `ConditionalGapContract)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_INFRASTRUCTURE_CONTRACT_OK {decl}"
