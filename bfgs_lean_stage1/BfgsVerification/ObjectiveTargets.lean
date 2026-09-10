import BfgsVerification.ObjectiveDefinitions

/-! Objective-level target propositions. They quantify over the accepted run
with initial-only SPD and actual derivatives. Their hypotheses do not contain
the matrix invariants or a normalized scalar hierarchy. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification

/-- M.2 for actual objective-level runs, retaining its weaker vanishing-budget
assumption instead of imposing summability. -/
def ObjectiveReciprocalGrowthTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (G : ℝ),
    0 < G → (∀ k, sqNorm (R.g k) ≤ G ^ 2) →
    Tendsto R.d atTop (𝓝 0) →
    Tendsto (reciprocalGeometricMean R.q) atTop atTop ∧
    Tendsto (reciprocalMean R.q) atTop atTop

/-- Lower-bounded values and bounded gradients suffice; summability is a
conclusion from actual Armijo acceptance, not an input hypothesis. -/
def ObjectiveLowerBoundGrowthTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (G L : ℝ),
    0 < G → (∀ k, sqNorm (R.g k) ≤ G ^ 2) → (∀ k, L ≤ F (R.x k)) →
    Summable R.d ∧
    Tendsto (reciprocalGeometricMean R.q) atTop atTop ∧
    Tendsto (reciprocalMean R.q) atTop atTop ∧
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2)
      atTop atTop

/-- On a compact initial sublevel, the gradient and budget hypotheses are all
derived from the finite convex objective and accepted-step conditions. -/
def CompactObjectiveGrowthTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F),
    IsCompact R.initialSublevel →
    (∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (R.g k) ≤ G ^ 2) ∧
    Summable R.d ∧
    Tendsto (reciprocalGeometricMean R.q) atTop atTop ∧
    Tendsto (reciprocalMean R.q) atTop atTop ∧
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2)
      atTop atTop

/-- The exact source bound for an objective run, with c fixed by its weak-Wolfe
constant and D the actual predicted-decrease tail sum. -/
def ObjectiveFiniteHorizonBound {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (G : ℝ) : Prop :=
  ∀ (J m : ℕ), 0 < m → ∀ η : ℝ, 0 < η →
    let c := 1 - R.c₂
    let D := ∑' i : ℕ, R.d (J + i)
    let V := ∑ j ∈ Finset.range n,
      ((4 * G ^ 2 / c ^ 2) / η) ^ j * principalSum (R.H J) (j + 1)
    ((m + 1 : ℕ) : ℝ) * (G ^ 2 * V) ^ (-1 / ((m + 1 : ℕ) : ℝ)) *
      (η + D / (c * (m : ℝ))) ^ (-(m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range (m + 1), (R.q (J + i))⁻¹

/-- Compactness supplies a positive gradient bound for the exact finite-horizon
estimate, without assuming either that bound or summability in the target. -/
def CompactObjectiveFiniteHorizonTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F),
    IsCompact R.initialSublevel →
    ∃ G : ℝ, 0 < G ∧ (∀ k, sqNorm (R.g k) ≤ G ^ 2) ∧ ObjectiveFiniteHorizonBound R G

end BfgsVerification
