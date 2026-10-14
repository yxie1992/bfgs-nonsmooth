import BfgsVerification.HomogeneousConsequences
import BfgsVerification.HomogeneousMaxLinear

/-!
# Compact homogeneous models (Corollary `art:homogeneous-examples`)

Explicit Lean forms of the three cases of the corollary: every norm (a seminorm
vanishing only at zero), every convex degree-one function with bounded unit
sublevel, and every finite linear maximum with bounded zero sublevel. Each has
the conclusion of Theorem `art:homogeneous`: zero is the unique minimizer, and
every infinite admissible full-BFGS run converges to it in value and in
iterates. All three reduce to
`AdmissibleBFGSRun.homogeneous_iterates_zero_of_bounded_zero_sublevel`.
-/

noncomputable section
open scoped Topology
open Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ}

/-- The conclusion of Theorem `art:homogeneous` from a bounded zero sublevel. -/
theorem homogeneous_conclusion_of_bounded_zero_sublevel {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (hF : Homogeneous.PositiveDegreeOne F)
    (hb : Bornology.IsBounded {x | F x ≤ 0}) :
    F 0 = 0 ∧ (∀ x, x ≠ 0 → 0 < F x) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have h0 := Homogeneous.value_zero hF
  have hpos : ∀ x, x ≠ 0 → 0 < F x := fun _ hx =>
    Homogeneous.positive_of_bounded_zero_sublevel hF hb hx
  have hnonneg : ∀ x, 0 ≤ F x := by
    intro x
    by_cases hx : x = 0
    · rw [hx, h0]
    · exact (hpos x hx).le
  exact ⟨h0, hpos, R.homogeneous_value_zero_of_lower_bound hF 0 (fun k => hnonneg (R.x k)),
    R.homogeneous_iterates_zero_of_bounded_zero_sublevel hF hb⟩

/-- Norm case: every norm on `ℝⁿ`, given as a seminorm that vanishes only at zero. -/
theorem norm_conclusion (N : Seminorm ℝ (Vec n)) (hN : ∀ x, N x = 0 → x = 0)
    (R : AdmissibleBFGSRun n N) :
    N 0 = 0 ∧ (∀ x, x ≠ 0 → 0 < N x) ∧
      Tendsto (fun k => N (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hF : Homogeneous.PositiveDegreeOne (N : Vec n → ℝ) := by
    intro t ht x
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hb : Bornology.IsBounded {x : Vec n | N x ≤ 0} := by
    apply (Bornology.isBounded_singleton : Bornology.IsBounded ({0} : Set (Vec n))).subset
    intro x hx
    have hx' : N x ≤ 0 := hx
    exact hN x (le_antisymm hx' (apply_nonneg N x))
  exact R.homogeneous_conclusion_of_bounded_zero_sublevel hF hb

/-- Gauge case: a convex positively degree-one function with bounded unit
sublevel. Convexity is part of the admissible run. -/
theorem gauge_conclusion {F : Vec n → ℝ} (hF : Homogeneous.PositiveDegreeOne F)
    (hb : Bornology.IsBounded {x | F x ≤ 1}) (R : AdmissibleBFGSRun n F) :
    F 0 = 0 ∧ (∀ x, x ≠ 0 → 0 < F x) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  apply R.homogeneous_conclusion_of_bounded_zero_sublevel hF
  apply hb.subset
  intro x hx
  have hx' : F x ≤ 0 := hx
  exact hx'.trans zero_le_one

/-- Finite linear maximum case `x ↦ max_{a ∈ A} aᵀx` with bounded zero sublevel. -/
theorem finiteMaxLinear_conclusion (A : Finset (Vec n)) (hA : A.Nonempty)
    (hb : Bornology.IsBounded {x | Homogeneous.finiteMaxLinear A hA x ≤ 0})
    (R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)) :
    Homogeneous.finiteMaxLinear A hA 0 = 0 ∧
      (∀ x, x ≠ 0 → 0 < Homogeneous.finiteMaxLinear A hA x) ∧
      Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) :=
  R.homogeneous_conclusion_of_bounded_zero_sublevel (Homogeneous.finiteMaxLinear_homogeneous A hA) hb

end BfgsVerification.AdmissibleBFGSRun
