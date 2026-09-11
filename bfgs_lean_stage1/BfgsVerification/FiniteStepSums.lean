import BfgsVerification.TarskiLocalIndex
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- The finite sum of closed right-hand steps with specified signed jumps. -/
def finiteStepSum (B : Finset ℝ) (j : ℝ → ℤ) (x : ℝ) : ℤ :=
  ∑ b ∈ B, if b ≤ x then j b else 0

theorem finiteStepSum_erase (B : Finset ℝ) (j : ℝ → ℤ) (a x : ℝ)
    (hj : a ∉ B → j a = 0) :
    finiteStepSum B j x = (if a ≤ x then j a else 0) + finiteStepSum (B.erase a) j x := by
  classical
  by_cases ha : a ∈ B
  · simpa only [finiteStepSum, add_comm] using
      (Finset.sum_erase_add B (fun b => if b ≤ x then j b else 0) ha).symm
  · simp [finiteStepSum, Finset.erase_eq_of_not_mem ha, hj ha]

theorem finiteStepSum_eventuallyEq_of_not_mem (B : Finset ℝ) (j : ℝ → ℤ) {a : ℝ}
    (ha : a ∉ B) : ∀ᶠ x in 𝓝 a, finiteStepSum B j x = finiteStepSum B j a := by
  classical
  have hh : ∀ b ∈ B, ∀ᶠ x in 𝓝 a,
      (if b ≤ x then j b else 0) = (if b ≤ a then j b else 0) := by
    intro b hb
    have hne : b ≠ a := by intro he; exact ha (he ▸ hb)
    rcases lt_or_gt_of_ne hne with hba | hab
    · filter_upwards [lt_mem_nhds hba] with x hx
      simp [hba.le, hx.le]
    · filter_upwards [gt_mem_nhds hab] with x hx
      simp [not_le_of_gt hab, not_le_of_gt hx]
  filter_upwards [B.eventually_all.mpr hh] with x hx
  exact Finset.sum_congr rfl hx

theorem finiteStepSum_eventually_atTop (B : Finset ℝ) (j : ℝ → ℤ) :
    ∀ᶠ x in atTop, finiteStepSum B j x = ∑ b ∈ B, j b := by
  classical
  have h : ∀ b ∈ B, ∀ᶠ x : ℝ in atTop, b ≤ x := fun b _ => eventually_ge_atTop b
  filter_upwards [B.eventually_all.mpr h] with x hx
  unfold finiteStepSum
  apply Finset.sum_congr rfl
  intro b hb
  rw [if_pos (hx b hb)]

theorem finiteStepSum_eventually_atBot (B : Finset ℝ) (j : ℝ → ℤ) :
    ∀ᶠ x in atBot, finiteStepSum B j x = 0 := by
  classical
  have h : ∀ b ∈ B, ∀ᶠ x : ℝ in atBot, x < b := fun b _ => eventually_lt_atBot b
  filter_upwards [B.eventually_all.mpr h] with x hx
  unfold finiteStepSum
  apply Finset.sum_eq_zero
  intro b hb
  rw [if_neg (not_le_of_gt (hx b hb))]

end RealAlgebraicGeometry
end BfgsVerification
