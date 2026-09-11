import BfgsVerification.ParabolicEnvelopeCells

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

/-- A finite ramp sum on the compact normalized envelope. Exact duplicates are
counted once, empty cells are omitted, and singleton cells contribute zero. -/
def envelopePotential (v : ℝ) : ℝ :=
  ∑ i ∈ P.retainedCells, (-P.b i / 2) * Envelope.ramp (P.cellLeft i) (P.cellRight i) v

/-- Original branch constants, including duplicates and tie-only pieces.
An empty cell receives an arbitrary zero constant and is never selected there. -/
def calibration (i : Fin m) : ℝ := by
  classical
  exact if (P.envelopeCell i).Nonempty then
    P.envelopePotential (P.cellLeft i) - P.a i * P.normalizedQuadratic i (P.cellLeft i) / 2 else 0

theorem potential_difference_on_retained_cell {i : Fin m} (hi : i ∈ P.retainedCells)
    {v w : ℝ} (hv : v ∈ P.envelopeCell i) (hw : w ∈ P.envelopeCell i) :
    P.envelopePotential v - P.envelopePotential w = (-P.b i / 2) * (v - w) := by
  classical
  have hin := (P.mem_retainedCells.mp hi).2
  have hv' := hv
  have hw' := hw
  rw [P.envelopeCell_eq_interval hin] at hv' hw'
  unfold envelopePotential
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [Envelope.ramp_of_mem hv', Envelope.ramp_of_mem hw']
    ring
  · intro j hj hji
    have hjn := (P.mem_retainedCells.mp hj).2
    have hs := P.retained_cell_inter_subsingleton hi hj hji.symm
    rw [P.envelopeCell_eq_interval hin, P.envelopeCell_eq_interval hjn] at hs
    have hc := Envelope.ramp_constant_on_cell (P.cellLeft_le_right hin)
      (P.cellLeft_le_right hjn) hs hv' hw'
    rw [hc]
    ring
  · intro hn
    exact False.elim (hn hi)

/-- The ramp identity extends to every original cell through its proved exact
coefficient representative; duplicated positive-length cells are not counted twice. -/
theorem potential_difference_on_cell {i : Fin m} {v w : ℝ}
    (hv : v ∈ P.envelopeCell i) (hw : w ∈ P.envelopeCell i) :
    P.envelopePotential v - P.envelopePotential w = (-P.b i / 2) * (v - w) := by
  have he := P.envelopeCell_eq_of_coefficients (P.canonicalIndex_coefficients i).1
    (P.canonicalIndex_coefficients i).2
  have h := P.potential_difference_on_retained_cell (v := v) (w := w) (P.canonicalIndex_mem_retained hv)
    (by rwa [he]) (by rwa [he])
  simpa only [(P.canonicalIndex_coefficients i).2] using h

/-- Each original active exponent is one and the same continuous ramp function
on its entire cell, including singleton cells and all endpoints. -/
theorem calibration_matches_cell {i : Fin m} {v : ℝ} (hv : v ∈ P.envelopeCell i) :
    P.envelopePotential v = P.a i * P.normalizedQuadratic i v / 2 + P.calibration i := by
  classical
  have hn : (P.envelopeCell i).Nonempty := ⟨v, hv⟩
  have hpot := P.potential_difference_on_cell hv (P.cellLeft_mem hn)
  have hline := P.normalizedQuadratic_identity i v
  have hline' := P.normalizedQuadratic_identity i (P.cellLeft i)
  rw [calibration, if_pos hn]
  nlinarith

/-- Calibration agrees whenever two original cells meet, with no exclusion of
triple ties, exact duplicates, or zero normal slope. -/
theorem calibration_matches_tie {i j : Fin m} {v : ℝ}
    (hi : v ∈ P.envelopeCell i) (hj : v ∈ P.envelopeCell j) :
    (P.a j - P.a i) * P.normalizedQuadratic j v / 2 + P.calibration j - P.calibration i = 0 := by
  have he : P.normalizedQuadratic i v = P.normalizedQuadratic j v := le_antisymm (hi.2 j) (hj.2 i)
  have h₁ := P.calibration_matches_cell hi
  have h₂ := P.calibration_matches_cell hj
  rw [he] at h₁
  nlinarith

/-- The source's exponent matching at every positive-level active tie. This
explicitly includes u=0, because normalization divides only by F>0. -/
theorem calibration_active_eq {i j : Fin m} {x : Vec 2}
    (hi : P.Active i x) (hj : P.Active j x) (hx : 0 < P.objective x) :
    P.a i * (x 0)^2 / (2 * P.objective x) + P.calibration i =
      P.a j * (x 0)^2 / (2 * P.objective x) + P.calibration j := by
  obtain ⟨hei, hci⟩ := P.active_normalized_cell hi hx
  obtain ⟨hej, hcj⟩ := P.active_normalized_cell hj hx
  have h₁ := P.calibration_matches_cell hci
  have h₂ := P.calibration_matches_cell hcj
  rw [hei] at h₁
  rw [hej] at h₂
  have he := h₁.symm.trans h₂
  convert he using 1 <;> ring

/-- Q.7 follows at any positive switching interface. No adjacency or envelope
pruning premise is required in this stronger pairwise interface identity. -/
theorem calibration_interface_identity (ξ : ℝ) {i j : Fin m}
    (hi : P.Active i ![(1 : ℝ), ξ]) (hj : P.Active j ![(1 : ℝ), ξ]) :
    P.calibration j - P.calibration i =
      -(P.a j - P.a i) / (2 * P.objective ![(1 : ℝ), ξ]) := by
  have hp : 0 < P.objective ![(1 : ℝ), ξ] := by
    have h := P.quadratic_lower_bound P.minQuadratic_le ![(1 : ℝ), ξ]
    simp only [Matrix.cons_val_zero, one_pow, mul_one] at h
    exact P.minQuadratic_pos.trans_le h
  have he := P.calibration_active_eq hi hj hp
  simp only [Matrix.cons_val_zero, one_pow, mul_one] at he
  have hn : 2 * P.objective ![(1 : ℝ), ξ] ≠ 0 := by positivity
  apply (eq_div_iff hn).mpr
  field_simp at he
  nlinarith

end Family
end Parabolic
end BfgsVerification
