import BfgsVerification.ParabolicEnvelopeCalibration
import BfgsVerification.ParabolicPairs

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

def envelopeDeficit (i j : Fin m) (v : ℝ) : ℝ :=
  1 - P.a i * P.normalizedQuadratic j v - P.b i * v

def envelopeExponentDifference (i j : Fin m) (v : ℝ) : ℝ :=
  (P.a j - P.a i) * P.normalizedQuadratic j v / 2 + P.calibration j - P.calibration i

theorem envelopeDeficit_affine (i j : Fin m) (v : ℝ) :
    P.envelopeDeficit i j v =
      (1 - P.a i / P.a j) + (P.a i * P.b j / P.a j - P.b i) * v := by
  unfold envelopeDeficit normalizedQuadratic
  ring

theorem envelopeExponentDifference_affine (i j : Fin m) (v : ℝ) :
    P.envelopeExponentDifference i j v =
      ((P.a j - P.a i) / 2 / P.a j + P.calibration j - P.calibration i) +
        (-(P.a j - P.a i) / 2 * (P.b j / P.a j)) * v := by
  unfold envelopeExponentDifference normalizedQuadratic
  ring

theorem envelopeDeficit_nonneg (i : Fin m) {j : Fin m} {v : ℝ}
    (hj : v ∈ P.envelopeCell j) : 0 ≤ P.envelopeDeficit i j v := by
  have hi := P.normalizedQuadratic_identity i v
  have hm := mul_le_mul_of_nonneg_left (hj.2 i) (P.a_pos i).le
  unfold envelopeDeficit
  linarith

/-- Every zero of the deficit on a cell is an actual tie of normalized branch
values, and therefore a zero of the calibrated exponent error. -/
theorem envelopeExponentDifference_zero_of_deficit_zero {i j : Fin m} {v : ℝ}
    (hj : v ∈ P.envelopeCell j) (hz : P.envelopeDeficit i j v = 0) :
    P.envelopeExponentDifference i j v = 0 := by
  have hid := P.normalizedQuadratic_identity i v
  have he : P.normalizedQuadratic i v = P.normalizedQuadratic j v := by
    unfold envelopeDeficit at hz
    nlinarith [P.a_pos i]
  have hi : v ∈ P.envelopeCell i := by
    refine ⟨hj.1, ?_⟩
    intro k
    rw [he]
    exact hj.2 k
  exact P.calibration_matches_tie hi hj

/-- The source finite-cell inequality, before taking the uniform finite maximum.
Empty cells are discarded by their proved lack of points; singleton cells remain. -/
theorem cell_pair_deficit_bound (i j : Fin m) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ P.envelopeCell j,
      |P.envelopeExponentDifference i j v| ≤ C * P.envelopeDeficit i j v := by
  by_cases hn : (P.envelopeCell j).Nonempty
  · let d₀ := 1 - P.a i / P.a j
    let d₁ := P.a i * P.b j / P.a j - P.b i
    let e₀ := (P.a j - P.a i) / 2 / P.a j + P.calibration j - P.calibration i
    let e₁ := -(P.a j - P.a i) / 2 * (P.b j / P.a j)
    have hd (v : ℝ) : P.envelopeDeficit i j v = d₀ + d₁ * v := P.envelopeDeficit_affine i j v
    have he (v : ℝ) : P.envelopeExponentDifference i j v = e₀ + e₁ * v :=
      P.envelopeExponentDifference_affine i j v
    obtain ⟨C, hC, hbound⟩ := Envelope.affine_deficit_bound (P.cellLeft j) (P.cellRight j)
      d₀ d₁ e₀ e₁ (P.cellLeft_le_right hn)
      (fun v hv => by
        rw [← hd]
        exact P.envelopeDeficit_nonneg i (by rwa [P.envelopeCell_eq_interval hn]))
      (fun v hv hz => by
        rw [← he]
        exact P.envelopeExponentDifference_zero_of_deficit_zero
          (by rwa [P.envelopeCell_eq_interval hn]) (by rwa [hd]))
    refine ⟨C, hC, ?_⟩
    intro v hv
    rw [hd, he]
    exact hbound v (by rwa [← P.envelopeCell_eq_interval hn])
  · exact ⟨1, zero_lt_one, fun v hv => (hn ⟨v, hv⟩).elim⟩

/-- One finite constant controls every original index pair. No adjacency,
nonzero normal slope, or retained-index assumption is present. -/
theorem exists_uniform_cell_deficit_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ i j v, v ∈ P.envelopeCell j →
      |P.envelopeExponentDifference i j v| ≤ C * P.envelopeDeficit i j v := by
  classical
  choose C hC hbound using P.cell_pair_deficit_bound
  let M := ∑ i : Fin m, ∑ j : Fin m, C i j
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hC i j).le))
  refine ⟨M + 1, by linarith, ?_⟩
  intro i j v hv
  have hij : C i j ≤ ∑ k : Fin m, C i k :=
    Finset.single_le_sum (fun k _ => (hC i k).le) (Finset.mem_univ j)
  have hi : (∑ k : Fin m, C i k) ≤ M :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => (hC l k).le)) (Finset.mem_univ i)
  exact (hbound i j v hv).trans (mul_le_mul_of_nonneg_right (by linarith) (P.envelopeDeficit_nonneg i hv))

/-- Q.16 for the actual original parabolic maximum. Calibration and the finite
constant are derived for every input family, including duplicates, tie-only
branches, empty cells, zero normal slopes, and u=0 at positive levels. -/
theorem exists_calibration_deficit_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin m) (z : Vec 2),
      P.Active j z → 0 < P.objective z →
      |(P.a j - P.a i) * (z 0)^2 / (2 * P.objective z) + P.calibration j - P.calibration i| ≤
        C * P.deficit i z / P.objective z := by
  obtain ⟨C, hC, hbound⟩ := P.exists_uniform_cell_deficit_bound
  refine ⟨C, hC, ?_⟩
  intro i j z hj hz
  obtain ⟨ht, hcell⟩ := P.active_normalized_cell hj hz
  have hh := hbound i j (z 1 / P.objective z) hcell
  have hd : P.envelopeDeficit i j (z 1 / P.objective z) = P.deficit i z / P.objective z := by
    unfold envelopeDeficit
    rw [ht]
    unfold deficit branch
    field_simp [hz.ne']
    <;> ring
  have he : P.envelopeExponentDifference i j (z 1 / P.objective z) =
      (P.a j - P.a i) * (z 0)^2 / (2 * P.objective z) + P.calibration j - P.calibration i := by
    unfold envelopeExponentDifference
    rw [ht]
    ring
  rw [hd, he] at hh
  simpa only [mul_div_assoc] using hh

end Family
end Parabolic
end BfgsVerification
