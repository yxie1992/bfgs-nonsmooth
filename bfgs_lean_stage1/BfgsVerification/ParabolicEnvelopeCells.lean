import BfgsVerification.ParabolicEnvelopeIntervals

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

/-- The affine graph of branch i on the normalized level-one arc. -/
def normalizedQuadratic (i : Fin m) (v : ℝ) : ℝ := (1 - P.b i * v) / P.a i

def normalLeft : ℝ := (P.b (Classical.choose P.negative_slope))⁻¹
def normalRight : ℝ := (P.b (Classical.choose P.positive_slope))⁻¹

theorem normalLeft_neg : P.normalLeft < 0 := inv_lt_zero.mpr (Classical.choose_spec P.negative_slope)
theorem normalRight_pos : 0 < P.normalRight := inv_pos.mpr (Classical.choose_spec P.positive_slope)

/-- Closed cells of the finite affine lower envelope on a bounded interval
containing the normalized arc. Empty cells are allowed in this definition. -/
def envelopeCell (i : Fin m) : Set ℝ :=
  {v | v ∈ Icc P.normalLeft P.normalRight ∧ ∀ j, P.normalizedQuadratic i v ≤ P.normalizedQuadratic j v}

theorem normalizedQuadratic_continuous (i : Fin m) : Continuous (P.normalizedQuadratic i) := by
  unfold normalizedQuadratic
  fun_prop

theorem normalizedQuadratic_combo (i : Fin m) (v w α β : ℝ) (hab : α + β = 1) :
    P.normalizedQuadratic i (α * v + β * w) =
      α * P.normalizedQuadratic i v + β * P.normalizedQuadratic i w := by
  unfold normalizedQuadratic
  field_simp [(P.a_pos i).ne']
  nlinarith [hab]

theorem envelopeCell_convex (i : Fin m) : Convex ℝ (P.envelopeCell i) := by
  intro v hv w hw α β hα hβ hab
  refine ⟨convex_Icc P.normalLeft P.normalRight hv.1 hw.1 hα hβ hab, ?_⟩
  intro j
  change P.normalizedQuadratic i (α * v + β * w) ≤ P.normalizedQuadratic j (α * v + β * w)
  rw [P.normalizedQuadratic_combo i v w α β hab, P.normalizedQuadratic_combo j v w α β hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (hv.2 j) hα) (mul_le_mul_of_nonneg_left (hw.2 j) hβ)

theorem envelopeCell_closed (i : Fin m) : IsClosed (P.envelopeCell i) := by
  convert (isClosed_Icc : IsClosed (Icc P.normalLeft P.normalRight)).inter (isClosed_iInter (fun j =>
    isClosed_le (P.normalizedQuadratic_continuous i) (P.normalizedQuadratic_continuous j))) using 1
  ext v
  simp [envelopeCell]

theorem envelopeCell_compact (i : Fin m) : IsCompact (P.envelopeCell i) :=
  isCompact_Icc.of_isClosed_subset (P.envelopeCell_closed i) (fun _ h => h.1)

def cellLeft (i : Fin m) : ℝ := sInf (P.envelopeCell i)
def cellRight (i : Fin m) : ℝ := sSup (P.envelopeCell i)

theorem envelopeCell_eq_interval {i : Fin m} (hi : (P.envelopeCell i).Nonempty) :
    P.envelopeCell i = Icc (P.cellLeft i) (P.cellRight i) :=
  eq_Icc_of_connected_compact ((P.envelopeCell_convex i).isConnected hi) (P.envelopeCell_compact i)

theorem cellLeft_mem {i : Fin m} (hi : (P.envelopeCell i).Nonempty) :
    P.cellLeft i ∈ P.envelopeCell i := (P.envelopeCell_compact i).sInf_mem hi

theorem cellRight_mem {i : Fin m} (hi : (P.envelopeCell i).Nonempty) :
    P.cellRight i ∈ P.envelopeCell i := (P.envelopeCell_compact i).sSup_mem hi

theorem cellLeft_le_right {i : Fin m} (hi : (P.envelopeCell i).Nonempty) :
    P.cellLeft i ≤ P.cellRight i := by
  have h := P.cellLeft_mem hi
  rw [P.envelopeCell_eq_interval hi] at h
  exact h.2

/-- A canonical retained index is the least original index with its exact
coefficient pair. This only removes exact duplicates, not tie-only branches. -/
def Canonical (i : Fin m) : Prop := ∀ j, P.a j = P.a i → P.b j = P.b i → i ≤ j

def coefficientFiber (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => P.a j = P.a i ∧ P.b j = P.b i)

theorem coefficientFiber_nonempty (i : Fin m) : (P.coefficientFiber i).Nonempty := by
  classical
  exact ⟨i, by simp [coefficientFiber]⟩

def canonicalIndex (i : Fin m) : Fin m := (P.coefficientFiber i).min' (P.coefficientFiber_nonempty i)

theorem canonicalIndex_coefficients (i : Fin m) :
    P.a (P.canonicalIndex i) = P.a i ∧ P.b (P.canonicalIndex i) = P.b i := by
  classical
  have h := Finset.min'_mem (P.coefficientFiber i) (P.coefficientFiber_nonempty i)
  simpa only [coefficientFiber, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem canonicalIndex_canonical (i : Fin m) : P.Canonical (P.canonicalIndex i) := by
  classical
  intro j hja hjb
  have hmem : j ∈ P.coefficientFiber i := by
    simp only [coefficientFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hja.trans (P.canonicalIndex_coefficients i).1, hjb.trans (P.canonicalIndex_coefficients i).2⟩
  exact Finset.min'_le _ j hmem

theorem canonical_unique {i j : Fin m} (hi : P.Canonical i) (hj : P.Canonical j)
    (ha : P.a i = P.a j) (hb : P.b i = P.b j) : i = j :=
  le_antisymm (hi j ha.symm hb.symm) (hj i ha hb)

theorem envelopeCell_eq_of_coefficients {i j : Fin m}
    (ha : P.a i = P.a j) (hb : P.b i = P.b j) : P.envelopeCell i = P.envelopeCell j := by
  ext v
  simp only [envelopeCell, normalizedQuadratic, ha, hb]

/-- Canonical nonempty cells are the only cells counted by the ramp sum. -/
def retainedCells : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => P.Canonical i ∧ (P.envelopeCell i).Nonempty)

theorem mem_retainedCells {i : Fin m} :
    i ∈ P.retainedCells ↔ P.Canonical i ∧ (P.envelopeCell i).Nonempty := by
  classical
  simp [retainedCells]

theorem canonicalIndex_mem_retained {i : Fin m} {v : ℝ} (hv : v ∈ P.envelopeCell i) :
    P.canonicalIndex i ∈ P.retainedCells := by
  rw [P.mem_retainedCells]
  refine ⟨P.canonicalIndex_canonical i, ?_⟩
  rw [P.envelopeCell_eq_of_coefficients (P.canonicalIndex_coefficients i).1 (P.canonicalIndex_coefficients i).2]
  exact ⟨v, hv⟩

/-- Distinct affine branch graphs can coincide at two points only when their
original coefficient pairs were duplicates. -/
theorem coefficients_eq_of_two_cell_points {i j : Fin m} {v w : ℝ}
    (hv : v ∈ P.envelopeCell i ∩ P.envelopeCell j)
    (hw : w ∈ P.envelopeCell i ∩ P.envelopeCell j) (hne : v ≠ w) :
    P.a i = P.a j ∧ P.b i = P.b j := by
  have hev := le_antisymm (hv.1.2 j) (hv.2.2 i)
  have hew := le_antisymm (hw.1.2 j) (hw.2.2 i)
  unfold normalizedQuadratic at hev hew
  have hev' := (div_eq_div_iff (P.a_pos i).ne' (P.a_pos j).ne').mp hev
  have hew' := (div_eq_div_iff (P.a_pos i).ne' (P.a_pos j).ne').mp hew
  have he : (v - w) * (P.a j * P.b i - P.a i * P.b j) = 0 := by nlinarith
  have hcoef : P.a j * P.b i - P.a i * P.b j = 0 :=
    (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
  have ha : P.a i = P.a j := by nlinarith [congrArg (fun z => z * v) hcoef]
  refine ⟨ha, ?_⟩
  rw [ha] at hcoef
  nlinarith [P.a_pos j]

theorem retained_cell_inter_subsingleton {i j : Fin m} (hi : i ∈ P.retainedCells)
    (hj : j ∈ P.retainedCells) (hne : i ≠ j) :
    (P.envelopeCell i ∩ P.envelopeCell j).Subsingleton := by
  intro v hv w hw
  by_contra hvw
  obtain ⟨ha, hb⟩ := P.coefficients_eq_of_two_cell_points hv hw hvw
  exact hne (P.canonical_unique (P.mem_retainedCells.mp hi).1 (P.mem_retainedCells.mp hj).1 ha hb)


/-- Any feasible normalized point lies between the bounds obtained from the
original positive and negative slope witnesses. No intermediate slope is divided by. -/
theorem normalized_normal_bounds {t v : ℝ} (ht : 0 ≤ t)
    (hb : ∀ i, P.a i * t + P.b i * v ≤ 1) : v ∈ Icc P.normalLeft P.normalRight := by
  have hbn := Classical.choose_spec P.negative_slope
  have hbp := Classical.choose_spec P.positive_slope
  have hn := hb (Classical.choose P.negative_slope)
  have hp := hb (Classical.choose P.positive_slope)
  have hqn := mul_nonneg (P.a_pos (Classical.choose P.negative_slope)).le ht
  have hqp := mul_nonneg (P.a_pos (Classical.choose P.positive_slope)).le ht
  constructor
  · change (P.b (Classical.choose P.negative_slope))⁻¹ ≤ v
    rw [← one_div]
    apply (div_le_iff_of_neg hbn).mpr
    nlinarith
  · change v ≤ (P.b (Classical.choose P.positive_slope))⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hbp).mpr
    nlinarith

theorem normalizedQuadratic_identity (i : Fin m) (v : ℝ) :
    P.a i * P.normalizedQuadratic i v + P.b i * v = 1 := by
  unfold normalizedQuadratic
  field_simp [(P.a_pos i).ne']

/-- Feasible normalized active points belong to the corresponding closed cell,
including points with zero quadratic coordinate. -/
theorem normalized_cell_of_active {t v : ℝ} (ht : 0 ≤ t)
    (hb : ∀ i, P.a i * t + P.b i * v ≤ 1) {j : Fin m}
    (hj : P.a j * t + P.b j * v = 1) :
    P.normalizedQuadratic j v = t ∧ v ∈ P.envelopeCell j := by
  have he : P.normalizedQuadratic j v = t := by
    unfold normalizedQuadratic
    apply (div_eq_iff (P.a_pos j).ne').mpr
    nlinarith
  refine ⟨he, P.normalized_normal_bounds ht hb, ?_⟩
  intro i
  rw [he]
  unfold normalizedQuadratic
  apply (le_div_iff₀ (P.a_pos i)).mpr
  nlinarith [hb i]

theorem active_normalized_cell {j : Fin m} {x : Vec 2}
    (hj : P.Active j x) (hx : 0 < P.objective x) :
    P.normalizedQuadratic j (x 1 / P.objective x) = (x 0)^2 / P.objective x ∧
      x 1 / P.objective x ∈ P.envelopeCell j := by
  have he (i : Fin m) : P.a i * ((x 0)^2 / P.objective x) + P.b i * (x 1 / P.objective x) =
      P.branch i x / P.objective x := by
    unfold branch
    ring
  apply P.normalized_cell_of_active (div_nonneg (sq_nonneg _) hx.le)
  · intro i
    rw [he i]
    exact (div_le_one hx).mpr (P.branch_le i x)
  · rw [he j, ← hj]
    exact div_self hx.ne'

/-- Every positive-level active branch has a retained exact-coefficient
representative active at the same actual point, with the same gradient. -/
theorem active_retained_representative {j : Fin m} {x : Vec 2}
    (hj : P.Active j x) (hx : 0 < P.objective x) :
    ∃ i ∈ P.retainedCells, P.Active i x ∧ P.branchGradient i x = P.branchGradient j x := by
  refine ⟨P.canonicalIndex j, P.canonicalIndex_mem_retained (P.active_normalized_cell hj hx).2, ?_, ?_⟩
  · simpa only [Active, branch, (P.canonicalIndex_coefficients j).1,
      (P.canonicalIndex_coefficients j).2] using hj
  · simp only [branchGradient, (P.canonicalIndex_coefficients j).1, (P.canonicalIndex_coefficients j).2]

end Family
end Parabolic
end BfgsVerification
