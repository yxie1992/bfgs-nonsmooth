import BfgsVerification.ParabolicEnvelopePruning
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

structure PrunedOrder where
  count : ℕ
  count_pos : 0 < count
  index : Fin count → Fin m
  essential : ∀ i, P.Essential (index i)
  covers : ∀ i, P.Essential i → ∃ k, index k = i
  slopes_strictMono : StrictMono (fun i => P.b (index i))

def prunedOrder : P.PrunedOrder := by
  classical
  let S := P.essentialIndices.image P.b
  let e := S.orderEmbOfFin rfl
  have hS : S.Nonempty := P.essentialIndices_nonempty.image P.b
  have hrep : ∀ k : Fin S.card, ∃ i, P.Essential i ∧ P.b i = e k := by
    intro k
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (S.orderEmbOfFin_mem rfl k)
    exact ⟨i, by simpa [essentialIndices] using hi, he⟩
  choose idx hi hb using hrep
  refine ⟨S.card, Finset.card_pos.mpr hS, idx, hi, ?_, ?_⟩
  · intro i he
    have hmem : P.b i ∈ S := Finset.mem_image.mpr ⟨i, by simpa [essentialIndices] using he, rfl⟩
    have hrange : P.b i ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hmem
    obtain ⟨k, hk⟩ := hrange
    exact ⟨k, P.essential_slopes_injective (hi k) he ((hb k).trans hk)⟩
  · intro i j hij
    change P.b (idx i) < P.b (idx j)
    rw [hb i, hb j]
    exact e.strictMono hij

def Adjacent (i j : Fin m) : Prop := P.Essential i ∧ P.Essential j ∧ P.b i < P.b j ∧
  ∀ k, P.Essential k → P.b k ≤ P.b i ∨ P.b j ≤ P.b k

theorem PrunedOrder.adjacent (O : P.PrunedOrder) {i j : Fin O.count}
    (hij : j.val = i.val+1) : P.Adjacent (O.index i) (O.index j) := by
  refine ⟨O.essential i, O.essential j, O.slopes_strictMono (by change i.val<j.val; omega), ?_⟩
  intro k hk
  obtain ⟨l, rfl⟩ := O.covers k hk
  have hl : l ≤ i ∨ j ≤ l := by
    change l.val ≤ i.val ∨ j.val ≤ l.val
    omega
  exact hl.imp (fun h => O.slopes_strictMono.monotone h) (fun h => O.slopes_strictMono.monotone h)

def breakpoint (i j : Fin m) : ℝ := (P.a i-P.a j)/(P.b j-P.b i)

theorem breakpoint_profile_eq {i j : Fin m} (hij : P.b i < P.b j) :
    P.profile i (P.breakpoint i j) = P.profile j (P.breakpoint i j) := by
  unfold profile breakpoint
  field_simp [(sub_pos.mpr hij).ne']
  <;> ring

theorem strict_profile_left_of_breakpoint {i j : Fin m} {ξ : ℝ}
    (hij : P.b i < P.b j) (hξ : P.profile j ξ < P.profile i ξ) : ξ < P.breakpoint i j := by
  apply (lt_div_iff₀ (sub_pos.mpr hij)).mpr
  dsimp [profile] at hξ
  nlinarith

theorem strict_profile_right_of_breakpoint {i j : Fin m} {ξ : ℝ}
    (hij : P.b i < P.b j) (hξ : P.profile i ξ < P.profile j ξ) : P.breakpoint i j < ξ := by
  apply (div_lt_iff₀ (sub_pos.mpr hij)).mpr
  dsimp [profile] at hξ
  nlinarith

theorem adjacent_breakpoint_active {i j : Fin m} (hij : P.Adjacent i j) :
    P.ProfileActive i (P.breakpoint i j) ∧ P.ProfileActive j (P.breakpoint i j) := by
  obtain ⟨ξ, hξ⟩ := hij.1.2
  obtain ⟨ζ, hζ⟩ := hij.2.1.2
  have hne : i ≠ j := by intro he; subst j; exact (lt_irrefl _ hij.2.2.1)
  have hleft : ξ < P.breakpoint i j :=
    P.strict_profile_left_of_breakpoint hij.2.2.1 (hξ j hij.2.1.1 hne.symm)
  have hright : P.breakpoint i j < ζ :=
    P.strict_profile_right_of_breakpoint hij.2.2.1 (hζ i hij.1.1 hne)
  have heq := P.breakpoint_profile_eq hij.2.2.1
  obtain ⟨k, hk, hactive⟩ := P.exists_essential_profileActive (P.breakpoint i j)
  have hki : P.profile k (P.breakpoint i j) ≤ P.profile i (P.breakpoint i j) := by
    by_contra hgt
    have hgt' := lt_of_not_ge hgt
    rcases hij.2.2.2 k hk with hki | hjk
    · by_cases hkiEq : k = i
      · subst k
        exact (lt_irrefl _ hgt')
      have hxi := hξ k hk.1 hkiEq
      have hprod := mul_nonneg (sub_nonneg.mpr hki) (sub_nonneg.mpr hleft.le)
      dsimp [profile] at hxi hgt'
      nlinarith
    · by_cases hkjEq : k = j
      · subst k
        exact (not_lt_of_ge heq.ge) hgt'
      have hzj := hζ k hk.1 hkjEq
      have hprod := mul_nonneg (sub_nonneg.mpr hjk) (sub_nonneg.mpr hright.le)
      rw [heq] at hgt'
      dsimp [profile] at hzj hgt'
      nlinarith
  constructor
  · intro l
    exact (hactive l).trans hki
  · intro l
    exact ((hactive l).trans hki).trans_eq heq

theorem adjacent_breakpoints_increasing {i j k : Fin m}
    (hij : P.Adjacent i j) (hjk : P.Adjacent j k) : P.breakpoint i j < P.breakpoint j k := by
  obtain ⟨ξ, hξ⟩ := hij.2.1.2
  have hijne : i ≠ j := by intro h; have hb := hij.2.2.1; rw [h] at hb; exact lt_irrefl _ hb
  have hkjne : k ≠ j := by intro h; have hb := hjk.2.2.1; rw [h] at hb; exact lt_irrefl _ hb
  exact (P.strict_profile_right_of_breakpoint hij.2.2.1 (hξ i hij.1.1 hijne)).trans
    (P.strict_profile_left_of_breakpoint hjk.2.2.1 (hξ k hjk.2.1.1 hkjne))

theorem profileActive_iff_active_one (i : Fin m) (ξ : ℝ) :
    P.ProfileActive i ξ ↔ P.Active i ![(1 : ℝ), ξ] := by
  constructor
  · intro h
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      simpa only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        one_pow, mul_one, profile] using h j
    · exact P.branch_le i _
  · intro h j
    have hh := P.branch_le j ![(1 : ℝ), ξ]
    rw [h] at hh
    simpa only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_pow, mul_one, profile] using hh

theorem adjacent_breakpoint_value_pos {i j : Fin m} (hij : P.Adjacent i j) :
    0 < P.profile i (P.breakpoint i j) := by
  have hi := (P.profileActive_iff_active_one i _).mp (P.adjacent_breakpoint_active hij).1
  have h := P.quadratic_lower_bound P.minQuadratic_le ![(1 : ℝ), P.breakpoint i j]
  rw [hi] at h
  simp only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_pow, mul_one] at h
  exact P.minQuadratic_pos.trans_le h

theorem adjacent_calibration {i j : Fin m} (hij : P.Adjacent i j) :
    P.calibration j-P.calibration i =
      -(P.a j-P.a i)/(2*P.profile i (P.breakpoint i j)) := by
  obtain ⟨hi, hj⟩ := P.adjacent_breakpoint_active hij
  have hi' := (P.profileActive_iff_active_one i _).mp hi
  have hj' := (P.profileActive_iff_active_one j _).mp hj
  have h := P.calibration_interface_identity (P.breakpoint i j) hi' hj'
  rw [hi'] at h
  simpa only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_pow, mul_one, profile] using h

theorem PrunedOrder.consecutive_breakpoints_increasing (O : P.PrunedOrder)
    {i j k : Fin O.count} (hij : j.val = i.val+1) (hjk : k.val = j.val+1) :
    P.breakpoint (O.index i) (O.index j) < P.breakpoint (O.index j) (O.index k) :=
  P.adjacent_breakpoints_increasing (O.adjacent P hij) (O.adjacent P hjk)

end Family
end Parabolic
end BfgsVerification
