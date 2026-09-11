import BfgsVerification.SignPatternIndicators

noncomputable section
open scoped BigOperators
namespace BfgsVerification.RealAlgebraicGeometry

/-- Number of elements with one simultaneous sign pattern. -/
def finiteSignCount {α : Type*} {m : ℕ} (S : Finset α)
    (h : α → Fin m → SignType) (σ : Fin m → SignType) : ℕ := by
  classical
  exact (S.filter (fun a => h a=σ)).card

/-- Signed power moment on the same actual finite set. -/
def finiteSignMoment {α : Type*} {m : ℕ} (S : Finset α)
    (h : α → Fin m → SignType) (e : Fin m → Fin 3) : ℚ :=
  ∑a∈S,∏i,(h a i : ℚ)^(e i).val

/-- Exact rational inversion of all simultaneous finite sign counts from
moments with exponents 0, 1 and 2. -/
theorem finite_sign_count_from_moments {α : Type*} {m : ℕ} (S : Finset α)
    (h : α → Fin m → SignType) (σ : Fin m → SignType) :
    (finiteSignCount S h σ : ℚ)=
      ∑e : Fin m → Fin 3,signPatternCoeff σ e * finiteSignMoment S h e := by
  classical
  have hc : (finiteSignCount S h σ : ℚ)=∑a∈S,if h a=σ then (1 : ℚ) else 0 := by
    simp [finiteSignCount]
  rw [hc]
  simp_rw [← sign_pattern_indicator σ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [finiteSignMoment,Finset.mul_sum]

theorem finiteSignCount_pos_iff {α : Type*} {m : ℕ} (S : Finset α)
    (h : α → Fin m → SignType) (σ : Fin m → SignType) :
    0<finiteSignCount S h σ ↔ ∃a∈S,h a=σ := by
  classical
  simp [finiteSignCount,Finset.card_pos,Finset.filter_nonempty_iff]

/-- Positivity of the explicit rational moment expression detects one common
witness for all signs. Separate existential witnesses are not combined. -/
theorem exists_sign_pattern_iff_moment_positive {α : Type*} {m : ℕ} (S : Finset α)
    (h : α → Fin m → SignType) (σ : Fin m → SignType) :
    (∃a∈S,h a=σ) ↔
      0<∑e : Fin m → Fin 3,signPatternCoeff σ e * finiteSignMoment S h e := by
  rw [← finite_sign_count_from_moments,← finiteSignCount_pos_iff]
  exact Nat.cast_pos.symm

/-- Equal power moments force equality of every simultaneous sign count. -/
theorem finite_sign_counts_eq_of_moments_eq {α β : Type*} {m : ℕ}
    (S : Finset α) (T : Finset β) (h : α → Fin m → SignType) (k : β → Fin m → SignType)
    (he : ∀e,finiteSignMoment S h e=finiteSignMoment T k e) :
    ∀σ,finiteSignCount S h σ=finiteSignCount T k σ := by
  intro σ
  apply Nat.cast_injective (R := ℚ)
  simp_rw [finite_sign_count_from_moments,he]

theorem finiteSignCount_empty_pattern {α : Type*} (S : Finset α)
    (h : α → Fin 0 → SignType) (σ : Fin 0 → SignType) : finiteSignCount S h σ=S.card := by
  classical
  have hh : ∀a,h a=σ := fun _ => Subsingleton.elim _ _
  simp [finiteSignCount,hh]

theorem finiteSignCount_empty_set {α : Type*} {m : ℕ}
    (h : α → Fin m → SignType) (σ : Fin m → SignType) : finiteSignCount ∅ h σ=0 := by
  simp [finiteSignCount]

end BfgsVerification.RealAlgebraicGeometry
