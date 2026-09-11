import BfgsVerification.ParabolicEnvelopeScale
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Literal strict-cell pruning of the original finite affine upper profile.
This is separate from the ramp construction used in the principal theorem. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

def profile (i : Fin m) (ξ : ℝ) : ℝ := P.a i+P.b i*ξ
def ProfileActive (i : Fin m) (ξ : ℝ) : Prop := ∀ j, P.profile j ξ ≤ P.profile i ξ

/-- Exactly one copy of a branch that is strictly active on an open profile
cell, compared with the canonical representatives of all original branches. -/
def Essential (i : Fin m) : Prop := P.Canonical i ∧
  ∃ ξ : ℝ, ∀ j, P.Canonical j → j ≠ i → P.profile j ξ < P.profile i ξ

def essentialIndices : Finset (Fin m) := by
  classical
  exact Finset.univ.filter P.Essential

def profileCrossings : Finset ℝ := by
  classical
  exact Finset.univ.image (fun ij : Fin m × Fin m => (P.a ij.1-P.a ij.2)/(P.b ij.2-P.b ij.1))

theorem profile_continuous (i : Fin m) : Continuous (P.profile i) := by unfold profile; fun_prop

theorem exists_profileActive (ξ : ℝ) : ∃ i, P.ProfileActive i ξ := by
  obtain ⟨i, hi⟩ := P.exists_active ![(1 : ℝ), ξ]
  refine ⟨i, ?_⟩
  intro j
  have h := P.branch_le j ![(1 : ℝ), ξ]
  rw [hi] at h
  simpa only [Family.branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_pow, mul_one, profile] using h

theorem profileActive_canonical {i : Fin m} {ξ : ℝ} (hi : P.ProfileActive i ξ) :
    P.ProfileActive (P.canonicalIndex i) ξ := by
  intro j
  simpa only [profile, (P.canonicalIndex_coefficients i).1,
    (P.canonicalIndex_coefficients i).2] using hi j

theorem essential_of_active_off_crossings {i : Fin m} {ξ : ℝ}
    (hi : P.Canonical i) (ha : P.ProfileActive i ξ) (hξ : ξ ∉ P.profileCrossings) : P.Essential i := by
  classical
  refine ⟨hi, ξ, ?_⟩
  intro j hj hji
  apply lt_of_le_of_ne (ha j)
  intro he
  have hbi : P.b i ≠ P.b j := by
    intro hb
    have hab : P.a i = P.a j := by dsimp [profile] at he; rw [hb] at he; linarith
    exact hji (P.canonical_unique hj hi hab.symm hb.symm)
  have heξ : ξ = (P.a i-P.a j)/(P.b j-P.b i) := by
    apply (eq_div_iff (sub_ne_zero.mpr hbi.symm)).mpr
    dsimp [profile] at he
    nlinarith
  apply hξ
  rw [heξ]
  exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩

/-- Tie-only, redundant, and duplicate pieces can all be removed while
preserving the complete real affine upper envelope, including every tie. -/
theorem exists_essential_profileActive (ξ : ℝ) : ∃ i, P.Essential i ∧ P.ProfileActive i ξ := by
  classical
  have hclosed : IsClosed {ξ : ℝ | ∃ i, P.Essential i ∧ P.ProfileActive i ξ} := by
    simp only [setOf_exists]
    apply isClosed_iUnion_of_finite
    intro i
    by_cases he : P.Essential i
    · simp only [he, true_and]
      simp only [ProfileActive, setOf_forall]
      exact isClosed_iInter (fun j => isClosed_le (P.profile_continuous j) (P.profile_continuous i))
    · simp only [he, false_and, setOf_false]
      exact isClosed_empty
  have hd : Dense ((P.profileCrossings : Set ℝ)ᶜ) :=
    (P.profileCrossings.finite_toSet.countable).dense_compl ℝ
  have hsub : (P.profileCrossings : Set ℝ)ᶜ ⊆ {ξ : ℝ | ∃ i, P.Essential i ∧ P.ProfileActive i ξ} := by
    intro ξ hξ
    obtain ⟨i, hi⟩ := P.exists_profileActive ξ
    have hc := P.profileActive_canonical hi
    exact ⟨P.canonicalIndex i, P.essential_of_active_off_crossings (P.canonicalIndex_canonical i) hc hξ, hc⟩
  have hcl := hd.mono hsub
  simpa only [hclosed.closure_eq] using hcl ξ

theorem essentialIndices_nonempty : P.essentialIndices.Nonempty := by
  classical
  obtain ⟨i, hi, _⟩ := P.exists_essential_profileActive 0
  exact ⟨i, by simpa [essentialIndices] using hi⟩

/-- Equal normal slopes cannot both survive strict-cell pruning. -/
theorem essential_slopes_injective {i j : Fin m} (hi : P.Essential i) (hj : P.Essential j)
    (hb : P.b i = P.b j) : i = j := by
  by_contra hij
  obtain ⟨ξ, hξ⟩ := hi.2
  obtain ⟨ζ, hζ⟩ := hj.2
  have hx := hξ j hj.1 (fun h => hij h.symm)
  have hz := hζ i hi.1 hij
  dsimp [profile] at hx hz
  rw [hb] at hx hz
  linarith

theorem exists_essential_active_of_horizontal_ne_zero {x : Vec 2} (hx : x 0 ≠ 0) :
    ∃ i, P.Essential i ∧ P.Active i x := by
  obtain ⟨i, hi, hact⟩ := P.exists_essential_profileActive (x 1/(x 0)^2)
  refine ⟨i, hi, le_antisymm ?_ (P.branch_le i x)⟩
  apply Finset.sup'_le
  intro j _
  have he (l : Fin m) : P.branch l x = (x 0)^2*P.profile l (x 1/(x 0)^2) := by
    unfold branch profile
    field_simp [hx]
    <;> ring
  rw [he j, he i]
  exact mul_le_mul_of_nonneg_left (hact j) (sq_nonneg _)

theorem essential_active_set_closed : IsClosed {x : Vec 2 | ∃ i, P.Essential i ∧ P.Active i x} := by
  classical
  simp only [setOf_exists]
  apply isClosed_iUnion_of_finite
  intro i
  by_cases he : P.Essential i
  · simp only [he, true_and]
    exact isClosed_eq P.objective_continuous (continuous_iff_continuousAt.mpr (fun x => (P.branch_hasGradient i x).continuousAt))
  · simp only [he, false_and, setOf_false]
    exact isClosed_empty

/-- The strict-cell representatives retain the actual objective at every
point, including u=0 where normalization by u² is unavailable. -/
theorem exists_essential_active (x : Vec 2) : ∃ i, P.Essential i ∧ P.Active i x := by
  let p : ℝ → Vec 2 := fun ε => ![x 0+ε, x 1]
  have hp : Continuous p := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun ε : ℝ => x 0+ε)
      fun_prop
    · change Continuous (fun _ : ℝ => x 1)
      fun_prop
  have hc : IsClosed {ε : ℝ | ∃ i, P.Essential i ∧ P.Active i (p ε)} :=
    P.essential_active_set_closed.preimage hp
  have hd : Dense ({-x 0}ᶜ : Set ℝ) := (Set.countable_singleton _).dense_compl ℝ
  have hsub : ({-x 0}ᶜ : Set ℝ) ⊆ {ε : ℝ | ∃ i, P.Essential i ∧ P.Active i (p ε)} := by
    intro ε hε
    have hne : (p ε) 0 ≠ 0 := by
      change x 0+ε ≠ 0
      have hn : ε ≠ -x 0 := hε
      intro he
      apply hn
      linarith
    exact P.exists_essential_active_of_horizontal_ne_zero hne
  have hzero := (hd.mono hsub) (0 : ℝ)
  rw [hc.closure_eq] at hzero
  have hp0 : p 0 = x := by ext i; fin_cases i <;> simp [p]
  change ∃ i, P.Essential i ∧ P.Active i (p 0) at hzero
  simpa only [hp0] using hzero

def prunedObjective (x : Vec 2) : ℝ :=
  P.essentialIndices.sup' P.essentialIndices_nonempty (fun i => P.branch i x)

theorem prunedObjective_eq (x : Vec 2) : P.prunedObjective x = P.objective x := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact P.branch_le i x
  · obtain ⟨i, hi, hactive⟩ := P.exists_essential_active x
    rw [hactive]
    apply Finset.le_sup' (fun j => P.branch j x)
    simpa [essentialIndices] using hi

theorem essential_active_gradient {x g : Vec 2}
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    ∃ i ∈ P.essentialIndices, P.Active i x ∧ P.branchGradient i x = g := by
  classical
  obtain ⟨i, hi, hactive⟩ := P.exists_essential_active x
  exact ⟨i, by simpa [essentialIndices] using hi, hactive, P.active_eq_gradient hactive hg⟩

end Family
end Parabolic
end BfgsVerification
