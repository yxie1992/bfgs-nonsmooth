import BfgsVerification.RootClusterConservation

noncomputable section
open scoped BigOperators
namespace BfgsVerification.RootClusterConservation

/-- Finite-cluster bookkeeping only; no polynomial decomposition is assumed or asserted. -/
def FiniteConservationTarget : Prop :=
  ∀n m : ℕ, ∀c : Fin n → Fin m, ∀w : Fin n → ℕ, ∀cap : Fin m → ℕ,
    (∀b, 0 < cap b) →
    (∀b, fiberWeight Finset.univ c w b ≤ cap b) →
    (∑a, w a = ∑b, cap b) →
    ∀b, fiberWeight Finset.univ c w b=cap b ∧ ∃a, c a=b

theorem finiteConservation : FiniteConservationTarget := by
  intro n m c w cap hp hle he b
  have hc : ∀a ∈ (Finset.univ : Finset (Fin n)), c a ∈ (Finset.univ : Finset (Fin m)) := by simp
  have hm := fun b (_ : b ∈ (Finset.univ : Finset (Fin m))) => hp b
  have hl := fun b (_ : b ∈ (Finset.univ : Finset (Fin m))) => hle b
  refine ⟨fiberWeight_eq_capacity hc hl he b (Finset.mem_univ b),?_⟩
  obtain ⟨a,_,ha⟩ := every_label_hit hc hm hl he b (Finset.mem_univ b)
  exact ⟨a,ha⟩

def FiniteBijectionTarget : Prop :=
  ∀n m : ℕ, ∀c : Fin n → Fin m, ∀w : Fin n → ℕ, ∀cap : Fin m → ℕ,
    (∀b, 0 < cap b) →
    (∀b, fiberWeight Finset.univ c w b ≤ cap b) →
    (∑a, w a = ∑b, cap b) → n=m →
    Function.Bijective c ∧ ∀a, w a=cap (c a)

theorem finiteBijection : FiniteBijectionTarget := by
  intro n m c w cap hp hle he hcard
  exact fintype_bijective_and_weights hp hle he (by simpa only [Fintype.card_fin] using hcard)

end BfgsVerification.RootClusterConservation
