import BfgsVerification.TwoPieceRecurrences
import Mathlib.Order.WellFounded

noncomputable section
namespace BfgsVerification.TwoPieceBudget

structure State where
  x : Vec 2
  H : Mat 2
  g : Vec 2
  positive : H.PosDef
  derivative : HasFDerivAt objective (gradientFunctional g) x

theorem State.gradient_nonzero (S : State) : S.g ≠ 0 := by
  intro h
  have he := (actual_gradient_shape S.derivative).1
  rw [h] at he
  norm_num at he

/-- Actual ordinary full-BFGS transition, including the accepted objective
and derivative tests. The states impose no convergence or spectral bounds. -/
def Step (c₁ c₂ : ℝ) (S T : State) : Prop := ∃ α : ℝ, 0 < α ∧
  T.x=S.x+bfgsStep S.H S.g α ∧
  T.H=inverseBFGS S.H (bfgsStep S.H S.g α) (T.g-S.g) ∧
  objective T.x ≤ objective S.x+c₁*dot S.g (bfgsStep S.H S.g α) ∧
  c₂*dot S.g (bfgsStep S.H S.g α) ≤ dot T.g (bfgsStep S.H S.g α)

def runOfChain {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (S : ℕ → State) (hs : ∀ k, Step c₁ c₂ (S k) (S (k+1))) :
    AdmissibleBFGSRun 2 objective where
  convex := objective_convex
  x k := (S k).x
  H k := (S k).H
  g k := (S k).g
  α k := (hs k).choose
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := (S 0).positive
  alpha_pos k := (hs k).choose_spec.1
  gradient_nonzero k := (S k).gradient_nonzero
  hasGradient k := (S k).derivative
  step k := (hs k).choose_spec.2.1
  update k := (hs k).choose_spec.2.2.1
  armijo k := (hs k).choose_spec.2.2.2.1
  weak_wolfe k := (hs k).choose_spec.2.2.2.2

/-- Every sequence of actual accepted transitions is finite: the reverse
transition relation is well founded, for every valid fixed pair of constants. -/
theorem wellFounded_actual_steps {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    WellFounded (fun T S => Step c₁ c₂ S T) := by
  apply WellFounded.wellFounded_iff_no_descending_seq.mpr
  refine ⟨?_⟩
  rintro ⟨S,hs⟩
  exact no_infinite_actual_run (runOfChain hc₁ hc hc₂ S hs)

theorem finite_path_to_terminal {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (S : State) :
    ∃ T : State, Relation.ReflTransGen (Step c₁ c₂) S T ∧
      ¬∃ U : State, Step c₁ c₂ T U := by
  obtain ⟨T,hT,hmin⟩ := (wellFounded_actual_steps hc₁ hc hc₂).has_min
    {T : State | Relation.ReflTransGen (Step c₁ c₂) S T} ⟨S,Relation.ReflTransGen.refl⟩
  refine ⟨T,hT,?_⟩
  rintro ⟨U,hU⟩
  exact hmin U (hT.tail hU) hU

end BfgsVerification.TwoPieceBudget
