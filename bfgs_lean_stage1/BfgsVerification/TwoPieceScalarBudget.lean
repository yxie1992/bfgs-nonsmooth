import BfgsVerification.Definitions
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators
namespace BfgsVerification.TwoPieceBudget

/-- Scalar consequence of the actual two-piece recurrences. The matrix/run
bridge is a separate obligation; this lemma alone is not a BFGS theorem. -/
theorem uniform_drop {c δ a ψ ψ' : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hδ1 : δ < 1) (ha : 1 < a)
    (harmijo : a * (δ + c * (1-δ)) ≤ δ * ψ)
    (hnext : ψ' = ψ - (ψ-a)/(1-δ)) : ψ' + c < ψ := by
  have hd : 0 < 1-δ := sub_pos.mpr hδ1
  have hca : c*δ < c*a := mul_lt_mul_of_pos_left (hδ1.trans ha) hc
  have hgap : c*(1-δ) < ψ-a := by
    have h1 : c*δ*(1-δ) < c*a*(1-δ) := mul_lt_mul_of_pos_right hca hd
    have h2 : c*a*(1-δ) ≤ δ*(ψ-a) := by nlinarith [harmijo]
    have h3 : δ*(c*(1-δ)) < δ*(ψ-a) := by nlinarith [h1,h2]
    exact (mul_lt_mul_left hδ).mp h3
  have hq : c < (ψ-a)/(1-δ) := (lt_div_iff₀ hd).mpr hgap
  linarith

theorem finite_budget {c : ℝ} (ψ : ℕ → ℝ) (N : ℕ)
    (hdrop : ∀ k < N, ψ (k+1)+c ≤ ψ k) :
    ψ N+(N : ℝ)*c ≤ ψ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun k hk => hdrop k (Nat.lt_succ_of_lt hk))
    have hlast := hdrop N (Nat.lt_succ_self N)
    push_cast
    linarith

theorem no_infinite_scalar_continuation {c : ℝ} (hc : 0 < c)
    (δ a ψ : ℕ → ℝ)
    (hδ : ∀ k, 0 < δ k) (hδ1 : ∀ k, δ k < 1)
    (ha : ∀ k, 1 < a k) (hψ : ∀ k, 1 < ψ k)
    (harmijo : ∀ k, a k*(δ k+c*(1-δ k)) ≤ δ k*ψ k)
    (hnext : ∀ k, ψ (k+1)=ψ k-(ψ k-a k)/(1-δ k)) : False := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((ψ 0-1)/c)
  have hNc : ψ 0-1 < (N : ℝ)*c := (div_lt_iff₀ hc).mp hN
  have hb := finite_budget ψ N (fun k _ =>
    (uniform_drop hc (hδ k) (hδ1 k) (ha k) (harmijo k) (hnext k)).le)
  linarith [hψ N]

end BfgsVerification.TwoPieceBudget
