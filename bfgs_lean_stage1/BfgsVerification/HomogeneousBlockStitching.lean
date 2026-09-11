import BfgsVerification.HomogeneousBlockControl

/-! Pure sequence stitching across unrestricted finite blocks. Actual BFGS
block bounds and actual anchor asymptotics will discharge these hypotheses. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace HomogeneousBlock

/-- Consecutive anchors straddle every sufficiently late index, and uniformly
bounded interpolation between vanishing endpoints forces the entire sequence
to zero. No bound on the gap between anchors is required. -/
theorem tendsto_zero_of_anchor_blocks {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (p : ℕ → Prop)
    (hcofinal : ∀ K, ∃ j, K ≤ j ∧ p j)
    (hanchor : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j, J ≤ j → p j → ‖x j‖ < ε)
    (C : ℝ) (hC : 0 ≤ C)
    (hblock : ∀ a b, a < b → p a → p b → (∀ j, a < j → j < b → ¬p j) →
      ∀ k, a ≤ k → k ≤ b → ‖x k‖ ≤ (1+C)*‖x a‖+C*‖x b‖) :
    Tendsto x atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : 0 < 1+2*C := by linarith
  obtain ⟨J, hJ⟩ := hanchor (ε/(1+2*C)) (div_pos hε hden)
  obtain ⟨j₀, hj₀J, hpj₀⟩ := hcofinal J
  refine ⟨j₀, ?_⟩
  intro k hj₀k
  let S := (Finset.range (k+1)).filter p
  have hj₀S : j₀ ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hpj₀⟩
  have hS : S.Nonempty := ⟨j₀, hj₀S⟩
  let a := S.max' hS
  have haS : a ∈ S := S.max'_mem hS
  have hak : a ≤ k := by
    have h := (Finset.mem_filter.mp haS).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp h)
  have hpa : p a := (Finset.mem_filter.mp haS).2
  have hj₀a : j₀ ≤ a := S.le_max' _ hj₀S
  have hfut : ∃ b, k < b ∧ p b := by
    obtain ⟨b, hb, hp⟩ := hcofinal (k+1)
    exact ⟨b, by omega, hp⟩
  let b := Nat.find hfut
  have hkb : k < b := (Nat.find_spec hfut).1
  have hpb : p b := (Nat.find_spec hfut).2
  have hnone : ∀ j, a < j → j < b → ¬p j := by
    intro j haj hjb hpj
    by_cases hjk : j ≤ k
    · have hjS : j ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hpj⟩
      have hja : j ≤ a := S.le_max' _ hjS
      omega
    · exact Nat.find_min hfut hjb ⟨by omega, hpj⟩
  have hbound := hblock a b (by omega) hpa hpb hnone k hak hkb.le
  have hxa := hJ a (by omega) hpa
  have hxb := hJ b (by omega) hpb
  rw [dist_zero_right]
  have hmul₁ := mul_lt_mul_of_pos_left hxa (by linarith : 0 < 1+C)
  have hmul₂ := mul_le_mul_of_nonneg_left hxb.le hC
  have hid : (1+C)*(ε/(1+2*C))+C*(ε/(1+2*C)) = ε := by field_simp; ring
  linarith

end HomogeneousBlock
end BfgsVerification
