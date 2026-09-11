import BfgsVerification.RationalRootOrder
import Mathlib.Algebra.Ring.Parity

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem inverse_sub_pow_tendsto_right (a : ℝ) {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun x : ℝ => ((x-a)⁻¹)^m) (𝓝[>] a) atTop :=
  (tendsto_pow_atTop hm).comp (inverse_sub_tendsto_right a)

theorem inverse_sub_pow_tendsto_left_even (a : ℝ) {m : ℕ}
    (hm : m ≠ 0) (he : Even m) :
    Tendsto (fun x : ℝ => ((x-a)⁻¹)^m) (𝓝[<] a) atTop := by
  have h := (tendsto_pow_atTop hm).comp
    (tendsto_neg_atBot_atTop.comp (inverse_sub_tendsto_left a))
  simpa only [Function.comp_def, he.neg_pow] using h

theorem inverse_sub_pow_tendsto_left_odd (a : ℝ) {m : ℕ} (ho : Odd m) :
    Tendsto (fun x : ℝ => ((x-a)⁻¹)^m) (𝓝[<] a) atBot := by
  have h := (tendsto_pow_atTop (by rintro rfl; exact Nat.not_odd_zero ho : m ≠ 0)).comp
    (tendsto_neg_atBot_atTop.comp (inverse_sub_tendsto_left a))
  have hn := tendsto_neg_atTop_atBot.comp h
  simpa only [Function.comp_def, ho.neg_pow, neg_neg] using hn

theorem localCauchyIndex_of_same_atTop {f : ℝ → ℝ} {a : ℝ}
    (hr : Tendsto f (𝓝[>] a) atTop) (hl : Tendsto f (𝓝[<] a) atTop) :
    localCauchyIndex f a = 0 := by
  have hnr := hr.not_tendsto disjoint_atTop_atBot
  have hnl := hl.not_tendsto disjoint_atTop_atBot
  simp [localCauchyIndex, hnr, hnl]

theorem localCauchyIndex_of_same_atBot {f : ℝ → ℝ} {a : ℝ}
    (hr : Tendsto f (𝓝[>] a) atBot) (hl : Tendsto f (𝓝[<] a) atBot) :
    localCauchyIndex f a = 0 := by
  have hnr := hr.not_tendsto disjoint_atBot_atTop
  have hnl := hl.not_tendsto disjoint_atBot_atTop
  simp [localCauchyIndex, hnr, hnl]

theorem normalized_power_pole_pos_right {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hc : 0 < c)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[>] a) atTop := by
  have hr := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_gt hx))
  apply (hr.pos_mul_atTop hc (inverse_sub_pow_tendsto_right a hm)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
  field_simp

theorem normalized_power_pole_neg_right {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hc : c < 0)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[>] a) atBot := by
  have hr := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_gt hx))
  apply (hr.neg_mul_atTop hc (inverse_sub_pow_tendsto_right a hm)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
  field_simp

theorem normalized_power_pole_pos_left_even {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (hm : m ≠ 0) (he : Even m) (hc : 0 < c)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[<] a) atTop := by
  have hl := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  apply (hl.pos_mul_atTop hc (inverse_sub_pow_tendsto_left_even a hm he)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
  field_simp

theorem normalized_power_pole_neg_left_even {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (hm : m ≠ 0) (he : Even m) (hc : c < 0)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[<] a) atBot := by
  have hl := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  apply (hl.neg_mul_atTop hc (inverse_sub_pow_tendsto_left_even a hm he)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
  field_simp

theorem normalized_power_pole_pos_left_odd {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (ho : Odd m) (hc : 0 < c)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[<] a) atBot := by
  have hl := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  apply ((inverse_sub_pow_tendsto_left_odd a ho).atBot_mul_pos hc hl).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
  field_simp

theorem normalized_power_pole_neg_left_odd {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (ho : Odd m) (hc : c < 0)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[<] a) atTop := by
  have hl := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  apply ((inverse_sub_pow_tendsto_left_odd a ho).atBot_mul_neg hc hl).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
  field_simp

theorem localCauchyIndex_normalized_power {f : ℝ → ℝ} {a c : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hc : c ≠ 0)
    (h : Tendsto (fun x => (x-a)^m*f x) (𝓝[≠] a) (𝓝 c)) :
    localCauchyIndex f a = if Odd m then (SignType.sign c : ℤ) else 0 := by
  rcases lt_or_gt_of_ne hc with hn | hp
  · have hr := normalized_power_pole_neg_right hm hn h
    rcases Nat.even_or_odd m with he | ho
    · rw [if_neg (Nat.not_odd_iff_even.mpr he)]
      exact localCauchyIndex_of_same_atBot hr (normalized_power_pole_neg_left_even hm he hn h)
    · rw [if_pos ho, sign_neg hn]
      exact localCauchyIndex_of_negative_pole hr (normalized_power_pole_neg_left_odd ho hn h)
  · have hr := normalized_power_pole_pos_right hm hp h
    rcases Nat.even_or_odd m with he | ho
    · rw [if_neg (Nat.not_odd_iff_even.mpr he)]
      exact localCauchyIndex_of_same_atTop hr (normalized_power_pole_pos_left_even hm he hp h)
    · rw [if_pos ho, sign_pos hp]
      exact localCauchyIndex_of_positive_pole hr (normalized_power_pole_pos_left_odd ho hp h)

end RealAlgebraicGeometry
end BfgsVerification
