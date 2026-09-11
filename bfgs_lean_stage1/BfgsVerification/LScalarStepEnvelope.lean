import BfgsVerification.LScalarStepAssembly

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalarStep
open LScalarGeometric

def line (b : ℝ) (n : ℕ) (x : ℝ) : ℝ := scale n*x+(1-b)*(scale n)^2

theorem positivePart_interval_sum {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    positivePart b x = component b m x+line b (m+1) x := by
  have he := (summable_component hl hr x).sum_add_tsum_nat_add (m+1)
  have hzero : ∑ n ∈ Finset.range m, component b n x = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact earlier_component_zero hl hr (Finset.mem_range.mp hn) hxhi
  rw [Finset.sum_range_succ, hzero, zero_add, tail_components hl hr m hxlo] at he
  change _ = positivePart b x at he
  simpa only [line, scale_succ, pow_one] using he.symm

theorem line_difference {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    line b n x-line b (n+1) x = (1-theta)*scale n*(x-LScalar.peak b n) := by
  rw [line, line, scale_succ, peak_formula hb]
  ring

theorem positivePart_interval_max {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    positivePart b x = max (line b (m+1) x) (line b m x) := by
  rw [positivePart_interval_sum hl hr m hxlo hxhi]
  have ha : 0 < (1-theta)*scale m := mul_pos (sub_pos.mpr theta_lt_one) (scale_pos m)
  have he := line_difference (by linarith : 0 < b) m x
  by_cases hx : x ≤ LScalar.peak b m
  · have ht : line b m x ≤ line b (m+1) x := by
      have h := mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hx)
      rw [← he] at h
      linarith
    rw [max_eq_left ht, component, hinge, max_eq_left (sub_nonpos.mpr hx), mul_zero, zero_add]
  · have hx' : LScalar.peak b m ≤ x := le_of_not_ge hx
    have ht : line b (m+1) x ≤ line b m x := by
      have h := mul_nonneg ha.le (sub_nonneg.mpr hx')
      rw [← he] at h
      linarith
    rw [max_eq_right ht, component, hinge, max_eq_right (sub_nonneg.mpr hx')]
    linarith

theorem positivePart_attained {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    ∃ n : ℕ, positivePart b x = line b n x := by
  by_cases hxb : b ≤ x
  · refine ⟨0, ?_⟩
    rw [positivePart_outer hl hr hxb, line, scale_zero]
    ring
  obtain ⟨m,hlo,hhi⟩ := positive_interval_cover (by linarith : 0 < b) hx (le_of_not_ge hxb)
  rw [positivePart_interval_max hl hr m hlo.le hhi]
  by_cases hm : line b m x ≤ line b (m+1) x
  · exact ⟨m+1, max_eq_left hm⟩
  · exact ⟨m,max_eq_right (le_of_not_ge hm)⟩

theorem line_le_phi {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) (x : ℝ) :
    line b n x ≤ phi b x := by
  have hc := phi_convex hl hr
  have hd := phi_node_hasDerivAt hl hr n
  rcases lt_trichotomy x (b*scale n) with hx | hx | hx
  · have h := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ _) hx hd
    rw [slope_def_field, phi_node hl hr n] at h
    have he := (div_le_iff₀ (sub_pos.mpr hx)).mp h
    dsimp [line]
    nlinarith [he]
  · rw [hx, phi_node hl hr n, line]
    nlinarith
  · have h := hc.le_slope_of_hasDerivAt (mem_univ _) (mem_univ x) hx hd
    rw [slope_def_field, phi_node hl hr n] at h
    have he := (le_div_iff₀ (sub_pos.mpr hx)).mp h
    dsimp [line]
    nlinarith [he]

def affineFamily (b : ℝ) : Option ℕ → ℝ → ℝ
  | none, x => -x
  | some n, x => line b n x

theorem phi_countable_max {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    IsGreatest (range (fun i => affineFamily b i x)) (phi b x) := by
  constructor
  · by_cases hx : x ≤ 0
    · exact ⟨none, (phi_eq_negative hl hr hx).symm⟩
    · obtain ⟨n,hn⟩ := positivePart_attained hl hr (lt_of_not_ge hx)
      exact ⟨some n, by simpa only [affineFamily,phi_eq_positive (le_of_not_ge hx)] using hn.symm⟩
  · rintro y ⟨i,rfl⟩
    cases i with
    | none =>
      dsimp [affineFamily, phi]
      have h := positivePart_nonnegative b x
      have hm := le_max_right (0 : ℝ) (-x)
      linarith
    | some n => exact line_le_phi hl hr n x

end BfgsVerification.LScalarStep
