import BfgsVerification.IntervalBounds

noncomputable section
namespace BfgsVerification.LShapeIntervalTools
open IntervalBounds

theorem enlarge {a x b l u : ℝ} (hx : Bounds a x b) (ha : l ≤ a) (hb : b ≤ u) :
    Bounds l x u := ⟨ha.trans hx.1,hx.2.trans hb⟩

theorem mul_corners {a x b c y d l u : ℝ} (hx : Bounds a x b) (hy : Bounds c y d)
    (hlac : l ≤ a*c) (hlad : l ≤ a*d) (hlbc : l ≤ b*c) (hlbd : l ≤ b*d)
    (huac : a*c ≤ u) (huad : a*d ≤ u) (hubc : b*c ≤ u) (hubd : b*d ≤ u) :
    Bounds l (x*y) u := by
  have hlo (z : ℝ) (hc : l ≤ z*c) (hd : l ≤ z*d) : l ≤ z*y := by
    rcases le_total 0 z with hz | hz
    · exact hc.trans (mul_le_mul_of_nonneg_left hy.1 hz)
    · exact hd.trans (mul_le_mul_of_nonpos_left hy.2 hz)
  have hhi (z : ℝ) (hc : z*c ≤ u) (hd : z*d ≤ u) : z*y ≤ u := by
    rcases le_total 0 z with hz | hz
    · exact (mul_le_mul_of_nonneg_left hy.2 hz).trans hd
    · exact (mul_le_mul_of_nonpos_left hy.1 hz).trans hc
  rcases le_total 0 y with hy0 | hy0
  · exact ⟨(hlo a hlac hlad).trans (mul_le_mul_of_nonneg_right hx.1 hy0),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans (hhi b hubc hubd)⟩
  · exact ⟨(hlo b hlbc hlbd).trans (mul_le_mul_of_nonpos_right hx.2 hy0),
      (mul_le_mul_of_nonpos_right hx.1 hy0).trans (hhi a huac huad)⟩

theorem inv_negative {a x b : ℝ} (hx : Bounds a x b) (hb : b < 0) :
    Bounds b⁻¹ x⁻¹ a⁻¹ := by
  have h := IntervalBounds.neg (IntervalBounds.inv_pos (IntervalBounds.neg hx) (neg_pos.mpr hb))
  simpa only [inv_neg,neg_neg] using h

end BfgsVerification.LShapeIntervalTools
