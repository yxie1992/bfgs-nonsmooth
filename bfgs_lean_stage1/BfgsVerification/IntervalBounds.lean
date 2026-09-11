import Mathlib
/-! Elementary real interval bounds, checked by the kernel. Generated rational endpoints are proof candidates only. -/
noncomputable section
namespace BfgsVerification.IntervalBounds

def Bounds (a x b : ℝ) : Prop := a ≤ x ∧ x ≤ b

theorem exact (a : ℝ) : Bounds a a a := ⟨le_refl a,le_refl a⟩
theorem add {a x b c y d : ℝ} (hx : Bounds a x b) (hy : Bounds c y d) :
    Bounds (a+c) (x+y) (b+d) := ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩
theorem neg {a x b : ℝ} (hx : Bounds a x b) : Bounds (-b) (-x) (-a) :=
  ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
theorem sub {a x b c y d : ℝ} (hx : Bounds a x b) (hy : Bounds c y d) :
    Bounds (a-d) (x-y) (b-c) := ⟨sub_le_sub hx.1 hy.2,sub_le_sub hx.2 hy.1⟩
theorem mul_nn {a x b c y d : ℝ} (hx : Bounds a x b) (hy : Bounds c y d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : Bounds (a*c) (x*y) (b*d) := by
  exact ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩
theorem mul_np {a x b c y d : ℝ} (hx : Bounds a x b) (hy : Bounds c y d)
    (ha : 0 ≤ a) (hd : d ≤ 0) : Bounds (b*c) (x*y) (a*d) := by
  have h := neg (mul_nn hx (neg hy) ha (neg_nonneg.mpr hd))
  simpa only [mul_neg,neg_neg] using h

theorem mul_pn {a x b c y d : ℝ} (hx : Bounds a x b) (hy : Bounds c y d)
    (hb : b ≤ 0) (hc : 0 ≤ c) : Bounds (a*d) (x*y) (b*c) := by
  have h := mul_np hy hx hc hb
  simpa only [mul_comm] using h

theorem mul_pp {a x b c y d : ℝ} (hx : Bounds a x b) (hy : Bounds c y d)
    (hb : b ≤ 0) (hd : d ≤ 0) : Bounds (b*d) (x*y) (a*c) := by
  have h := mul_nn (neg hx) (neg hy) (neg_nonneg.mpr hb) (neg_nonneg.mpr hd)
  simpa only [neg_mul_neg] using h

theorem inv_pos {a x b : ℝ} (hx : Bounds a x b) (ha : 0 < a) :
    Bounds b⁻¹ x⁻¹ a⁻¹ := by
  have hx0 := ha.trans_le hx.1
  exact ⟨inv_anti₀ hx0 hx.2,inv_anti₀ ha hx.1⟩
end BfgsVerification.IntervalBounds
