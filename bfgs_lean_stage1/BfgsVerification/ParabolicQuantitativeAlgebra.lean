import BfgsVerification.ParabolicScalarTransport

/-! Explicit rational estimates for the uniform compensated transport proof. -/
noncomputable section
namespace BfgsVerification
namespace Parabolic

/-- A numerator and a positive denominator can be bounded independently. -/
theorem ratio_bound {n N b B : ℝ} (hn : 0 ≤ n) (hnN : n ≤ N)
    (hb : 0 < b) (hbB : b ≤ B) : n/B ≤ N/b := by
  exact (div_le_div_of_nonneg_left hn hb hbB).trans
    (div_le_div_of_nonneg_right hnN hb.le)

theorem cancellation_residual_bound {r α h d u F D R C η : ℝ}
    (hη : 0 < η) (hF : η ≤ F) (hD : D ≠ 0) (hR : 0 ≤ R)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hu : |u| ≤ R) (hh : |h| ≤ C*|D|)
    (he : r-1+α*h = -u*h*d/(F*D)) :
    |r-1+α*h| ≤ (R*C/η)*d := by
  have hFp : 0 < F := hη.trans_le hF
  have hDp : 0 < |D| := abs_pos.mpr hD
  have huF : |u|/F ≤ R/η := ratio_bound (abs_nonneg _) hu hη hF
  have hhD : |h|/|D| ≤ C := (div_le_iff₀ hDp).mpr hh
  rw [he]
  have hid : |-u*h*d/(F*D)| = (|u|/F)*(|h|/|D|)*d := by
    simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg hd, abs_of_pos hFp]
    ring
  rw [hid]
  have hp := mul_le_mul huF hhD (div_nonneg (abs_nonneg _) hDp.le)
    (div_nonneg hR hη.le)
  exact (mul_le_mul_of_nonneg_right hp hd).trans_eq (by ring)

theorem exponent_remainder_bound {a A u h d Δ F Z η amin R : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (hη : 0 < η) (hF : η ≤ F) (hZ : η ≤ Z)
    (hamin : 0 < amin) (hd : 0 ≤ d) (hΔ : 0 ≤ Δ) (hΔd : Δ ≤ d)
    (hh : h^2 ≤ d/amin) (hu : u^2 ≤ R^2) :
    |a*h^2/(2*F)+a*u^2*Δ/(2*F*Z)| ≤
      (A/(2*η*amin)+A*R^2/(2*η^2))*d := by
  have hA : 0 ≤ A := ha.trans haA
  have hFp : 0 < F := hη.trans_le hF
  have hZp : 0 < Z := hη.trans_le hZ
  have hn1 : a*h^2 ≤ (A/amin)*d := by
    calc
      a*h^2 ≤ A*h^2 := mul_le_mul_of_nonneg_right haA (sq_nonneg _)
      _ ≤ A*(d/amin) := mul_le_mul_of_nonneg_left hh hA
      _ = _ := by ring
  have hn2 : a*u^2*Δ ≤ (A*R^2)*d :=
    mul_le_mul (mul_le_mul haA hu (sq_nonneg _) hA) hΔd hΔ (mul_nonneg hA (sq_nonneg R))
  have ht1 := ratio_bound (mul_nonneg ha (sq_nonneg h)) hn1
    (show 0 < 2*η by positivity) (show 2*η ≤ 2*F by linarith)
  have hden : 2*η^2 ≤ 2*F*Z := by nlinarith [mul_le_mul hF hZ hη.le hFp.le]
  have ht2 := ratio_bound (mul_nonneg (mul_nonneg ha (sq_nonneg u)) hΔ) hn2
    (show 0 < 2*η^2 by positivity) hden
  rw [abs_of_nonneg (by positivity : 0 ≤ a*h^2/(2*F)+a*u^2*Δ/(2*F*Z))]
  convert add_le_add ht1 ht2 using 1 <;> ring

theorem close_multiplier_of_small_decrease {r K d : ℝ} (hK : 0 ≤ K)
    (hd : 0 ≤ d) (hdsmall : d ≤ 1/(4*(K+1))) (hsq : (r-1)^2 ≤ K*d) :
    |r-1| ≤ 1/2 ∧ 0 < r := by
  have hden : 0 < 4*(K+1) := by positivity
  have hh := (le_div_iff₀ hden).mp hdsmall
  have hab : |r-1| ≤ 1/2 := by nlinarith [sq_abs (r-1), abs_nonneg (r-1)]
  refine ⟨hab, ?_⟩
  have hlo := (abs_le.mp hab).1
  linarith

end Parabolic
end BfgsVerification
