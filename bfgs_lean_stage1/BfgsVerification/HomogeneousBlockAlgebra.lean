import BfgsVerification.HomogeneousPlanarEscape
import BfgsVerification.AffineLifting

/-! Exact opposite-gradient contraction and bounded affine interpolation for
H.7.4. These helpers impose no bound on the number of transitions in a block. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace HomogeneousBlock

theorem dot_smul_first {n : ℕ} (c : ℝ) (g x : Vec n) :
    dot (c • g) x = c * dot g x := by
  simp [dot, Finset.mul_sum, mul_assoc]

/-- Positive multiples active at positive-value points coincide. -/
theorem positive_parallel_supports_eq {n : ℕ} {F : Vec n → ℝ}
    (hh : Homogeneous.PositiveDegreeOne F) (x z g h : Vec n)
    (hg : Homogeneous.Supports F x g) (hhg : Homogeneous.Supports F z h)
    (hx : 0 < F x) (hz : 0 < F z) (c : ℝ) (hc : 0 < c) (he : h = c • g) : h = g := by
  have hex := Homogeneous.supporting_euler hh hg
  have hez := Homogeneous.supporting_euler hh hhg
  have hbx := Homogeneous.supporting_linear_le hh hhg x
  have haz := Homogeneous.supporting_linear_le hh hg z
  rw [he, HomogeneousBlock.dot_smul_first, hex] at hbx
  rw [he, HomogeneousBlock.dot_smul_first] at hez
  have hc1 : c = 1 := by
    have hp := mul_le_mul_of_nonneg_left haz hc.le
    nlinarith
  rw [he, hc1, one_smul]

/-- In dimension two a zero actual determinant gives an actual scalar multiple. -/
theorem exists_smul_of_pairDet_eq_zero (g h : Vec 2) (hg : g ≠ 0)
    (hd : HomogeneousPlanar.pairDet g h = 0) : ∃ c : ℝ, h = c • g := by
  by_cases h0 : g 0 = 0
  · have h1 : g 1 ≠ 0 := by
      intro h1
      apply hg
      ext i
      fin_cases i <;> assumption
    have hh0 : h 0 = 0 := by
      dsimp [HomogeneousPlanar.pairDet] at hd
      rw [h0, zero_mul, zero_sub] at hd
      exact (mul_eq_zero.mp (neg_eq_zero.mp hd)).resolve_left h1
    refine ⟨h 1 / g 1, ?_⟩
    ext i
    fin_cases i
    · simp [h0, hh0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨h 0 / g 0, ?_⟩
    ext i
    fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff h0).mpr
      change h 1 * g 0 = h 0 * g 1
      dsimp [HomogeneousPlanar.pairDet] at hd
      nlinarith

/-- The source interpolation bound uses the positive old value and the first
opposite-transition contraction; it does not assume θ lies between zero and one. -/
theorem interpolation_parameter_bound {n : ℕ} (g a b x : Vec n)
    (f κ c θ : ℝ) (hf : 0 < f) (hκ : 0 < κ) (hc : 0 < c)
    (ha : dot g a = f) (hb : dot g b ≤ (1-c)*f)
    (hxlow : -f/κ ≤ dot g x) (hxhigh : dot g x ≤ f)
    (hx : x = a + θ • (b-a)) :
    0 ≤ θ ∧ θ ≤ (1+1/κ)/c := by
  have hd : dot g b - f < 0 := by nlinarith
  have hid : dot g x = f + θ*(dot g b-f) := by
    rw [hx]
    change g ⬝ᵥ (a + θ • (b-a)) = _
    rw [dotProduct_add, dotProduct_smul, dotProduct_sub]
    change dot g a + θ*(dot g b-dot g a) = _
    rw [ha]
  have hθ : 0 ≤ θ := by nlinarith
  refine ⟨hθ, (le_div_iff₀ hc).mpr ?_⟩
  have hm := mul_le_mul_of_nonneg_left hb hθ
  have hdiv : f/κ = f*(1/κ) := by ring
  rw [neg_div, hdiv] at hxlow
  nlinarith

/-- Bounded affine interpolation controls every intermediate point by the two
endpoints, even for arbitrarily long blocks and θ exceeding one. -/
theorem interpolation_norm_bound {n : ℕ} (a b x : Vec n) (θ C : ℝ)
    (hθ : 0 ≤ θ) (hC : θ ≤ C) (hx : x = a + θ • (b-a)) :
    ‖x‖ ≤ (1+C)*‖a‖ + C*‖b‖ := by
  rw [hx]
  calc
    ‖a + θ • (b-a)‖ ≤ ‖a‖ + ‖θ • (b-a)‖ := norm_add_le _ _
    _ = ‖a‖ + θ*‖b-a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    _ ≤ ‖a‖ + θ*(‖b‖+‖a‖) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hθ) _
    _ ≤ (1+C)*‖a‖ + C*‖b‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hC (add_nonneg (norm_nonneg b) (norm_nonneg a))]

end HomogeneousBlock
namespace AdmissibleBFGSRun

/-- Every dependent planar transition on a positive homogeneous branch is
between opposite slopes. No finite alphabet is needed for this local statement. -/
theorem homogeneous_dependent_transition_opposite {F : Vec 2 → ℝ}
    (R : AdmissibleBFGSRun 2 F) (hh : Homogeneous.PositiveDegreeOne F)
    (hp : ∀ k, 0 < F (R.x k)) (k : ℕ)
    (hd : HomogeneousPlanar.pairDet (R.g k) (R.g (k+1)) = 0) :
    ∃ κ : ℝ, 0 < κ ∧ R.g (k+1) = -κ • R.g k := by
  obtain ⟨c, hc⟩ := HomogeneousBlock.exists_smul_of_pairDet_eq_zero
    (R.g k) (R.g (k+1)) (R.gradient_nonzero k) hd
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, zero_smul] at hc
    exact R.gradient_nonzero (k+1) hc
  have hcneg : c < 0 := by
    by_contra hn
    have hpos : 0 < c := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hc0)
    have he := HomogeneousBlock.positive_parallel_supports_eq hh
      (R.x k) (R.x (k+1)) (R.g k) (R.g (k+1))
      (convex_supporting_inequality R.convex (R.hasGradient k))
      (convex_supporting_inequality R.convex (R.hasGradient (k+1))) (hp k) (hp (k+1)) c hpos hc
    exact R.gradient_transition_ne k he.symm
  exact ⟨-c, neg_pos.mpr hcneg, by simpa only [neg_neg] using hc⟩

/-- The opposite-transition decrease is exactly the sum of the two scaled
positive endpoint values. -/
theorem homogeneous_opposite_decrease {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (hh : Homogeneous.PositiveDegreeOne F)
    (k : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : R.g (k+1) = -κ • R.g k) :
    R.d k = F (R.x k) + F (R.x (k+1))/κ := by
  have he := R.homogeneous_euler hh (k+1)
  rw [hg, HomogeneousBlock.dot_smul_first, R.homogeneous_old_endpoint_pairing hh] at he
  have hd : R.d k - F (R.x k) = F (R.x (k+1))/κ := by
    apply (eq_div_iff hκ.ne').mpr
    nlinarith
  linarith

/-- The exact Armijo contraction of the first opposite transition in a block. -/
theorem homogeneous_opposite_contraction {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (hh : Homogeneous.PositiveDegreeOne F)
    (k : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : R.g (k+1) = -κ • R.g k)
    (hp : 0 ≤ F (R.x k)) :
    F (R.x (k+1)) ≤ ((1-R.c₁)/(1+R.c₁/κ))*F (R.x k) ∧
      F (R.x (k+1)) ≤ (1-R.c₁)*F (R.x k) := by
  have hd := R.homogeneous_opposite_decrease hh k κ hκ hg
  have ha := R.armijo_decrease k
  rw [hd] at ha
  have hden : 0 < 1+R.c₁/κ :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg R.c₁_pos.le hκ.le)
  have hc1 : R.c₁ < 1 := R.c₁_lt_c₂.trans R.c₂_lt_one
  have hfirst : F (R.x (k+1)) ≤ ((1-R.c₁)/(1+R.c₁/κ))*F (R.x k) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    have hid : F (R.x (k+1)) * (1+R.c₁/κ) =
        F (R.x (k+1)) + R.c₁*(F (R.x (k+1))/κ) := by ring
    rw [hid]
    nlinarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hp
  apply (div_le_iff₀ hden).mpr
  have hhpos : 0 ≤ (1-R.c₁)*(R.c₁/κ) :=
    mul_nonneg (sub_nonneg.mpr hc1.le) (div_nonneg R.c₁_pos.le hκ.le)
  nlinarith

end AdmissibleBFGSRun
end BfgsVerification
