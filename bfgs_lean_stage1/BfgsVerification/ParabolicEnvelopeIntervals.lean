import BfgsVerification.ParabolicFamily

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace Parabolic
namespace Envelope

/-- Length of the portion of [l,r] lying to the left of v. -/
def ramp (l r v : ℝ) : ℝ := max 0 (min v r - l)

theorem ramp_of_mem {l r v : ℝ} (hv : v ∈ Icc l r) : ramp l r v = v - l := by
  rw [ramp, min_eq_left hv.2, max_eq_right (sub_nonneg.mpr hv.1)]

theorem ramp_of_le_left {l r v : ℝ} (hv : v ≤ l) : ramp l r v = 0 := by
  apply max_eq_left
  linarith [min_le_left v r]

theorem ramp_of_right_le {l r v : ℝ} (hlr : l ≤ r) (hv : r ≤ v) : ramp l r v = r - l := by
  rw [ramp, min_eq_right hv, max_eq_right (sub_nonneg.mpr hlr)]

theorem ramp_degenerate (p v : ℝ) : ramp p p v = 0 := by
  apply max_eq_left
  linarith [min_le_right v p]

/-- Two nondegenerate closed intervals with at most one common point have
disjoint interiors and one lies entirely to the left of the other. -/
theorem intervals_ordered_of_subsingleton {l r p q : ℝ} (hlr : l < r) (hpq : p < q)
    (hsub : (Icc l r ∩ Icc p q).Subsingleton) : r ≤ p ∨ q ≤ l := by
  by_contra hn
  have hpr : p < r := lt_of_not_ge (fun h => hn (Or.inl h))
  have hlq : l < q := lt_of_not_ge (fun h => hn (Or.inr h))
  have hlt : max l p < min r q := lt_min (max_lt hlr hpr) (max_lt hlq hpq)
  have hmax : max l p ∈ Icc l r ∩ Icc p q := by
    constructor <;> constructor
    · exact le_max_left _ _
    · exact hlt.le.trans (min_le_left _ _)
    · exact le_max_right _ _
    · exact hlt.le.trans (min_le_right _ _)
  have hmin : min r q ∈ Icc l r ∩ Icc p q := by
    constructor <;> constructor
    · exact (le_max_left _ _).trans hlt.le
    · exact min_le_left _ _
    · exact (le_max_right _ _).trans hlt.le
    · exact min_le_right _ _
  exact hlt.ne (hsub hmax hmin)

/-- A different cell's ramp is constant on a cell when their intersection has
at most one point. Degenerate cells contribute zero length. -/
theorem ramp_constant_on_cell {l r p q : ℝ} (hlr : l ≤ r) (hpq : p ≤ q)
    (hsub : (Icc l r ∩ Icc p q).Subsingleton)
    {v w : ℝ} (hv : v ∈ Icc l r) (hw : w ∈ Icc l r) : ramp p q v = ramp p q w := by
  rcases eq_or_lt_of_le hlr with he | hlr
  · have hv' : v = l := by rw [← he] at hv; exact le_antisymm hv.2 hv.1
    have hw' : w = l := by rw [← he] at hw; exact le_antisymm hw.2 hw.1
    rw [hv', hw']
  rcases eq_or_lt_of_le hpq with he | hpq
  · subst q
    rw [ramp_degenerate, ramp_degenerate]
  rcases intervals_ordered_of_subsingleton hlr hpq hsub with hrp | hql
  · rw [ramp_of_le_left (hv.2.trans hrp), ramp_of_le_left (hw.2.trans hrp)]
  · rw [ramp_of_right_le hpq.le (hql.trans hv.1), ramp_of_right_le hpq.le (hql.trans hw.1)]

/-- A nonnegative affine deficit controls an affine error on a compact interval
if all its zeros are also zeros of the error. This covers zero endpoint deficits
and singleton cells without a division by either one. -/
theorem affine_deficit_bound (l r d₀ d₁ e₀ e₁ : ℝ) (hlr : l ≤ r)
    (hd : ∀ v ∈ Icc l r, 0 ≤ d₀ + d₁ * v)
    (hz : ∀ v ∈ Icc l r, d₀ + d₁ * v = 0 → e₀ + e₁ * v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ Icc l r, |e₀ + e₁ * v| ≤ C * (d₀ + d₁ * v) := by
  have hep : ∀ v ∈ Icc l r, ∃ C : ℝ, 0 < C ∧ |e₀ + e₁ * v| ≤ C * (d₀ + d₁ * v) := by
    intro v hv
    by_cases hzero : d₀ + d₁ * v = 0
    · exact ⟨1, zero_lt_one, by rw [hz v hv hzero, hzero]; simp⟩
    have hpos : 0 < d₀ + d₁ * v := lt_of_le_of_ne (hd v hv) (Ne.symm hzero)
    refine ⟨|e₀ + e₁ * v| / (d₀ + d₁ * v) + 1, by positivity, ?_⟩
    have he := div_mul_cancel₀ |e₀ + e₁ * v| hzero
    nlinarith
  obtain ⟨C₀, hC₀, he₀⟩ := hep l ⟨le_rfl, hlr⟩
  obtain ⟨C₁, hC₁, he₁⟩ := hep r ⟨hlr, le_rfl⟩
  let C := max C₀ C₁
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  have hl : |e₀ + e₁ * l| ≤ C * (d₀ + d₁ * l) :=
    he₀.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hd l ⟨le_rfl, hlr⟩))
  have hr : |e₀ + e₁ * r| ≤ C * (d₀ + d₁ * r) :=
    he₁.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hd r ⟨hlr, le_rfl⟩))
  refine ⟨C, hC, ?_⟩
  intro v hv
  rcases eq_or_lt_of_le hlr with hsame | hlt
  · have hv' : v = l := by rw [← hsame] at hv; exact le_antisymm hv.2 hv.1
    rwa [hv']
  let t := (v - l) / (r - l)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hv.1) (sub_pos.mpr hlt).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hlt)).mpr (by linarith [hv.2])
  have hcomb : (1 - t) * l + t * r = v := by
    dsimp [t]
    field_simp [(sub_pos.mpr hlt).ne']
    <;> ring
  have he : e₀ + e₁ * v = (1 - t) * (e₀ + e₁ * l) + t * (e₀ + e₁ * r) := by
    nlinarith [congrArg (fun z => e₁ * z) hcomb]
  rw [he]
  calc
    |(1 - t) * (e₀ + e₁ * l) + t * (e₀ + e₁ * r)| ≤
        |(1 - t) * (e₀ + e₁ * l)| + |t * (e₀ + e₁ * r)| := abs_add _ _
    _ = (1 - t) * |e₀ + e₁ * l| + t * |e₀ + e₁ * r| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1 - t) * (C * (d₀ + d₁ * l)) + t * (C * (d₀ + d₁ * r)) :=
      add_le_add (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hr ht0)
    _ = C * (d₀ + d₁ * v) := by nlinarith [congrArg (fun z => C * d₁ * z) hcomb]

end Envelope
end Parabolic
end BfgsVerification
