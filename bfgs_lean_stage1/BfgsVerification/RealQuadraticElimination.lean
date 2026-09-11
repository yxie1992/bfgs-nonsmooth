import BfgsVerification.SemialgebraicGraphs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact scalar elimination for quadratic fibers over the reals. Degenerate
linear and constant fibers are included explicitly in every equivalence. -/
noncomputable section
open Set Filter
namespace BfgsVerification
namespace RealAlgebraicGeometry

def quadraticValue (a b c t : ℝ) : ℝ := a*t^2+b*t+c

theorem quadratic_square_identity (a b c t : ℝ) :
    4*a*quadraticValue a b c t=(2*a*t+b)^2-(b^2-4*a*c) := by
  unfold quadraticValue
  ring

theorem quadratic_vertex_identity {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    4*a*quadraticValue a b c (-b/(2*a))=-(b^2-4*a*c) := by
  rw [quadratic_square_identity]
  have he : 2*a*(-b/(2*a))+b=0 := by field_simp; ring
  rw [he]
  ring

theorem exists_quadratic_zero_iff (a b c : ℝ) :
    (∃ t : ℝ, quadraticValue a b c t=0) ↔
      (a=0 ∧ (b≠0 ∨ c=0)) ∨ (a≠0 ∧ 0≤b^2-4*a*c) := by
  by_cases ha : a=0
  · subst a
    simp only [quadraticValue,zero_mul,zero_add,true_and,ne_eq,not_true_eq_false,false_and,
      or_false]
    constructor
    · rintro ⟨t,ht⟩
      by_cases hb : b=0
      · exact Or.inr (by simpa [hb] using ht)
      · exact Or.inl hb
    · rintro (hb|hc)
      · refine ⟨-c/b,?_⟩
        rw [mul_div_cancel₀ _ hb]
        ring
      · exact ⟨0,by simp [hc]⟩
  · constructor
    · rintro ⟨t,ht⟩
      right
      refine ⟨ha,?_⟩
      have he := quadratic_square_identity a b c t
      rw [ht,mul_zero] at he
      nlinarith [sq_nonneg (2*a*t+b)]
    · rintro (⟨he,_⟩ | ⟨_,hd⟩)
      · exact (ha he).elim
      · obtain ⟨t,ht⟩ := _root_.exists_quadratic_eq_zero ha
          ⟨Real.sqrt (b^2-4*a*c),by simpa [discrim,sq] using (Real.sq_sqrt hd).symm⟩
        exact ⟨t,by simpa [quadraticValue,sq] using ht⟩

theorem exists_quadratic_positive_of_leading_pos {a : ℝ} (ha : 0<a) (b c : ℝ) :
    ∃ t : ℝ, 0<quadraticValue a b c t := by
  have ht : Tendsto (fun x : ℝ => (a*x+b)*x+c) atTop atTop :=
    tendsto_atTop_add_const_right _ c <|
      (tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)).atTop_mul_atTop₀ tendsto_id
  obtain ⟨t,ht⟩ := (ht.eventually (eventually_gt_atTop 0)).exists
  refine ⟨t,?_⟩
  unfold quadraticValue
  nlinarith [ht]

theorem exists_affine_positive_iff (b c : ℝ) :
    (∃ t : ℝ, 0<b*t+c) ↔ b≠0 ∨ 0<c := by
  by_cases hb : b=0
  · simp [hb]
  · constructor
    · exact fun _ => Or.inl hb
    · intro _
      refine ⟨(1-c)/b,?_⟩
      rw [mul_div_cancel₀ _ hb]
      linarith

theorem exists_affine_nonnegative_iff (b c : ℝ) :
    (∃ t : ℝ, 0≤b*t+c) ↔ b≠0 ∨ 0≤c := by
  by_cases hb : b=0
  · simp [hb]
  · constructor
    · exact fun _ => Or.inl hb
    · intro _
      refine ⟨-c/b,?_⟩
      rw [mul_div_cancel₀ _ hb]
      linarith

theorem exists_concave_quadratic_positive_iff {a : ℝ} (ha : a<0) (b c : ℝ) :
    (∃ t : ℝ, 0<quadraticValue a b c t) ↔ 0<b^2-4*a*c := by
  constructor
  · rintro ⟨t,ht⟩
    have hmul : 4*a*quadraticValue a b c t<0 :=
      mul_neg_of_neg_of_pos (by linarith) ht
    rw [quadratic_square_identity] at hmul
    linarith [sq_nonneg (2*a*t+b)]
  · intro hd
    refine ⟨-b/(2*a),?_⟩
    have he := quadratic_vertex_identity ha.ne b c
    by_contra! hq
    have hmul : 0≤4*a*quadraticValue a b c (-b/(2*a)) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hq
    linarith

theorem exists_concave_quadratic_nonnegative_iff {a : ℝ} (ha : a<0) (b c : ℝ) :
    (∃ t : ℝ, 0≤quadraticValue a b c t) ↔ 0≤b^2-4*a*c := by
  constructor
  · rintro ⟨t,ht⟩
    have hmul : 4*a*quadraticValue a b c t≤0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) ht
    rw [quadratic_square_identity] at hmul
    linarith [sq_nonneg (2*a*t+b)]
  · intro hd
    refine ⟨-b/(2*a),?_⟩
    have he := quadratic_vertex_identity ha.ne b c
    by_contra! hq
    have hmul : 0<4*a*quadraticValue a b c (-b/(2*a)) :=
      mul_pos_of_neg_of_neg (by linarith) hq
    linarith

theorem exists_quadratic_positive_iff (a b c : ℝ) :
    (∃ t : ℝ, 0<quadraticValue a b c t) ↔
      0<a ∨ (a=0 ∧ (b≠0 ∨ 0<c)) ∨ (a<0 ∧ 0<b^2-4*a*c) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · simpa only [ha,ha.ne,not_lt_of_gt ha,false_or,false_and,true_and] using
      exists_concave_quadratic_positive_iff ha b c
  · subst a
    simpa only [quadraticValue,zero_mul,zero_add,lt_self_iff_false,false_or,
      true_and,true_or,eq_self,false_and,or_false] using exists_affine_positive_iff b c
  · exact iff_of_true (exists_quadratic_positive_of_leading_pos ha b c) (Or.inl ha)

theorem exists_quadratic_nonnegative_iff (a b c : ℝ) :
    (∃ t : ℝ, 0≤quadraticValue a b c t) ↔
      0<a ∨ (a=0 ∧ (b≠0 ∨ 0≤c)) ∨ (a<0 ∧ 0≤b^2-4*a*c) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · simpa only [ha,ha.ne,not_lt_of_gt ha,false_or,false_and,true_and] using
      exists_concave_quadratic_nonnegative_iff ha b c
  · subst a
    simpa only [quadraticValue,zero_mul,zero_add,lt_self_iff_false,false_or,
      true_and,true_or,eq_self,false_and,or_false] using exists_affine_nonnegative_iff b c
  · obtain ⟨t,ht⟩ := exists_quadratic_positive_of_leading_pos ha b c
    exact iff_of_true ⟨t,ht.le⟩ (Or.inl ha)

end RealAlgebraicGeometry
end BfgsVerification
