import Mathlib

/-! Exact polynomial bump and integrated spline for source Module U.7. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

/-- A checked gluing rule at the single interface of two differentiable pieces. -/
theorem hasDerivAt_join_at {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfg : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) d c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact if_pos ht
    · exact if_pos le_rfl
  have hr : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases he : t = c
      · subst t
        simpa only [if_pos le_rfl] using hfg
      · simp only [if_neg (not_le.mpr (lt_of_le_of_ne ht (fun h => he h.symm)))]
    · simpa only [if_pos le_rfl] using hfg
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

theorem hasDerivAt_join {f g f' g' : ℝ → ℝ} (c : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hfg : f c = g c) (hd : f' c = g' c) (t : ℝ) :
    HasDerivAt (fun u => if u ≤ c then f u else g u) (if t ≤ c then f' t else g' t) t := by
  rcases lt_trichotomy t c with ht | he | ht
  · rw [if_pos ht.le]
    apply (hf t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with u hu
    simp only [if_pos hu.le]
  · subst t
    rw [if_pos le_rfl]
    exact hasDerivAt_join_at (hf c) ((hg c).congr_deriv hd.symm) hfg
  · rw [if_neg (not_le.mpr ht)]
    apply (hg t).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with u hu
    simp only [if_neg (not_le.mpr hu)]

def massPoly (t : ℝ) : ℝ := t - (2/3 : ℝ) * t^3 + (1/5 : ℝ) * t^5

def momentPoly (t : ℝ) : ℝ := (1/2 : ℝ) * t^2 - (1/2 : ℝ) * t^4 + (1/6 : ℝ) * t^6

def bump (t : ℝ) : ℝ := if t ≤ -1 then 0 else if t ≤ 1 then (1-t^2)^2 else 0

def bumpDerivative (t : ℝ) : ℝ := if t ≤ -1 then 0 else if t ≤ 1 then 4*t*(t^2-1) else 0

def cumulativeMass (t : ℝ) : ℝ := if t ≤ -1 then 0 else if t ≤ 1 then massPoly t + 8/15 else 16/15

def primitivePoly (t : ℝ) : ℝ := t * (massPoly t + 8/15) - momentPoly t + 1/6

def primitive (t : ℝ) : ℝ := if t ≤ -1 then 0 else if t ≤ 1 then primitivePoly t else (16/15)*t

theorem massPoly_hasDerivAt (t : ℝ) : HasDerivAt massPoly ((1-t^2)^2) t := by
  convert ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).const_mul (2/3 : ℝ))).add
    (((hasDerivAt_id t).pow 5).const_mul (1/5 : ℝ)) using 1 <;> try simp only [massPoly, id_eq] <;> ring

theorem momentPoly_hasDerivAt (t : ℝ) : HasDerivAt momentPoly (t*(1-t^2)^2) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul (1/2 : ℝ)).sub
    (((hasDerivAt_id t).pow 4).const_mul (1/2 : ℝ))).add
    (((hasDerivAt_id t).pow 6).const_mul (1/6 : ℝ)) using 1 <;> try simp only [momentPoly, id_eq] <;> ring

theorem primitivePoly_hasDerivAt (t : ℝ) : HasDerivAt primitivePoly (massPoly t + 8/15) t := by
  convert (((hasDerivAt_id t).mul ((massPoly_hasDerivAt t).add_const (8/15 : ℝ))).sub
    (momentPoly_hasDerivAt t)).add_const (1/6 : ℝ) using 1 <;> try simp only [primitivePoly, id_eq] <;> ring

theorem bump_poly_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ => (1-u^2)^2) (4*t*(t^2-1)) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 2) using 1 <;> simp only [id_eq] <;> ring

theorem bump_hasDerivAt (t : ℝ) : HasDerivAt bump (bumpDerivative t) t := by
  apply hasDerivAt_join (-1) (fun u => hasDerivAt_const u 0)
    (fun u => hasDerivAt_join 1 bump_poly_hasDerivAt (fun v => hasDerivAt_const v 0)
      (by norm_num) (by norm_num) u) (by norm_num) (by norm_num) t

theorem cumulativeMass_hasDerivAt (t : ℝ) : HasDerivAt cumulativeMass (bump t) t := by
  apply hasDerivAt_join (-1) (fun u => hasDerivAt_const u 0)
    (fun u => hasDerivAt_join 1 (fun v => (massPoly_hasDerivAt v).add_const (8/15 : ℝ))
      (fun v => hasDerivAt_const v (16/15 : ℝ)) (by norm_num [massPoly]) (by norm_num) u)
    (by norm_num [massPoly]) (by norm_num) t

theorem primitive_hasDerivAt (t : ℝ) : HasDerivAt primitive (cumulativeMass t) t := by
  have hr (v : ℝ) : HasDerivAt (fun u : ℝ => (16/15)*u) (16/15) v := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id v).const_mul (16/15 : ℝ)
  apply hasDerivAt_join (-1) (fun u => hasDerivAt_const u 0)
    (fun u => hasDerivAt_join 1 primitivePoly_hasDerivAt hr
      (by norm_num [primitivePoly, massPoly, momentPoly]) (by norm_num [massPoly]) u)
    (by norm_num [primitivePoly, massPoly, momentPoly]) (by norm_num [massPoly]) t

theorem bump_eq_source (t : ℝ) : bump t = if |t| ≤ 1 then (1-t^2)^2 else 0 := by
  by_cases h : |t| ≤ 1
  · obtain ⟨hl, hr⟩ := abs_le.mp h
    by_cases ht : t ≤ -1
    · have he : t = -1 := le_antisymm ht hl
      subst t
      norm_num [bump]
    · simp only [bump, if_neg ht, if_pos hr, if_pos h]
  · by_cases ht : t ≤ -1
    · simp only [bump, if_pos ht, if_neg h]
    · have hr : ¬t ≤ 1 := fun hr => h (abs_le.mpr ⟨(lt_of_not_ge ht).le, hr⟩)
      simp only [bump, if_neg ht, if_neg hr, if_neg h]

theorem bump_nonneg (t : ℝ) : 0 ≤ bump t := by unfold bump; split_ifs <;> positivity

theorem cumulativeMass_monotone : Monotone cumulativeMass :=
  monotone_of_hasDerivAt_nonneg cumulativeMass_hasDerivAt bump_nonneg

theorem cumulativeMass_bounds (t : ℝ) : 0 ≤ cumulativeMass t ∧ cumulativeMass t ≤ 16/15 := by
  by_cases hleft : t ≤ -1
  · norm_num [cumulativeMass, hleft]
  by_cases hright : 1 ≤ t
  · rcases hright.eq_or_lt with rfl | ht
    · norm_num [cumulativeMass, massPoly]
    · norm_num [cumulativeMass, hleft, not_le.mpr ht]
  have hlow := cumulativeMass_monotone (le_of_lt (lt_of_not_ge hleft))
  have hupp := cumulativeMass_monotone (le_of_lt (lt_of_not_ge hright))
  have hm : cumulativeMass (-1) = 0 := by norm_num [cumulativeMass]
  have hp : cumulativeMass 1 = 16/15 := by norm_num [cumulativeMass, massPoly]
  rw [hm] at hlow
  rw [hp] at hupp
  exact ⟨hlow, hupp⟩

theorem bumpDerivative_continuous : Continuous bumpDerivative := by
  have hr : Continuous (fun t : ℝ => if t ≤ 1 then 4*t*(t^2-1) else 0) :=
    Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
      (by intro t ht; norm_num [show t = 1 from ht])
  exact Continuous.if_le continuous_const hr continuous_id continuous_const
    (by intro t ht; norm_num [show t = -1 from ht])

theorem bump_contDiff : ContDiff ℝ 1 bump := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (bump_hasDerivAt t).differentiableAt, ?_⟩
  have he : deriv bump = bumpDerivative := funext fun t => (bump_hasDerivAt t).deriv
  rw [he]
  exact bumpDerivative_continuous

theorem cumulativeMass_continuous : Continuous cumulativeMass :=
  continuous_iff_continuousAt.mpr fun t => (cumulativeMass_hasDerivAt t).continuousAt

theorem primitive_continuous : Continuous primitive :=
  continuous_iff_continuousAt.mpr fun t => (primitive_hasDerivAt t).continuousAt

theorem primitive_monotone : Monotone primitive :=
  monotone_of_hasDerivAt_nonneg primitive_hasDerivAt fun t => (cumulativeMass_bounds t).1

theorem primitive_nonneg (t : ℝ) : 0 ≤ primitive t := by
  by_cases ht : t ≤ -1
  · simp [primitive, ht]
  · have h := primitive_monotone (le_of_lt (lt_of_not_ge ht))
    simpa only [primitive, if_pos le_rfl] using h

theorem primitive_convex : ConvexOn ℝ univ primitive := by
  apply Monotone.convexOn_univ_of_deriv (fun t => (primitive_hasDerivAt t).differentiableAt)
  convert cumulativeMass_monotone using 1
  exact funext fun t => (primitive_hasDerivAt t).deriv

theorem primitive_lipschitz : LipschitzWith (⟨16/15, by norm_num⟩ : NNReal) primitive := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (primitive_hasDerivAt t).differentiableAt)
  intro t
  rw [(primitive_hasDerivAt t).deriv]
  exact_mod_cast (show |cumulativeMass t| ≤ 16/15 by
    rw [abs_of_nonneg (cumulativeMass_bounds t).1]
    exact (cumulativeMass_bounds t).2)

theorem bump_integral (a b : ℝ) :
    (∫ t in a..b, bump t) = cumulativeMass b - cumulativeMass a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => cumulativeMass_hasDerivAt t)
    (bump_contDiff.continuous.intervalIntegrable a b)

theorem bump_total_mass : (∫ t in (-1 : ℝ)..1, bump t) = 16/15 := by
  rw [bump_integral]
  norm_num [cumulativeMass, massPoly]

theorem cumulativeMass_integral (a b : ℝ) :
    (∫ t in a..b, cumulativeMass t) = primitive b - primitive a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => primitive_hasDerivAt t)
    (cumulativeMass_continuous.intervalIntegrable a b)

theorem cumulativeMass_at_zero : cumulativeMass 0 = 8/15 := by
  norm_num [cumulativeMass, massPoly]

theorem primitive_at_zero : primitive 0 = 1/6 := by
  norm_num [primitive, primitivePoly, massPoly, momentPoly]

end BfgsVerification.NormalSpike
