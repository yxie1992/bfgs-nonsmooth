import BfgsVerification.LinearElimination

/-! One-variable elimination with independently strict or weak inequalities.
This includes arbitrary equalities after replacing one equality by two weak
inequalities; empty families and zero coefficients remain covered. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- A marked comparison: true is strict, false is weak. -/
def markedLE (strict : Bool) (x y : ℝ) : Prop := if strict then x < y else x ≤ y

theorem markedLE_of_lt (s : Bool) {x y : ℝ} (h : x < y) : markedLE s x y := by
  cases s <;> simp [markedLE, h.le, h]

theorem markedLE_le {s : Bool} {x y : ℝ} (h : markedLE s x y) : x ≤ y := by
  cases s <;> simp only [markedLE, Bool.false_eq_true, if_false, if_true] at h
  · exact h
  · exact h.le

/-- Exact consistency of a finite collection of marked lower and upper
bounds, including touching weak bounds and empty bound sets. -/
theorem exists_between_finite_marked (lo hi : Finset (ℝ × Bool))
    (h : ∀ l ∈ lo, ∀ u ∈ hi, markedLE (l.2 || u.2) l.1 u.1) :
    ∃ t : ℝ, (∀ l ∈ lo, markedLE l.2 l.1 t) ∧
      ∀ u ∈ hi, markedLE u.2 t u.1 := by
  classical
  by_cases hlo : lo.Nonempty
  · obtain ⟨l,hl,hmax⟩ := Finset.exists_max_image lo Prod.fst hlo
    by_cases hhi : hi.Nonempty
    · obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image hi Prod.fst hhi
      have hlu := markedLE_le (h l hl u hu)
      rcases hlu.eq_or_lt with heq | hlt
      · refine ⟨l.1, ?_, ?_⟩
        · intro q hq
          cases hs : q.2
          · simpa [markedLE, hs] using hmax q hq
          · have hqu := h q hq u hu
            simpa [markedLE, hs, ← heq] using hqu
        · intro q hq
          cases hs : q.2
          · simpa [markedLE, hs, heq] using hmin q hq
          · have hlq := h l hl q hq
            simpa [markedLE, hs] using hlq
      · obtain ⟨t,hlt,hut⟩ := exists_between hlt
        exact ⟨t,fun q hq => markedLE_of_lt _ ((hmax q hq).trans_lt hlt),
          fun q hq => markedLE_of_lt _ (hut.trans_le (hmin q hq))⟩
    · refine ⟨l.1+1,fun q hq => markedLE_of_lt _ (lt_of_le_of_lt (hmax q hq) (by linarith)),?_⟩
      intro q hq
      exact (hhi ⟨q,hq⟩).elim
  · by_cases hhi : hi.Nonempty
    · obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image hi Prod.fst hhi
      refine ⟨u.1-1,?_,fun q hq => markedLE_of_lt _ (lt_of_lt_of_le (by linarith) (hmin q hq))⟩
      intro q hq
      exact (hlo ⟨q,hq⟩).elim
    · exact ⟨0,fun q hq => (hlo ⟨q,hq⟩).elim,fun q hq => (hhi ⟨q,hq⟩).elim⟩

/-- Positive multiplication preserves a marked comparison. -/
theorem markedLE_mul_pos {s : Bool} {x y a : ℝ} (ha : 0 < a)
    (h : markedLE s x y) : markedLE s (x*a) (y*a) := by
  cases s
  · exact mul_le_mul_of_nonneg_right h ha.le
  · exact mul_lt_mul_of_pos_right h ha

/-- Negative multiplication reverses a marked comparison. -/
theorem markedLE_mul_neg {s : Bool} {x y a : ℝ} (ha : a < 0)
    (h : markedLE s x y) : markedLE s (y*a) (x*a) := by
  cases s
  · exact mul_le_mul_of_nonpos_right h ha.le
  · exact mul_lt_mul_of_neg_right h ha

theorem markedLE_trans_or {s t : Bool} {x y z : ℝ}
    (hxy : markedLE s x y) (hyz : markedLE t y z) : markedLE (s || t) x z := by
  cases s <;> cases t
  · exact le_trans hxy hyz
  · exact lt_of_le_of_lt hxy hyz
  · exact lt_of_lt_of_le hxy hyz
  · exact lt_trans hxy hyz

/-- Division-free exact Fourier--Motzkin criterion for mixed strict/weak
one-variable systems, with no sign, nonzero, or feasibility assumptions. -/
theorem exists_marked_affine_iff {ι : Type*} [Fintype ι]
    (s : ι → Bool) (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i, markedLE (s i) (a i*t) (b i)) ↔
      (∀ i, a i = 0 → markedLE (s i) 0 (b i)) ∧
      ∀ i j, a i < 0 → 0 < a j → markedLE (s i || s j) (b j*a i) (b i*a j) := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i hi => by simpa only [hi,zero_mul] using ht i,?_⟩
    intro i j hi hj
    have hi' := markedLE_mul_pos hj (ht i)
    have hj' := markedLE_mul_neg hi (ht j)
    have he : a j*t*a i = a i*t*a j := by ring
    rw [he] at hj'
    simpa only [Bool.or_comm] using markedLE_trans_or hj' hi'
  · rintro ⟨hzero,hpair⟩
    let lo : Finset (ℝ × Bool) := (Finset.univ.filter (fun i => a i < 0)).image
      (fun i => (b i/a i,s i))
    let hi : Finset (ℝ × Bool) := (Finset.univ.filter (fun i => 0 < a i)).image
      (fun i => (b i/a i,s i))
    have hsep : ∀ l ∈ lo, ∀ u ∈ hi, markedLE (l.2 || u.2) l.1 u.1 := by
      intro l hl u hu
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
      have hi0 := (Finset.mem_filter.mp hi).2
      have hj0 := (Finset.mem_filter.mp hj).2
      have h := hpair i j hi0 hj0
      cases hs : s i || s j
      · simp only [hs,markedLE,Bool.false_eq_true,if_false] at h ⊢
        apply (div_le_iff_of_neg hi0).mpr
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hj0).mpr h
      · simp only [hs,markedLE,if_true] at h ⊢
        apply (div_lt_iff_of_neg hi0).mpr
        rw [div_mul_eq_mul_div]
        exact (div_lt_iff₀ hj0).mpr h
    obtain ⟨t,htlo,hthi⟩ := exists_between_finite_marked lo hi hsep
    refine ⟨t,fun i => ?_⟩
    rcases lt_trichotomy (a i) 0 with hn | hz | hp
    · have hb := htlo _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩)
      change markedLE (s i) (b i/a i) t at hb
      cases hs : s i
      · simp only [hs,markedLE,Bool.false_eq_true,if_false] at hb ⊢
        simpa only [mul_comm] using (div_le_iff_of_neg hn).mp hb
      · simp only [hs,markedLE,if_true] at hb ⊢
        simpa only [mul_comm] using (div_lt_iff_of_neg hn).mp hb
    · simpa only [hz,zero_mul] using hzero i hz
    · have hb := hthi _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩)
      change markedLE (s i) t (b i/a i) at hb
      cases hs : s i
      · simp only [hs,markedLE,Bool.false_eq_true,if_false] at hb ⊢
        simpa only [mul_comm] using (le_div_iff₀ hp).mp hb
      · simp only [hs,markedLE,if_true] at hb ⊢
        simpa only [mul_comm] using (lt_div_iff₀ hp).mp hb

end RealAlgebraicGeometry
end BfgsVerification
