import BfgsVerification.OrderedRealRoots
import Mathlib.Order.Interval.Finset.Fin

noncomputable section
open Set Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

/-- Number of distinct actual roots strictly below a real number. -/
def rootBelowCount (p : Polynomial ℝ) (t : ℝ) : ℕ :=
  (p.roots.toFinset.filter (fun a => a < t)).card

theorem finset_card_below_orderEmb {α : Type*} [LinearOrder α]
    (S : Finset α) (i : Fin S.card) :
    (S.filter (fun a => a < S.orderEmbOfFin rfl i)).card = i.val := by
  classical
  have hm := S.map_orderEmbOfFin_univ rfl
  rw [show (S.filter (fun a => a < S.orderEmbOfFin rfl i)).card =
      ((Finset.univ.map (S.orderEmbOfFin rfl).toEmbedding).filter
        (fun a => a < S.orderEmbOfFin rfl i)).card from
      congrArg (fun T : Finset α => (T.filter (fun a => a < S.orderEmbOfFin rfl i)).card) hm.symm]
  rw [Finset.filter_map, Finset.card_map]
  have he : (Finset.univ.filter (fun j =>
      S.orderEmbOfFin rfl j < S.orderEmbOfFin rfl i)) = Finset.Iio i := by
    ext j
    simp
  change (Finset.univ.filter (fun j =>
      S.orderEmbOfFin rfl j < S.orderEmbOfFin rfl i)).card = i.val
  rw [he, Fin.card_Iio]

theorem rootBelowCount_orderedRealRoot (p : Polynomial ℝ) {k : ℕ}
    (hk : k < p.roots.toFinset.card) :
    rootBelowCount p (orderedRealRoot p k) = k := by
  rw [rootBelowCount, orderedRealRoot_eq_orderEmb p rfl ⟨k,hk⟩]
  exact finset_card_below_orderEmb _ _

theorem orderedRealRoot_valid_iff (p : Polynomial ℝ) (k : ℕ) (t : ℝ) :
    (k < p.roots.toFinset.card ∧ t = orderedRealRoot p k) ↔
      t ∈ p.roots.toFinset ∧ rootBelowCount p t = k := by
  classical
  constructor
  · rintro ⟨hk,rfl⟩
    exact ⟨orderedRealRoot_mem p hk,rootBelowCount_orderedRealRoot p hk⟩
  · rintro ⟨ht,hr⟩
    have ht' : t ∈ Set.range (p.roots.toFinset.orderEmbOfFin rfl) := by
      rwa [Finset.range_orderEmbOfFin]
    obtain ⟨i,hi⟩ := ht'
    have hri : rootBelowCount p t = i.val := by
      rw [← hi, rootBelowCount]
      exact finset_card_below_orderEmb _ _
    have hik : i.val = k := hri.symm.trans hr
    have hk : k < p.roots.toFinset.card := hik ▸ i.isLt
    refine ⟨hk,?_⟩
    rw [← hi, orderedRealRoot_eq_orderEmb p rfl ⟨k,hk⟩]
    congr 1
    exact Fin.ext hik

theorem orderedRealRoot_valid_iff_root (p : Polynomial ℝ) (k : ℕ) (t : ℝ) :
    (k < p.roots.toFinset.card ∧ t = orderedRealRoot p k) ↔
      p ≠ 0 ∧ p.eval t = 0 ∧ rootBelowCount p t = k := by
  rw [orderedRealRoot_valid_iff]
  constructor
  · rintro ⟨ht,hr⟩
    have ht' := Multiset.mem_toFinset.mp ht
    exact ⟨Polynomial.ne_zero_of_mem_roots ht',Polynomial.isRoot_of_mem_roots ht',hr⟩
  · rintro ⟨hp,ht,hr⟩
    exact ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ht),hr⟩

theorem orderedRealRoot_total_iff (p : Polynomial ℝ) (k : ℕ) (t : ℝ) :
    t = orderedRealRoot p k ↔
      (p ≠ 0 ∧ p.eval t = 0 ∧ rootBelowCount p t = k) ∨
        (p.roots.toFinset.card ≤ k ∧ t = 0) := by
  by_cases hk : k < p.roots.toFinset.card
  · have hv := orderedRealRoot_valid_iff_root p k t
    simpa only [hk, true_and, not_le_of_gt hk, false_and, or_false] using hv
  · have he : orderedRealRoot p k = 0 := by simp [orderedRealRoot,hk]
    have hn : ¬ (p ≠ 0 ∧ p.eval t = 0 ∧ rootBelowCount p t = k) := by
      rw [← orderedRealRoot_valid_iff_root]
      exact fun h => hk h.1
    simp only [he,hn,false_or,le_of_not_gt hk,true_and]

end BfgsVerification.RealAlgebraicGeometry
