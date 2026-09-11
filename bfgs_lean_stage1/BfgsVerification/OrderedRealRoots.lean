import BfgsVerification.ActualRootMatching

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Canonical increasing enumeration of the distinct actual real roots, with
zero only as the total-function value beyond the end of the root list. -/
def orderedRealRoot (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  if hk : k < p.roots.toFinset.card then
    p.roots.toFinset.orderEmbOfFin rfl ⟨k,hk⟩ else 0

theorem orderedRealRoot_eq_orderEmb (p : Polynomial ℝ) {m : ℕ}
    (h : p.roots.toFinset.card = m) (i : Fin m) :
    orderedRealRoot p i.val = p.roots.toFinset.orderEmbOfFin h i := by
  classical
  have hi : i.val < p.roots.toFinset.card := by simpa only [h] using i.isLt
  rw [orderedRealRoot,dif_pos hi]
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

theorem orderedRealRoot_mem (p : Polynomial ℝ) {k : ℕ} (hk : k < p.roots.toFinset.card) :
    orderedRealRoot p k ∈ p.roots.toFinset := by
  rw [orderedRealRoot_eq_orderEmb p rfl ⟨k,hk⟩]
  exact p.roots.toFinset.orderEmbOfFin_mem rfl ⟨k,hk⟩

theorem orderedRealRoot_isRoot (p : Polynomial ℝ) {k : ℕ} (hk : k < p.roots.toFinset.card) :
    p.IsRoot (orderedRealRoot p k) :=
  Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (orderedRealRoot_mem p hk))

theorem orderedRealRoot_matching (p q : Polynomial ℝ) (hp : p ≠ 0) (δ : ℝ)
    (hdisj : ∀ b ∈ p.roots.toFinset, ∀ c ∈ p.roots.toFinset, b ≠ c →
      Disjoint (Icc (b-δ) (b+δ)) (Icc (c-δ) (c+δ)))
    (hcover : ∀ t ∈ q.roots.toFinset, ∃ b ∈ p.roots.toFinset, t ∈ Icc (b-δ) (b+δ))
    (hbudget : ∀ b ∈ p.roots.toFinset,
      rootWeightIn q (Icc (b-δ) (b+δ)) ≤ p.rootMultiplicity b)
    (hcard : q.roots.toFinset.card = p.roots.toFinset.card)
    (hweight : q.roots.card = p.roots.card) {k : ℕ} (hk : k < p.roots.toFinset.card) :
    orderedRealRoot q k ∈ Icc (orderedRealRoot p k-δ) (orderedRealRoot p k+δ) ∧
      q.rootMultiplicity (orderedRealRoot q k) = p.rootMultiplicity (orderedRealRoot p k) := by
  have hq := orderedRealRoot_eq_orderEmb q hcard ⟨k,hk⟩
  have hp' := orderedRealRoot_eq_orderEmb p rfl ⟨k,hk⟩
  simpa only [← hq,← hp'] using actual_ordered_root_matching p q hp δ hdisj hcover
    hbudget hcard hweight ⟨k,hk⟩

end RealAlgebraicGeometry
end BfgsVerification
