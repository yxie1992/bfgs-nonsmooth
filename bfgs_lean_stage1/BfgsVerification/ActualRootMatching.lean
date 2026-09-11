import BfgsVerification.FiniteClusterOrder
import BfgsVerification.RootClusterConservation

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

open RootClusterConservation

theorem sum_actual_root_multiplicities (p : Polynomial ℝ) :
    ∑ t ∈ p.roots.toFinset, p.rootMultiplicity t = p.roots.card := by
  classical
  simpa only [Polynomial.count_roots] using Multiset.toFinset_sum_count_eq p.roots

/-- Exact matching of actual ordered roots follows from the derived cluster
budgets and conservation of both distinct count and total multiplicity. -/
theorem actual_ordered_root_matching (p q : Polynomial ℝ) (hp : p ≠ 0) (δ : ℝ)
    (hdisj : ∀ b ∈ p.roots.toFinset, ∀ c ∈ p.roots.toFinset, b ≠ c →
      Disjoint (Icc (b-δ) (b+δ)) (Icc (c-δ) (c+δ)))
    (hcover : ∀ t ∈ q.roots.toFinset, ∃ b ∈ p.roots.toFinset, t ∈ Icc (b-δ) (b+δ))
    (hbudget : ∀ b ∈ p.roots.toFinset,
      rootWeightIn q (Icc (b-δ) (b+δ)) ≤ p.rootMultiplicity b)
    (hcard : q.roots.toFinset.card = p.roots.toFinset.card)
    (hweight : q.roots.card = p.roots.card) :
    ∀ i : Fin p.roots.toFinset.card,
      q.roots.toFinset.orderEmbOfFin hcard i ∈
        Icc (p.roots.toFinset.orderEmbOfFin rfl i-δ) (p.roots.toFinset.orderEmbOfFin rfl i+δ) ∧
      q.rootMultiplicity (q.roots.toFinset.orderEmbOfFin hcard i) =
        p.rootMultiplicity (p.roots.toFinset.orderEmbOfFin rfl i) := by
  classical
  obtain ⟨c,hc,hciff⟩ := finite_cluster_assignment p.roots.toFinset q.roots.toFinset
    (fun b => Icc (b-δ) (b+δ)) hcover hdisj
  have hmaps : ∀ t ∈ q.roots.toFinset, c t ∈ p.roots.toFinset := fun t ht => (hc t ht).1
  have hm : ∀ b ∈ p.roots.toFinset, 0 < p.rootMultiplicity b := by
    intro b hb
    exact (Polynomial.rootMultiplicity_pos hp).mpr
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hb))
  have hfiber : ∀ b ∈ p.roots.toFinset,
      fiberWeight q.roots.toFinset c q.rootMultiplicity b = rootWeightIn q (Icc (b-δ) (b+δ)) := by
    intro b hb
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_filter,rootsIn]
      exact and_congr_right (fun ht => hciff t ht b hb)
    · intro t _
      rfl
  have hle : ∀ b ∈ p.roots.toFinset,
      fiberWeight q.roots.toFinset c q.rootMultiplicity b ≤ p.rootMultiplicity b := by
    intro b hb
    rw [hfiber b hb]
    exact hbudget b hb
  have htotal : ∑ t ∈ q.roots.toFinset, q.rootMultiplicity t =
      ∑ b ∈ p.roots.toFinset, p.rootMultiplicity b := by
    rw [sum_actual_root_multiplicities,sum_actual_root_multiplicities,hweight]
  have hbij := label_bijOn_of_card_eq hmaps hm hle htotal hcard
  have hordered := ordered_cluster_assignment p.roots.toFinset q.roots.toFinset δ c
    hcard hc hbij.injOn hdisj
  intro i
  have hi := q.roots.toFinset.orderEmbOfFin_mem hcard i
  constructor
  · simpa only [hordered i] using (hc _ hi).2
  · simpa only [hordered i] using sole_weight_eq_capacity hmaps hm hle htotal hcard hi

end RealAlgebraicGeometry
end BfgsVerification
