import BfgsVerification.OrderedRootSmoothCharts

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem mem_rootSignatureStratum_self (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n) :
    a ∈ rootSignatureStratum p a := ⟨rfl,rfl,rfl⟩

theorem rootSignatureStratum_eq_of_mem (p : Polynomial (MvPolynomial (Fin n) ℝ))
    {a b : Vec n} (hb : b ∈ rootSignatureStratum p a) :
    rootSignatureStratum p b = rootSignatureStratum p a := by
  ext x
  change (_ = _ ∧ _ = _ ∧ _ = _) ↔ (_ = _ ∧ _ = _ ∧ _ = _)
  rw [hb.1,hb.2.1,hb.2.2]

theorem orderedFiberRoot_contDiffOn_signature
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) {k : ℕ}
    (hk : k < (fiberPolynomial p a).roots.toFinset.card) :
    ContDiffOn ℝ ∞ (orderedFiberRoot p k)
      (rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a) := by
  intro b hb
  have hcard : (fiberPolynomial p b).roots.toFinset.card = (fiberPolynomial p a).roots.toFinset.card := by
    simpa only [← fiberPolynomial_eq_map] using hb.2.1
  have hkb : k < (fiberPolynomial p b).roots.toFinset.card := hcard ▸ hk
  have hpb : fiberPolynomial p b ≠ 0 := Polynomial.ne_zero_of_mem_roots
    (Multiset.mem_toFinset.mp (orderedRealRoot_mem _ hkb))
  apply orderedFiberRoot_contDiffWithinAt p b hpb hkb
  rw [rootSignatureStratum_eq_of_mem _ hb]

theorem orderedRealRoot_strictMono (p : Polynomial ℝ) :
    StrictMono (fun i : Fin p.roots.toFinset.card => orderedRealRoot p i.val) := by
  intro i j hij
  change orderedRealRoot p i.val < orderedRealRoot p j.val
  rw [orderedRealRoot_eq_orderEmb p rfl i,orderedRealRoot_eq_orderEmb p rfl j]
  exact (p.roots.toFinset.orderEmbOfFin rfl).strictMono hij

theorem orderedRealRoot_lt (p : Polynomial ℝ) {i j : ℕ}
    (hij : i < j) (hj : j < p.roots.toFinset.card) :
    orderedRealRoot p i < orderedRealRoot p j :=
  orderedRealRoot_strictMono p (show (⟨i,hij.trans hj⟩ : Fin p.roots.toFinset.card) < ⟨j,hj⟩ from hij)

theorem isRoot_iff_exists_orderedRealRoot (p : Polynomial ℝ) (hp : p ≠ 0) (t : ℝ) :
    p.IsRoot t ↔ ∃ k < p.roots.toFinset.card, orderedRealRoot p k = t := by
  classical
  constructor
  · intro ht
    have hmem : t ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ht)
    obtain ⟨i,hi⟩ := (p.roots.toFinset.orderIsoOfFin rfl).surjective ⟨t,hmem⟩
    refine ⟨i.val,i.isLt,?_⟩
    rw [orderedRealRoot_eq_orderEmb p rfl i]
    exact congrArg Subtype.val hi
  · rintro ⟨k,hk,rfl⟩
    exact orderedRealRoot_isRoot p hk

end RealAlgebraicGeometry
end BfgsVerification
