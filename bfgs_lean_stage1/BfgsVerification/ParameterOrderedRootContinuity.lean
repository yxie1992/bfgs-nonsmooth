import BfgsVerification.OrderedRealRoots

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

/-- Actual parameter-fiber signature: degree, number of distinct real roots,
and real-root count with multiplicities. The zero fiber remains separate. -/
def rootSignatureStratum (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n) : Set (Vec n) :=
  {x | (p.map (MvPolynomial.eval x)).natDegree = (p.map (MvPolynomial.eval a)).natDegree ∧
    (p.map (MvPolynomial.eval x)).roots.toFinset.card =
      (p.map (MvPolynomial.eval a)).roots.toFinset.card ∧
    (p.map (MvPolynomial.eval x)).roots.card = (p.map (MvPolynomial.eval a)).roots.card}

theorem parameter_ordered_root_eventually_near
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n)
    (hp : p.map (MvPolynomial.eval a) ≠ 0) {k : ℕ}
    (hk : k < (p.map (MvPolynomial.eval a)).roots.toFinset.card) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 a,
      (p.map (MvPolynomial.eval x)).natDegree ≤ (p.map (MvPolynomial.eval a)).natDegree →
      (p.map (MvPolynomial.eval x)).roots.toFinset.card =
        (p.map (MvPolynomial.eval a)).roots.toFinset.card →
      (p.map (MvPolynomial.eval x)).roots.card = (p.map (MvPolynomial.eval a)).roots.card →
      dist (orderedRealRoot (p.map (MvPolynomial.eval x)) k)
        (orderedRealRoot (p.map (MvPolynomial.eval a)) k) < ε ∧
      (p.map (MvPolynomial.eval x)).rootMultiplicity (orderedRealRoot (p.map (MvPolynomial.eval x)) k) =
        (p.map (MvPolynomial.eval a)).rootMultiplicity (orderedRealRoot (p.map (MvPolynomial.eval a)) k) := by
  obtain ⟨δ,hδ,hδε,hdisj,hnear⟩ := parameter_root_clusters p a hp hε
  filter_upwards [hnear] with x hx
  intro hdeg hcard hweight
  obtain ⟨hcover,hbudget⟩ := hx hdeg
  have hcover' : ∀ t ∈ (p.map (MvPolynomial.eval x)).roots.toFinset,
      ∃ b ∈ (p.map (MvPolynomial.eval a)).roots.toFinset, t ∈ Icc (b-δ) (b+δ) := by
    intro t ht
    obtain ⟨b,hb,hbt⟩ := hcover t
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ht))
    exact ⟨b,hb,⟨hbt.1.le,hbt.2.le⟩⟩
  obtain ⟨hmatch,horder⟩ := orderedRealRoot_matching _ _ hp δ hdisj hcover' hbudget hcard hweight hk
  refine ⟨?_,horder⟩
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [hmatch.1,hmatch.2]

theorem parameter_ordered_root_continuousWithinAt
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n)
    (hp : p.map (MvPolynomial.eval a) ≠ 0) {k : ℕ}
    (hk : k < (p.map (MvPolynomial.eval a)).roots.toFinset.card) {S : Set (Vec n)}
    (hS : S ⊆ rootSignatureStratum p a) :
    ContinuousWithinAt (fun x => orderedRealRoot (p.map (MvPolynomial.eval x)) k) S a := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear := parameter_ordered_root_eventually_near p a hp hk hε
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hx hxS
  obtain ⟨hd,hc,hw⟩ := hS hxS
  exact (hx hd.le hc hw).1

theorem parameter_ordered_root_multiplicity_locally_constant
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n)
    (hp : p.map (MvPolynomial.eval a) ≠ 0) {k : ℕ}
    (hk : k < (p.map (MvPolynomial.eval a)).roots.toFinset.card) {S : Set (Vec n)}
    (hS : S ⊆ rootSignatureStratum p a) :
    ∀ᶠ x in 𝓝[S] a,
      (p.map (MvPolynomial.eval x)).rootMultiplicity (orderedRealRoot (p.map (MvPolynomial.eval x)) k) =
        (p.map (MvPolynomial.eval a)).rootMultiplicity (orderedRealRoot (p.map (MvPolynomial.eval a)) k) := by
  have hnear := parameter_ordered_root_eventually_near p a hp hk (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hx hxS
  obtain ⟨hd,hc,hw⟩ := hS hxS
  exact (hx hd.le hc hw).2

end RealAlgebraicGeometry
end BfgsVerification
