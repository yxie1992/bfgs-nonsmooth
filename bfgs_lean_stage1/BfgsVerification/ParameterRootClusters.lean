import BfgsVerification.FiniteRootNeighborhoods

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

/-- Uniform small disjoint clusters contain every nearby actual root on the
actual degree stratum, and each cluster's total multiplicity is bounded by its
base root multiplicity. No constancy of root counts is used here. -/
theorem parameter_root_clusters
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n)
    (hp : p.map (MvPolynomial.eval a) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (∀ b ∈ (p.map (MvPolynomial.eval a)).roots.toFinset,
        ∀ c ∈ (p.map (MvPolynomial.eval a)).roots.toFinset, b ≠ c →
        Disjoint (Icc (b-δ) (b+δ)) (Icc (c-δ) (c+δ))) ∧
      ∀ᶠ x in 𝓝 a,
        (p.map (MvPolynomial.eval x)).natDegree ≤ (p.map (MvPolynomial.eval a)).natDegree →
        (∀ t : ℝ, (p.map (MvPolynomial.eval x)).IsRoot t →
          ∃ b ∈ (p.map (MvPolynomial.eval a)).roots.toFinset, t ∈ Ioo (b-δ) (b+δ)) ∧
        (∀ b ∈ (p.map (MvPolynomial.eval a)).roots.toFinset,
          rootWeightIn (p.map (MvPolynomial.eval x)) (Icc (b-δ) (b+δ)) ≤
            (p.map (MvPolynomial.eval a)).rootMultiplicity b) := by
  classical
  let S := (p.map (MvPolynomial.eval a)).roots.toFinset
  choose γ hγ hbudget using (fun b : S => parameter_root_multiplicity_cluster_bound p a b hp)
  let γall : ℝ → ℝ := fun b => if hb : b ∈ S then γ ⟨b,hb⟩ else 1
  have hgall : ∀ b ∈ S, 0 < γall b := by
    intro b hb
    simpa only [γall,dif_pos hb] using hγ ⟨b,hb⟩
  obtain ⟨δ,hδ,hδε,hδγ,hsep⟩ := finite_root_separating_radius S γall hgall hε
  have hsmall : ∀ b : S, δ < γ b := by
    intro b
    simpa only [γall,dif_pos b.2] using hδγ b b.2
  have hb : ∀ᶠ x in 𝓝 a, ∀ b : S,
      rootWeightIn (p.map (MvPolynomial.eval x)) (Icc (b-γ b) (b+γ b)) ≤
        (p.map (MvPolynomial.eval a)).rootMultiplicity (b : ℝ) := Filter.eventually_all.mpr hbudget
  let U : Set ℝ := ⋃ b : S, Ioo ((b : ℝ)-δ) ((b : ℝ)+δ)
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_Ioo)
  have hrU : ∀ t : ℝ, (p.map (MvPolynomial.eval a)).IsRoot t → t ∈ U := by
    intro t ht
    have htr : t ∈ S := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ht)
    exact mem_iUnion.mpr ⟨⟨t,htr⟩,by constructor <;> linarith⟩
  have hu := parameter_roots_upper_semicontinuous_degree_stratum p a hp hU hrU
  refine ⟨δ,hδ,hδε,?_,?_⟩
  · intro b hb c hc hbc
    exact disjoint_closed_root_intervals (hsep b hb c hc hbc)
  · filter_upwards [hu,hb] with x hux hbx
    intro hdeg
    constructor
    · intro t ht
      obtain ⟨b,hb⟩ := mem_iUnion.mp (hux hdeg t ht)
      exact ⟨b,b.2,hb⟩
    · intro b hb
      apply (rootWeightIn_mono _ (Icc_subset_Icc ?_ ?_)).trans (hbx ⟨b,hb⟩)
      all_goals have hh := hsmall ⟨b,hb⟩; dsimp at hh ⊢; linarith

/-- The interval weight on the whole real line is the actual roots multiset
cardinality, so repeated roots contribute their true multiplicities. -/
theorem rootWeightIn_univ (p : Polynomial ℝ) : rootWeightIn p univ = p.roots.card := by
  classical
  simpa [rootWeightIn,rootsIn,← Polynomial.count_roots] using
    (Multiset.toFinset_sum_count_eq p.roots)

end RealAlgebraicGeometry
end BfgsVerification
