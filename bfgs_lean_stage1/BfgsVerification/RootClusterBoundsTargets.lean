import BfgsVerification.ParameterRootClusters

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

def ParameterRootDegreeBoundTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n),
    p.map (MvPolynomial.eval a) ≠ 0 →
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ x in 𝓝 a,
      (p.map (MvPolynomial.eval x)).natDegree ≤ (p.map (MvPolynomial.eval a)).natDegree →
      ∀ t : ℝ, (p.map (MvPolynomial.eval x)).IsRoot t → |t| < R

theorem parameterRootDegreeBound : ParameterRootDegreeBoundTarget := by
  intro n p a ha
  exact parameter_roots_bounded_on_degree_stratum p a ha

def IntervalMultiplicityRolleTarget : Prop :=
  ∀ (p : Polynomial ℝ) (I : Set ℝ), OrdConnected I → ∀ m : ℕ,
    (∀ t ∈ I, (Polynomial.derivative^[m] p).eval t ≠ 0) → rootWeightIn p I ≤ m

theorem intervalMultiplicityRolle : IntervalMultiplicityRolleTarget := by
  intro p I hI m h
  exact rootWeightIn_le_of_derivative_nonzero p I hI m h

def ParameterRootMultiplicityClusterTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n) (b : ℝ),
    p.map (MvPolynomial.eval a) ≠ 0 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 a,
      rootWeightIn (p.map (MvPolynomial.eval x)) (Icc (b-δ) (b+δ)) ≤
        (p.map (MvPolynomial.eval a)).rootMultiplicity b

theorem parameterRootMultiplicityCluster : ParameterRootMultiplicityClusterTarget := by
  intro n p a b hp
  exact parameter_root_multiplicity_cluster_bound p a b hp

def ParameterRootClusterCoverTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n),
    p.map (MvPolynomial.eval a) ≠ 0 → ∀ ε : ℝ, 0 < ε →
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
            (p.map (MvPolynomial.eval a)).rootMultiplicity b)

theorem parameterRootClusterCover : ParameterRootClusterCoverTarget := by
  intro n p a hp ε hε
  exact parameter_root_clusters p a hp hε

end RealAlgebraicGeometry
end BfgsVerification
