import BfgsVerification.RootMultiplicityCluster
import BfgsVerification.FiniteDegreePrefixes

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

/-- The degree condition is imposed only on the points being compared. Higher
coefficients may be nonzero arbitrarily near the base point outside that set. -/
theorem parameter_roots_bounded_on_degree_stratum
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n)
    (ha : p.map (MvPolynomial.eval a) ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ x in 𝓝 a,
      (p.map (MvPolynomial.eval x)).natDegree ≤ (p.map (MvPolynomial.eval a)).natDegree →
      ∀ t : ℝ, (p.map (MvPolynomial.eval x)).IsRoot t → |t| < R := by
  let N := (p.map (MvPolynomial.eval a)).natDegree
  let q := degreePrefix p N
  have hq : MvPolynomial.eval a q.leadingCoeff ≠ 0 :=
    degreePrefix_leadingCoeff_specialize p (MvPolynomial.eval a) ha
  obtain ⟨R,hR,hb⟩ := parameter_roots_eventually_bounded q hq
  refine ⟨R,hR,?_⟩
  filter_upwards [hb] with x hx
  intro hdeg t ht
  apply hx t
  rwa [show q.map (MvPolynomial.eval x) = p.map (MvPolynomial.eval x) from
    degreePrefix_map p _ N hdeg]

/-- Upper semicontinuity is retained on every actual degree-drop stratum. -/
theorem parameter_roots_upper_semicontinuous_degree_stratum
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n)
    (ha : p.map (MvPolynomial.eval a) ≠ 0) {U : Set ℝ}
    (hU : IsOpen U) (hroots : ∀ t : ℝ, (p.map (MvPolynomial.eval a)).IsRoot t → t ∈ U) :
    ∀ᶠ x in 𝓝 a,
      (p.map (MvPolynomial.eval x)).natDegree ≤ (p.map (MvPolynomial.eval a)).natDegree →
      ∀ t : ℝ, (p.map (MvPolynomial.eval x)).IsRoot t → t ∈ U := by
  let N := (p.map (MvPolynomial.eval a)).natDegree
  let q := degreePrefix p N
  have hq : MvPolynomial.eval a q.leadingCoeff ≠ 0 :=
    degreePrefix_leadingCoeff_specialize p (MvPolynomial.eval a) ha
  have hqa : q.map (MvPolynomial.eval a) = p.map (MvPolynomial.eval a) :=
    degreePrefix_map p _ N le_rfl
  have hu := parameter_roots_upper_semicontinuous q hq hU (by simpa [hqa] using hroots)
  filter_upwards [hu] with x hx
  intro hdeg t ht
  apply hx t
  rwa [show q.map (MvPolynomial.eval x) = p.map (MvPolynomial.eval x) from
    degreePrefix_map p _ N hdeg]

end RealAlgebraicGeometry
end BfgsVerification
