import BfgsVerification.ParameterRootBounds
import Mathlib.Topology.Compactness.Compact

noncomputable section
open Filter Set Polynomial
open scoped Topology NNReal
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem parameter_polynomial_eval_continuous (p : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Continuous (fun z : Vec n × ℝ => (p.map (MvPolynomial.eval z.1)).eval z.2) := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  apply continuous_finset_sum
  intro i _
  exact ((MvPolynomial.continuous_eval (p.coeff i)).comp continuous_fst).mul
    (continuous_snd.pow i)

theorem parameter_polynomial_eventually_nonzero_on_compact
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n) {K : Set ℝ}
    (hK : IsCompact K) (hne : ∀ t ∈ K, (p.map (MvPolynomial.eval a)).eval t ≠ 0) :
    ∀ᶠ x in 𝓝 a, ∀ t ∈ K, (p.map (MvPolynomial.eval x)).eval t ≠ 0 := by
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  exact (parameter_polynomial_eval_continuous p).continuousAt.eventually_ne (hne t ht)

theorem parameter_roots_upper_semicontinuous
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) {a : Vec n}
    (ha : MvPolynomial.eval a p.leadingCoeff ≠ 0) {U : Set ℝ}
    (hU : IsOpen U) (hroots : ∀ t : ℝ, (p.map (MvPolynomial.eval a)).IsRoot t → t ∈ U) :
    ∀ᶠ x in 𝓝 a, ∀ t : ℝ, (p.map (MvPolynomial.eval x)).IsRoot t → t ∈ U := by
  obtain ⟨R,hR,hbound⟩ := parameter_roots_eventually_bounded p ha
  let K : Set ℝ := Metric.closedBall 0 R ∩ Uᶜ
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) R).inter_right hU.isClosed_compl
  have hn : ∀ t ∈ K, (p.map (MvPolynomial.eval a)).eval t ≠ 0 := by
    intro t ht he
    exact ht.2 (hroots t he)
  have he := parameter_polynomial_eventually_nonzero_on_compact p a hK hn
  filter_upwards [hbound, he] with x hbx hex
  intro t ht
  by_contra htu
  have hmem : t ∈ K := by
    refine ⟨?_, htu⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact (hbx t ht).le
  exact hex t hmem ht

end RealAlgebraicGeometry
end BfgsVerification
