import BfgsVerification.RootMultiplicityRolle
import BfgsVerification.PolynomialRootMultiplicity

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem rootWeightIn_le_iterated_derivative_add (p : Polynomial ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (m : ℕ) :
    rootWeightIn p I ≤ rootWeightIn (Polynomial.derivative^[m] p) I + m := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    have h := (rootWeightIn_le_derivative_add_one p I hI).trans
      (Nat.add_le_add_right (ih p.derivative) 1)
    simpa only [Function.iterate_succ_apply, Nat.add_assoc] using h

theorem rootWeightIn_eq_zero_of_eval_ne_zero (p : Polynomial ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, p.eval t ≠ 0) : rootWeightIn p I = 0 := by
  classical
  have he : rootsIn p I = ∅ := by
    apply Finset.eq_empty_of_forall_not_mem
    intro t ht
    obtain ⟨hr,htI⟩ := Finset.mem_filter.mp ht
    exact h t htI (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
  simp [rootWeightIn,he]

theorem rootWeightIn_le_of_derivative_nonzero (p : Polynomial ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (m : ℕ)
    (h : ∀ t ∈ I, (Polynomial.derivative^[m] p).eval t ≠ 0) :
    rootWeightIn p I ≤ m := by
  have hb := rootWeightIn_le_iterated_derivative_add p I hI m
  simpa only [rootWeightIn_eq_zero_of_eval_ne_zero _ _ h,zero_add] using hb

/-- The actual total multiplicity of roots in a small fixed interval cannot
exceed the actual multiplicity at its center in the base fiber. This also
covers a nonroot center, whose multiplicity and nearby interval budget are zero. -/
theorem parameter_root_multiplicity_cluster_bound
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n) (b : ℝ)
    (hp : p.map (MvPolynomial.eval a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 a,
      rootWeightIn (p.map (MvPolynomial.eval x)) (Icc (b-δ) (b+δ)) ≤
        (p.map (MvPolynomial.eval a)).rootMultiplicity b := by
  let m := (p.map (MvPolynomial.eval a)).rootMultiplicity b
  let d := Polynomial.derivative^[m] p
  have hd : (d.map (MvPolynomial.eval a)).eval b ≠ 0 := by
    simpa only [d,← Polynomial.iterate_derivative_map] using
      eval_derivative_rootMultiplicity_ne_zero hp b
  have hn := (d.map (MvPolynomial.eval a)).continuous.continuousAt.eventually_ne hd
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hclosed : ∀ t ∈ Icc (b-δ) (b+δ), (d.map (MvPolynomial.eval a)).eval t ≠ 0 := by
    intro t ht
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> dsimp [δ] at ht ⊢ <;> linarith [ht.1,ht.2]
  have he := parameter_polynomial_eventually_nonzero_on_compact d a isCompact_Icc hclosed
  refine ⟨δ,hδ,?_⟩
  filter_upwards [he] with x hx
  apply rootWeightIn_le_of_derivative_nonzero _ _ ordConnected_Icc m
  intro t ht
  simpa only [Polynomial.iterate_derivative_map] using hx t ht

end RealAlgebraicGeometry
end BfgsVerification
