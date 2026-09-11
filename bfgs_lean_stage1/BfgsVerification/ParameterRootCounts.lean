import BfgsVerification.ParameterSignQueries
import BfgsVerification.PolynomialRootMultiplicity

/-! Exact semialgebraic fibers for the actual finite polynomial root counts.
The identically zero polynomial retains mathlib's empty root multiset. -/
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace BfgsVerification.RealAlgebraicGeometry

variable {σ : Type*} [Finite σ] {m : ℕ}

theorem finiteSemialgebraic_actualRootSignCount
    (p : Polynomial (MvPolynomial σ ℝ))
    (q : Fin m → Polynomial (MvPolynomial σ ℝ)) (ω : Fin m → SignType) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ => rootSignCount
      (p.map (MvPolynomial.eval x)) (fun i => (q i).map (MvPolynomial.eval x)) ω) := by
  classical
  refine ⟨(Set.finite_Iic p.natDegree).subset ?_, fun k => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (rootSignCount_le_natDegree _ _ _).trans Polynomial.natDegree_map_le
  · have h := (finiteSemialgebraic_signQueryExpression p q ω).fiber (k : ℚ)
    simpa only [signQueryExpression, ← root_sign_count_from_tarskiQueries,
      Nat.cast_inj] using h

theorem finiteSemialgebraic_distinctRealRootCount
    (p : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      (p.map (MvPolynomial.eval x)).roots.toFinset.card) := by
  have h := finiteSemialgebraic_actualRootSignCount p
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
  simpa only [rootSignCount_empty_pattern] using h

theorem derivative_prefix_zero_iff {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) (k : ℕ) :
    (∀ j : Fin (k+1), (Polynomial.derivative^[j.val] p).eval t = 0) ↔
      k < p.rootMultiplicity t := by
  constructor
  · intro h
    by_contra hle
    have hm : p.rootMultiplicity t < k+1 := by omega
    exact eval_derivative_rootMultiplicity_ne_zero hp t (h ⟨_, hm⟩)
  · intro h j
    exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega)

theorem derivative_zero_sign_count (p : Polynomial ℝ) (k : ℕ) :
    rootSignCount p (fun j : Fin (k+1) => Polynomial.derivative^[j.val] p)
      (fun _ => 0) =
      (p.roots.toFinset.filter (fun t => k < p.rootMultiplicity t)).card := by
  classical
  by_cases hp : p = 0
  · simp [hp, rootSignCount_zero_polynomial]
  · unfold rootSignCount finiteSignCount
    congr 1
    apply Finset.filter_congr
    intro t _
    simp only [funext_iff, sign_eq_zero_iff]
    exact derivative_prefix_zero_iff hp t k

theorem rootCount_sum_actual_multiplicities (p : Polynomial ℝ) :
    ∑ t ∈ p.roots.toFinset, p.rootMultiplicity t = p.roots.card := by
  classical
  simpa only [← Polynomial.count_roots] using Multiset.toFinset_sum_count_eq p.roots

theorem real_root_multiplicity_sum_counts (p : Polynomial ℝ) (D : ℕ)
    (hD : p.natDegree ≤ D) :
    p.roots.card = ∑ k ∈ Finset.range D,
      rootSignCount p (fun j : Fin (k+1) => Polynomial.derivative^[j.val] p)
        (fun _ => 0) := by
  classical
  by_cases hp : p = 0
  · simp [hp, rootSignCount_zero_polynomial]
  · simp_rw [derivative_zero_sign_count, Finset.card_filter]
    rw [Finset.sum_comm, ← rootCount_sum_actual_multiplicities]
    apply Finset.sum_congr rfl
    intro t _
    have hm := (rootMultiplicity_le_natDegree hp t).trans hD
    rw [← Finset.card_filter]
    have he : (Finset.range D).filter (fun k => k < p.rootMultiplicity t) =
        Finset.range (p.rootMultiplicity t) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [he, Finset.card_range]

theorem finiteSemialgebraic_totalRealRootMultiplicity
    (p : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      (p.map (MvPolynomial.eval x)).roots.card) := by
  have h := FiniteSemialgebraicFunction.sum (Finset.range p.natDegree)
    (fun k x => rootSignCount (p.map (MvPolynomial.eval x))
      (fun j : Fin (k+1) => (Polynomial.derivative^[j.val] p).map (MvPolynomial.eval x))
      (fun _ => 0))
    (fun k _ => finiteSemialgebraic_actualRootSignCount p
      (fun j : Fin (k+1) => Polynomial.derivative^[j.val] p) (fun _ => 0))
  simp_rw [← Polynomial.iterate_derivative_map] at h
  convert h using 1
  funext x
  exact real_root_multiplicity_sum_counts _ _ Polynomial.natDegree_map_le

end BfgsVerification.RealAlgebraicGeometry
