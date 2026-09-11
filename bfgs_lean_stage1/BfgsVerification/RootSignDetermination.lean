import BfgsVerification.FiniteSignDetermination
import BfgsVerification.TarskiLocalIndex

noncomputable section
open scoped BigOperators
open Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

/-- Count the distinct roots supplied by the actual polynomial root multiset
that realize all signs simultaneously. For p=0 the library root multiset is
empty; the actual-real-root interpretation below explicitly requires p≠0. -/
def rootSignCount {m : ℕ} (p : Polynomial ℝ) (q : Fin m → Polynomial ℝ)
    (σ : Fin m → SignType) : ℕ :=
  finiteSignCount p.roots.toFinset (fun a i => SignType.sign ((q i).eval a)) σ

/-- The actual polynomial whose Tarski query is a power moment. -/
def signQueryPolynomial {m : ℕ} (q : Fin m → Polynomial ℝ) (e : Fin m → Fin 3) : Polynomial ℝ :=
  ∏i,(q i)^(e i).val

theorem root_sign_moment_eq_tarskiQuery {m : ℕ} (p : Polynomial ℝ)
    (q : Fin m → Polynomial ℝ) (e : Fin m → Fin 3) :
    finiteSignMoment p.roots.toFinset (fun a i => SignType.sign ((q i).eval a)) e=
      (tarskiQuery p (signQueryPolynomial q e) : ℚ) := by
  classical
  unfold finiteSignMoment tarskiQuery
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [signQueryPolynomial,Polynomial.eval_prod]
  simp only [Polynomial.eval_pow]
  exact (sign_product_powers_rat (fun i => (q i).eval a) e).symm

/-- Exact simultaneous sign determination on the distinct actual roots: all
counts are rational combinations of the 3^m actual polynomial Tarski queries. -/
theorem root_sign_count_from_tarskiQueries {m : ℕ} (p : Polynomial ℝ)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    (rootSignCount p q σ : ℚ)=∑e : Fin m → Fin 3,
      signPatternCoeff σ e * (tarskiQuery p (signQueryPolynomial q e) : ℚ) := by
  rw [rootSignCount,finite_sign_count_from_moments]
  simp_rw [root_sign_moment_eq_tarskiQuery]

/-- Only this interpretation as the complete actual real-root set needs a
nonzero root polynomial. Repeated roots still contribute only once. -/
theorem rootSignCount_pos_iff {m : ℕ} {p : Polynomial ℝ} (hp : p≠0)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    0<rootSignCount p q σ ↔ ∃a : ℝ,p.eval a=0 ∧ ∀i,SignType.sign ((q i).eval a)=σ i := by
  classical
  rw [rootSignCount,finiteSignCount_pos_iff]
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨a,(Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp ha),fun i => congrFun he i⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨a,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ha),funext he⟩

/-- Positivity of one explicit rational expression detects a common real root
realizing every requested sign, with no genericity or multiplicity premise. -/
theorem exists_root_sign_pattern_iff_query_positive {m : ℕ} {p : Polynomial ℝ} (hp : p≠0)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    (∃a : ℝ,p.eval a=0 ∧ ∀i,SignType.sign ((q i).eval a)=σ i) ↔
      0<∑e : Fin m → Fin 3,signPatternCoeff σ e * (tarskiQuery p (signQueryPolynomial q e) : ℚ) := by
  rw [← rootSignCount_pos_iff hp,← root_sign_count_from_tarskiQueries]
  exact Nat.cast_pos.symm

/-- The finite actual query vector determines the whole simultaneous sign
count vector, even when the two root polynomials have different degrees. -/
theorem root_sign_counts_eq_of_queries_eq {m : ℕ} (p p' : Polynomial ℝ)
    (q q' : Fin m → Polynomial ℝ)
    (he : ∀e,tarskiQuery p (signQueryPolynomial q e)=tarskiQuery p' (signQueryPolynomial q' e)) :
    ∀σ,rootSignCount p q σ=rootSignCount p' q' σ := by
  intro σ
  apply Nat.cast_injective (R := ℚ)
  simp_rw [root_sign_count_from_tarskiQueries,he]

theorem rootSignCount_zero_polynomial {m : ℕ} (q : Fin m → Polynomial ℝ)
    (σ : Fin m → SignType) : rootSignCount 0 q σ=0 := by
  simp [rootSignCount,finiteSignCount]

theorem rootSignCount_empty_pattern (p : Polynomial ℝ)
    (q : Fin 0 → Polynomial ℝ) (σ : Fin 0 → SignType) :
    rootSignCount p q σ=p.roots.toFinset.card := finiteSignCount_empty_pattern _ _ _

theorem signQueryPolynomial_empty (q : Fin 0 → Polynomial ℝ) (e : Fin 0 → Fin 3) :
    signQueryPolynomial q e=1 := by simp [signQueryPolynomial]

/-- The recovered count is a natural number bounded by the actual root degree. -/
theorem rootSignCount_le_natDegree {m : ℕ} (p : Polynomial ℝ)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    rootSignCount p q σ≤p.natDegree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p))

theorem root_sign_expression_bounds {m : ℕ} (p : Polynomial ℝ)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    0≤∑e : Fin m → Fin 3,signPatternCoeff σ e * (tarskiQuery p (signQueryPolynomial q e) : ℚ) ∧
      (∑e : Fin m → Fin 3,signPatternCoeff σ e * (tarskiQuery p (signQueryPolynomial q e) : ℚ))≤p.natDegree := by
  rw [← root_sign_count_from_tarskiQueries]
  exact ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (rootSignCount_le_natDegree p q σ)⟩

theorem card_sign_query_indices (m : ℕ) : Fintype.card (Fin m → Fin 3)=3^m := by simp

end BfgsVerification.RealAlgebraicGeometry
