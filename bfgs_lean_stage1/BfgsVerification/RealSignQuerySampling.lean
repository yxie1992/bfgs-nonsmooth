import BfgsVerification.PolynomialTailSamples
import BfgsVerification.RootSignDetermination

noncomputable section
open scoped BigOperators
open Set Filter Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

/-- The explicit rational linear combination of actual polynomial queries. -/
def signQueryExpression {m : ℕ} (p : Polynomial ℝ) (q : Fin m → Polynomial ℝ)
    (σ : Fin m → SignType) : ℚ :=
  ∑e : Fin m → Fin 3,signPatternCoeff σ e*(tarskiQuery p (signQueryPolynomial q e) : ℚ)

theorem signQueryExpression_positive_iff_rootList {m : ℕ} (p : Polynomial ℝ)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    0<signQueryExpression p q σ ↔
      ∃a∈p.roots.toFinset,∀i,SignType.sign ((q i).eval a)=σ i := by
  rw [signQueryExpression,← root_sign_count_from_tarskiQueries,Nat.cast_pos,
    rootSignCount,finiteSignCount_pos_iff]
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,fun i => congrFun he i⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,funext he⟩

/-- Fixed-fiber reduction of every simultaneous sign question on R to two
finite actual Tarski-query expressions and the two literal coefficient-tail
patterns. Zero factors, constants, repeated roots and empty families are all
handled. The derivative root polynomial may be zero; its query is then zero. -/
theorem exists_real_sign_pattern_iff_queries_and_tails {m : ℕ}
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType) :
    (∃x : ℝ,∀i,SignType.sign ((q i).eval x)=σ i) ↔
      0<signQueryExpression (nonzeroFamilyProduct q) q σ ∨
      0<signQueryExpression (nonzeroFamilyProduct q).derivative q σ ∨
      (∀i,(-1 : SignType)^(q i).natDegree*SignType.sign (q i).leadingCoeff=σ i) ∨
      (∀i,SignType.sign (q i).leadingCoeff=σ i) := by
  classical
  rw [exists_family_signs_iff_sample]
  constructor
  · rintro ⟨a,ha,hσ⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact Or.inl ((signQueryExpression_positive_iff_rootList _ q σ).mpr ⟨a,ha,hσ⟩)
      · exact Or.inr (Or.inl ((signQueryExpression_positive_iff_rootList _ q σ).mpr ⟨a,ha,hσ⟩))
    · simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (fun i => (left_tail_sample_sign q i).symm.trans (hσ i))))
      · exact Or.inr (Or.inr (Or.inr (fun i => (right_tail_sample_sign q i).symm.trans (hσ i))))
  · rintro (h | h | h | h)
    · obtain ⟨a,ha,hσ⟩ := (signQueryExpression_positive_iff_rootList _ q σ).mp h
      exact ⟨a,Finset.mem_union_left _ (Finset.mem_union_left _ ha),hσ⟩
    · obtain ⟨a,ha,hσ⟩ := (signQueryExpression_positive_iff_rootList _ q σ).mp h
      exact ⟨a,Finset.mem_union_left _ (Finset.mem_union_right _ ha),hσ⟩
    · exact ⟨-signSampleRadius (nonzeroFamilyProduct q).roots.toFinset,
        Finset.mem_union_right _ (by simp),fun i => (left_tail_sample_sign q i).trans (h i)⟩
    · exact ⟨signSampleRadius (nonzeroFamilyProduct q).roots.toFinset,
        Finset.mem_union_right _ (by simp),fun i => (right_tail_sample_sign q i).trans (h i)⟩

theorem signQueryExpression_zero_root_polynomial {m : ℕ} (q : Fin m → Polynomial ℝ)
    (σ : Fin m → SignType) : signQueryExpression 0 q σ=0 := by
  rw [signQueryExpression,← root_sign_count_from_tarskiQueries,rootSignCount_zero_polynomial]
  rfl

end BfgsVerification.RealAlgebraicGeometry
