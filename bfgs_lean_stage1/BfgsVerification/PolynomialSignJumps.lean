import BfgsVerification.RationalRemainderInvariance
import BfgsVerification.PolynomialInfinitySigns
import BfgsVerification.FiniteJumpTelescoping

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

def polynomialRightSign (p : Polynomial ℝ) (a : ℝ) : ℤ :=
  SignType.sign ((rootFactor p a).eval a)

def polynomialLeftSign (p : Polynomial ℝ) (a : ℝ) : ℤ :=
  (-1 : ℤ)^p.rootMultiplicity a * polynomialRightSign p a

theorem polynomialRightSign_of_ne_zero {p : Polynomial ℝ} {a : ℝ}
    (ha : p.eval a ≠ 0) : polynomialRightSign p a = (SignType.sign (p.eval a) : ℤ) := by
  have hm : p.rootMultiplicity a = 0 := Polynomial.rootMultiplicity_eq_zero ha
  have he := rootFactor_eval_factorization p a a
  rw [hm, pow_zero, one_mul] at he
  unfold polynomialRightSign
  rw [← he]

theorem polynomialRightSign_right_germ {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    ∀ᶠ x in 𝓝[>] a, polynomialRightSign p x = polynomialRightSign p a := by
  have hn : ∀ᶠ x in 𝓝[>] a, p.eval x ≠ 0 :=
    (polynomial_eventually_ne_punctured hp a).filter_mono
      (nhdsWithin_mono a (by intro x hx; exact ne_of_gt hx))
  filter_upwards [polynomial_sign_right_of_rootMultiplicity hp a, hn] with x hx hnx
  rw [polynomialRightSign_of_ne_zero hnx]
  exact congrArg (fun s : SignType => (s : ℤ)) hx

theorem polynomialRightSign_closed_right_germ {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    ∀ᶠ x in 𝓝[≥] a, polynomialRightSign p x = polynomialRightSign p a := by
  have hs : Ici a = insert a (Ioi a) := by
    ext x
    simp only [mem_Ici, mem_insert_iff, mem_Ioi]
    constructor
    · intro hx
      rcases hx.eq_or_lt with he | hl
      · exact Or.inl he.symm
      · exact Or.inr hl
    · rintro (rfl | hx)
      · exact le_rfl
      · exact hx.le
  rw [hs, nhdsWithin_insert, eventually_sup]
  exact ⟨by simp, polynomialRightSign_right_germ hp a⟩

theorem polynomialRightSign_left_germ {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    ∀ᶠ x in 𝓝[<] a, polynomialRightSign p x = polynomialLeftSign p a := by
  have hn : ∀ᶠ x in 𝓝[<] a, p.eval x ≠ 0 :=
    (polynomial_eventually_ne_punctured hp a).filter_mono
      (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  filter_upwards [polynomial_sign_left_of_rootMultiplicity hp a, hn] with x hx hnx
  rw [polynomialRightSign_of_ne_zero hnx]
  simpa only [SignType.coe_mul, SignType.coe_pow, SignType.coe_neg_one,
    polynomialLeftSign, polynomialRightSign] using congrArg (fun s : SignType => (s : ℤ)) hx

theorem polynomialLeftSign_eq_right_of_not_root {p : Polynomial ℝ} {a : ℝ}
    (ha : p.eval a ≠ 0) : polynomialLeftSign p a = polynomialRightSign p a := by
  have hm := Polynomial.rootMultiplicity_eq_zero ha
  simp [polynomialLeftSign, hm]

theorem polynomialRightSign_atTop {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, polynomialRightSign p x = (SignType.sign p.leadingCoeff : ℤ) := by
  filter_upwards [polynomial_sign_atTop p, p.eventually_no_roots hp] with x hx hnx
  rw [polynomialRightSign_of_ne_zero hnx]
  exact congrArg (fun s : SignType => (s : ℤ)) hx

theorem polynomialRightSign_atBot {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, polynomialRightSign p x =
      (-1 : ℤ)^p.natDegree * (SignType.sign p.leadingCoeff : ℤ) := by
  have hn : ∀ᶠ x in atBot, ¬ p.IsRoot x :=
    atBot_le_cofinite (Polynomial.finite_setOf_isRoot hp).compl_mem_cofinite
  filter_upwards [polynomial_sign_atBot p, hn] with x hx hnx
  rw [polynomialRightSign_of_ne_zero hnx]
  simpa only [SignType.coe_mul, SignType.coe_pow, SignType.coe_neg_one] using
    congrArg (fun s : SignType => (s : ℤ)) hx

theorem polynomial_sign_jump_sum {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∑ a ∈ p.roots.toFinset, (polynomialRightSign p a-polynomialLeftSign p a) =
      (SignType.sign p.leadingCoeff : ℤ) -
        (-1 : ℤ)^p.natDegree * (SignType.sign p.leadingCoeff : ℤ) := by
  classical
  apply finite_jump_telescope p.roots.toFinset (polynomialRightSign p) (polynomialLeftSign p)
    (polynomialRightSign_left_germ hp) (polynomialRightSign_closed_right_germ hp)
    ?_ _ _ (polynomialRightSign_atBot hp) (polynomialRightSign_atTop hp)
  intro a ha
  apply polynomialLeftSign_eq_right_of_not_root
  intro hr
  exact ha (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hr))

end RealAlgebraicGeometry
end BfgsVerification
