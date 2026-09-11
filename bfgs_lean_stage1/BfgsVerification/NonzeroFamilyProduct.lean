import BfgsVerification.FiniteRootGap
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open scoped BigOperators
open Set Filter Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

/-- Actual nonzero-factor product, with empty product one. -/
def nonzeroFamilyProduct {m : ℕ} (q : Fin m → Polynomial ℝ) : Polynomial ℝ := by
  classical
  exact ∏i∈Finset.univ.filter (fun i => q i≠0),q i

theorem nonzeroFamilyProduct_ne_zero {m : ℕ} (q : Fin m → Polynomial ℝ) :
    nonzeroFamilyProduct q≠0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (Finset.mem_filter.mp hi).2

theorem nonzeroFamilyProduct_eval_zero_iff {m : ℕ} (q : Fin m → Polynomial ℝ) (x : ℝ) :
    (nonzeroFamilyProduct q).eval x=0 ↔ ∃i,q i≠0 ∧ (q i).eval x=0 := by
  classical
  simp only [nonzeroFamilyProduct,Polynomial.eval_prod,Finset.prod_eq_zero_iff,
    Finset.mem_filter,Finset.mem_univ,true_and]

theorem rootBoundary_eq_nonzeroFamilyProduct_roots {m : ℕ} (q : Fin m → Polynomial ℝ) :
    rootBoundary (Finset.univ.image q)=(nonzeroFamilyProduct q).roots.toFinset := by
  classical
  ext x
  rw [Multiset.mem_toFinset,Polynomial.mem_roots (nonzeroFamilyProduct_ne_zero q)]
  change x∈rootBoundary (Finset.univ.image q) ↔ (nonzeroFamilyProduct q).eval x=0
  rw [nonzeroFamilyProduct_eval_zero_iff]
  constructor
  · intro hx
    obtain ⟨p,hp,hroot⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    have hqi : q i≠0 := by
      intro hzero
      simpa only [hzero,Polynomial.roots_zero,Multiset.toFinset_zero,Finset.not_mem_empty] using hroot
    exact ⟨i,hqi,(Polynomial.mem_roots hqi).mp (Multiset.mem_toFinset.mp hroot)⟩
  · rintro ⟨i,hi,hroot⟩
    exact mem_rootBoundary (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) hi hroot

theorem sign_eq_of_zero_positive_iff {a b : ℝ} (hz : a=0 ↔ b=0) (hp : 0<a ↔ 0<b) :
    SignType.sign a=SignType.sign b := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hbn : b<0 := lt_of_le_of_ne
      (le_of_not_gt (fun hb => (not_lt_of_ge ha.le) (hp.mpr hb)))
      (fun hb => ha.ne (hz.mpr hb))
    rw [sign_neg ha,sign_neg hbn]
  · rw [ha,hz.mp ha]
  · rw [sign_pos ha,sign_pos (hp.mp ha)]

/-- Equality of product-root cut profiles preserves every original polynomial
sign, including zero family members. -/
theorem family_signs_eq_of_product_profile {m : ℕ} (q : Fin m → Polynomial ℝ)
    {x y : ℝ} (hx : x∉(nonzeroFamilyProduct q).roots.toFinset)
    (hy : y∉(nonzeroFamilyProduct q).roots.toFinset)
    (hp : cutProfile (nonzeroFamilyProduct q).roots.toFinset x=
      cutProfile (nonzeroFamilyProduct q).roots.toFinset y) :
    ∀i,SignType.sign ((q i).eval x)=SignType.sign ((q i).eval y) := by
  rw [← rootBoundary_eq_nonzeroFamilyProduct_roots] at hx hy hp
  intro i
  have h := polynomial_sign_constant_on_profile (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) hx hy hp
  exact sign_eq_of_zero_positive_iff h.1 h.2

end BfgsVerification.RealAlgebraicGeometry
