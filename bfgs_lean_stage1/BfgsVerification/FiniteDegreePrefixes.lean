import BfgsVerification.LeadingCoefficientStrata

/-! An explicit finite family of symbolic prefixes captures every nonzero
specialization of a polynomial, with its actual leading coefficient retained. -/
noncomputable section
open scoped BigOperators
open Polynomial Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {R S : Type*} [CommRing R] [CommRing S]

def degreePrefix (q : Polynomial R) (N : ℕ) : Polynomial R :=
  ∑ j ∈ Finset.range (N+1), monomial j (q.coeff j)

theorem degreePrefix_coeff (q : Polynomial R) (N j : ℕ) :
    (degreePrefix q N).coeff j=if j≤N then q.coeff j else 0 := by
  classical
  simp [degreePrefix,coeff_sum,coeff_monomial,Finset.mem_range,Nat.lt_succ_iff]

theorem degreePrefix_natDegree_le (q : Polynomial R) (N : ℕ) :
    (degreePrefix q N).natDegree≤N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  simp [degreePrefix_coeff,not_le_of_gt hj]

theorem degreePrefix_natDegree {q : Polynomial R} {N : ℕ} (hN : q.coeff N≠0) :
    (degreePrefix q N).natDegree=N :=
  natDegree_eq_of_le_of_coeff_ne_zero (degreePrefix_natDegree_le q N)
    (by simpa [degreePrefix_coeff] using hN)

theorem degreePrefix_map (q : Polynomial R) (f : R →+* S) (N : ℕ)
    (hdeg : (q.map f).natDegree≤N) : (degreePrefix q N).map f=q.map f := by
  apply Polynomial.ext
  intro j
  rw [coeff_map,degreePrefix_coeff]
  by_cases hj : j≤N
  · simp [hj]
  · rw [if_neg hj,map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (Nat.lt_of_not_ge hj))).symm

theorem degreePrefix_leadingCoeff_specialize (q : Polynomial R) (f : R →+* S)
    (hq : q.map f≠0) :
    f (degreePrefix q (q.map f).natDegree).leadingCoeff≠0 := by
  have hc : f (q.coeff (q.map f).natDegree)≠0 := by
    rw [← coeff_map,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq
  have hc0 : q.coeff (q.map f).natDegree≠0 := by
    intro he
    exact hc (by rw [he,map_zero])
  rw [leadingCoeff,degreePrefix_natDegree hc0,degreePrefix_coeff,if_pos le_rfl]
  exact hc

theorem exists_degreePrefix_specialize (q : Polynomial R) (f : R →+* S)
    (hq : q.map f≠0) :
    ∃ N ∈ Finset.range (q.natDegree+1), (degreePrefix q N).map f=q.map f ∧
      f (degreePrefix q N).leadingCoeff≠0 := by
  refine ⟨(q.map f).natDegree,Finset.mem_range.mpr
    (Nat.lt_succ_of_le natDegree_map_le),degreePrefix_map q f _ le_rfl,
    degreePrefix_leadingCoeff_specialize q f hq⟩

end RealAlgebraicGeometry
end BfgsVerification
