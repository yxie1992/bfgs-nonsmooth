import BfgsVerification.PolynomialCriticalSamples
import BfgsVerification.PolynomialInfinitySigns

noncomputable section
open scoped BigOperators Topology
open Set Filter Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

/-- The explicit right tail sample has the actual leading-coefficient sign
for every original member, including zero and constant polynomials. -/
theorem right_tail_sample_sign {m : ℕ} (q : Fin m → Polynomial ℝ) (i : Fin m) :
    SignType.sign ((q i).eval (signSampleRadius (nonzeroFamilyProduct q).roots.toFinset))=
      SignType.sign (q i).leadingCoeff := by
  classical
  let B := (nonzeroFamilyProduct q).roots.toFinset
  let R := signSampleRadius B
  obtain ⟨x,hxR,he⟩ := ((eventually_gt_atTop R).and (polynomial_sign_atTop (q i))).exists
  have hx : x∉B := by
    intro hx
    exact (not_lt_of_ge (mem_lt_signSampleRadius hx).2.le) hxR
  have hprof : cutProfile B x=B := by
    apply Finset.filter_eq_self.mpr
    intro b hb
    exact (mem_lt_signSampleRadius hb).2.trans hxR
  exact (family_signs_eq_of_product_profile q (signSampleRadius_not_mem B).2 hx
    ((signSampleRadius_profiles B).2.trans hprof.symm) i).trans he

/-- The explicit left tail sample has the actual parity/leading-coefficient
sign; no exclusion of zero or constant branches is imposed. -/
theorem left_tail_sample_sign {m : ℕ} (q : Fin m → Polynomial ℝ) (i : Fin m) :
    SignType.sign ((q i).eval (-signSampleRadius (nonzeroFamilyProduct q).roots.toFinset))=
      (-1 : SignType)^(q i).natDegree*SignType.sign (q i).leadingCoeff := by
  classical
  let B := (nonzeroFamilyProduct q).roots.toFinset
  let R := signSampleRadius B
  obtain ⟨x,hxR,he⟩ := ((eventually_lt_atBot (-R)).and (polynomial_sign_atBot (q i))).exists
  have hx : x∉B := by
    intro hx
    exact (not_lt_of_ge (mem_lt_signSampleRadius hx).1.le) hxR
  have hprof : cutProfile B x=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro b hb
    obtain ⟨hb,hbx⟩ := Finset.mem_filter.mp hb
    exact (not_lt_of_ge (mem_lt_signSampleRadius hb).1.le) (hbx.trans hxR)
  exact (family_signs_eq_of_product_profile q (signSampleRadius_not_mem B).1 hx
    ((signSampleRadius_profiles B).1.trans hprof.symm) i).trans he

end BfgsVerification.RealAlgebraicGeometry
