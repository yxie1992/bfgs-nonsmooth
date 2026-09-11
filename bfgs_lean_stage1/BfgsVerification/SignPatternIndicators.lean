import Mathlib.Data.Sign
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace BfgsVerification.RealAlgebraicGeometry

/-- Rational coefficients of the three exact indicator polynomials on signs.
The columns are powers 0, 1 and 2. -/
def signIndicatorCoeff (σ : SignType) (e : Fin 3) : ℚ :=
  if e=0 then (if σ=SignType.zero then 1 else 0)
  else if e=1 then (σ : ℚ)/2
  else if σ=SignType.zero then -1 else 1/2

theorem sign_indicator_identity (σ τ : SignType) :
    (∑e : Fin 3,signIndicatorCoeff σ e * (τ : ℚ)^e.val)=if τ=σ then 1 else 0 := by
  have h20 : (2 : Fin 3)≠0 := by decide
  have h21 : (2 : Fin 3)≠1 := by decide
  have hn : (-1 : SignType)≠0 := by decide
  have hn' : (0 : SignType)≠-1 := Ne.symm hn
  cases σ <;> cases τ <;>
    norm_num [signIndicatorCoeff,Fin.sum_univ_three,SignType.cast,h20,h21,hn,hn']

/-- The tensor-product coefficient is an actual finite rational product. -/
def signPatternCoeff {m : ℕ} (σ : Fin m → SignType) (e : Fin m → Fin 3) : ℚ :=
  ∏i,signIndicatorCoeff (σ i) (e i)

/-- The complete simultaneous indicator follows by a finite product-of-sums
expansion. No numerical matrix inversion or assumed sign table is used. -/
theorem sign_pattern_indicator {m : ℕ} (σ τ : Fin m → SignType) :
    (∑e : Fin m → Fin 3,signPatternCoeff σ e * ∏i,(τ i : ℚ)^(e i).val)=
      if τ=σ then 1 else 0 := by
  classical
  calc
    _ = ∏i,∑e : Fin 3,signIndicatorCoeff (σ i) e * (τ i : ℚ)^e.val := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact Finset.prod_mul_distrib.symm
    _ = ∏i,if τ i=σ i then (1 : ℚ) else 0 := by simp_rw [sign_indicator_identity]
    _ = _ := by
      by_cases h : τ=σ
      · simp [h]
      · rw [if_neg h]
        have hn : ∃i,τ i≠σ i := Function.ne_iff.mp h
        obtain ⟨i,hi⟩ := hn
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]

/-- The empty pattern has one coefficient and imposes no sign constraints. -/
theorem signPatternCoeff_empty (σ : Fin 0 → SignType) (e : Fin 0 → Fin 3) :
    signPatternCoeff σ e=1 := by simp [signPatternCoeff]

/-- Exact signs of real products commute with the finite product and powers. -/
theorem sign_product_powers {m : ℕ} (a : Fin m → ℝ) (e : Fin m → Fin 3) :
    SignType.sign (∏i,a i^(e i).val)=∏i,(SignType.sign (a i))^(e i).val := by
  change (signHom : ℝ →*₀ SignType) (∏i,a i^(e i).val)=_
  rw [map_prod]
  simp only [signHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,sign_pow]

/-- Integer and rational sign coercions are compatible with product moments. -/
theorem sign_product_powers_rat {m : ℕ} (a : Fin m → ℝ) (e : Fin m → Fin 3) :
    ((SignType.sign (∏i,a i^(e i).val) : ℤ) : ℚ)=
      ∏i,(SignType.sign (a i) : ℚ)^(e i).val := by
  rw [SignType.intCast_cast,sign_product_powers]
  change (SignType.castHom : SignType →*₀ ℚ) (∏i,(SignType.sign (a i))^(e i).val)=_
  rw [map_prod]
  simp only [map_pow,SignType.castHom_apply]

end BfgsVerification.RealAlgebraicGeometry
