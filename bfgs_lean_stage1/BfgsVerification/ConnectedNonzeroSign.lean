import BfgsVerification.FiniteSmoothCovers

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem sign_constant_on_preconnected {E : Type*} [TopologicalSpace E]
    {S : Set E} (hS : IsPreconnected S) {f : E → ℝ} (hf : ContinuousOn f S)
    (hne : ∀ x ∈ S, f x ≠ 0) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    SignType.sign (f x) = SignType.sign (f y) := by
  have hpos : 0 < f x ↔ 0 < f y := by
    constructor
    · intro hxpos
      by_contra hyn
      obtain ⟨z,hz,hz0⟩ := hS.intermediate_value hy hx hf
        (show (0 : ℝ) ∈ Icc (f y) (f x) from ⟨le_of_not_gt hyn,hxpos.le⟩)
      exact hne z hz hz0
    · intro hypos
      by_contra hxn
      obtain ⟨z,hz,hz0⟩ := hS.intermediate_value hx hy hf
        (show (0 : ℝ) ∈ Icc (f x) (f y) from ⟨le_of_not_gt hxn,hypos.le⟩)
      exact hne z hz hz0
  by_cases hxpos : 0 < f x
  · rw [sign_eq_one_iff.mpr hxpos,sign_eq_one_iff.mpr (hpos.mp hxpos)]
  · have hyneg : f y < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => hxpos (hpos.mpr h))) (hne y hy)
    have hxneg : f x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) (hne x hx)
    rw [sign_eq_neg_one_iff.mpr hxneg,sign_eq_neg_one_iff.mpr hyneg]

theorem polynomial_sign_constant_on_smooth_connected {σ : Type*} [Fintype σ]
    {S : Set (σ → ℝ)} (hS : PiecewiseSmoothConnected S) (p : MvPolynomial σ ℝ)
    (hne : ∀ x ∈ S, MvPolynomial.eval x p ≠ 0) {x y : σ → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    SignType.sign (MvPolynomial.eval x p) = SignType.sign (MvPolynomial.eval y p) :=
  sign_constant_on_preconnected hS.isPreconnected (MvPolynomial.continuous_eval p).continuousOn hne hx hy

end RealAlgebraicGeometry
end BfgsVerification
