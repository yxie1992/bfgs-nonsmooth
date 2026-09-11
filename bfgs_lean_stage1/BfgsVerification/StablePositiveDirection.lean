import BfgsVerification.LocalStableOrbit

noncomputable section
open scoped Topology ZeroAtInfty NNReal
open Set Filter
namespace BfgsVerification.LocalStableOrbit

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- Prescribing a positive stable coordinate gives a nontrivial forward orbit
in an arbitrarily small neighborhood. No nonlinear stable manifold is assumed. -/
theorem positive_stable_direction (A : S →L[ℝ] S) (L : U ≃L[ℝ] U) (T : S×U → S×U)
    (hT0 : T 0=0) (hT : HasStrictFDerivAt T (A.prodMap L.toContinuousLinearMap) 0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1)
    (lambda : S →L[ℝ] ℝ) (e : S) (he : 0<lambda e) {r : ℝ} (hr : 0<r) :
    ∃ w : ℕ → S×U, (∀ n, ‖w n‖≤r) ∧ Tendsto w atTop (𝓝 0) ∧
      0<lambda (w 0).1 ∧ w 0≠0 ∧ ∀ n, w (n+1)=T (w n) := by
  obtain ⟨R,hR,hsol⟩ := local_stable_orbits A L T hT0 hT hA hB hr
  let t := R/(‖e‖+1)
  have hden : 0<‖e‖+1 := by positivity
  have ht : 0<t := div_pos hR hden
  have htR : t*(‖e‖+1)=R := div_mul_cancel₀ R hden.ne'
  have ha : ‖t • e‖≤R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  obtain ⟨w,hw,hlim,hstart,hrec⟩ := hsol (t • e) ha
  have hp : 0<lambda (w 0).1 := by
    rw [hstart, map_smul, smul_eq_mul]
    exact mul_pos ht he
  refine ⟨w,hw,hlim,hp,?_,hrec⟩
  intro hz
  rw [hz] at hp
  exact (lt_irrefl (0 : ℝ)) (by simpa only [Prod.fst_zero, map_zero] using hp)

end BfgsVerification.LocalStableOrbit
