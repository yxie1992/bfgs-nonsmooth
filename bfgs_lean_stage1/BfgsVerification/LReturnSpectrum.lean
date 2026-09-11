import BfgsVerification.LShapeSpectrum
import BfgsVerification.LReturnOrbitCore
import BfgsVerification.LExactDiagonalization

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix Polynomial
namespace BfgsVerification.LReturnSpectrum
open SeedOrbit LNormalizedReturn LShapeDerivative LShapeSpectrum LShapeSpectralAlgebra
open LExactDiagonalization

theorem actual_spectral_contract (μ : ℝ) :
    ∃ ls lu : ℝ, (38/1000 < ls ∧ ls < 39/1000) ∧
      (1564/1000 < lu ∧ lu < 1565/1000) ∧
      ∃ E : LBlockSplitting.Coordinates ≃L[ℝ] State,
        (∀ w, E w 4=w.1 1) ∧
        (∀ w, (fderiv ℝ (returnMap μ) seed) (E w)=E
          (LBlockSplitting.diagonalMap ![ls,seedRatio] w.1,
           LBlockSplitting.diagonalMap ![seedRatio⁻¹,seedRatio⁻¹,lu] w.2)) ∧
        (fderiv ℝ (returnMap μ) seed).toLinearMap.charpoly=
          (X-C seedRatio⁻¹)^2*(X-C ls)*(X-C lu)*(X-C seedRatio) := by
  obtain ⟨ls,lu,hs,hu,hsroot,huroot,hfactor⟩ := source_shape_roots
  have hr := tight_ratio root_tight_box.1 root_tight_box.2
  have hs0 : 0 < ls := by linarith [hs.1]
  have hsr : ls < seedRatio := by linarith [hs.2,hr.1]
  have hu1 : 1 < lu := by linarith [hu.1]
  have hr2 : 2 < 1/seedRatio := (lt_div_iff₀ source_ratio_pos_lt_one.1).mpr (by linarith [hr.2])
  rw [one_div] at hr2
  have hua : lu < seedRatio⁻¹ := by linarith [hu.2]
  have hs' : (ls-jacobian seedC seedD 0 0)*(ls-jacobian seedC seedD 1 1)=
      jacobian seedC seedD 0 1*jacobian seedC seedD 1 0 := by
    dsimp [characteristic] at hsroot
    nlinarith
  have hu' : (lu-jacobian seedC seedD 0 0)*(lu-jacobian seedC seedD 1 1)=
      jacobian seedC seedD 0 1*jacobian seedC seedD 1 0 := by
    dsimp [characteristic] at huroot
    nlinarith
  obtain ⟨E,hscale,hE⟩ := exact_block_diagonalization (LReturnOrbitCore.actual_block μ)
    source_ratio_pos_lt_one.1 source_ratio_pos_lt_one.2 hs0 hsr hu1 hua
    source_jacobian_offdiag_positive.ne' hs' hu'
  exact ⟨ls,lu,hs,hu,E,hscale,hE,charpoly_of_exact_diagonalization E hE⟩

theorem actual_scale_eigenvector (μ : ℝ) :
    ∃ v : State, v 4=1 ∧ (fderiv ℝ (returnMap μ) seed) v=seedRatio • v := by
  obtain ⟨ls,lu,hs,hu,E,hscale,hE,hchar⟩ := actual_spectral_contract μ
  let w : LBlockSplitting.Coordinates := (![0,1],![0,0,0])
  refine ⟨E w,hscale w,?_⟩
  rw [hE,← map_smul]
  congr 1
  apply Prod.ext <;> ext i <;> fin_cases i <;> simp [w,LBlockSplitting.diagonalMap_apply]

theorem actual_no_zero_or_unit_real_root (μ : ℝ) {lam : ℝ}
    (hroot : (fderiv ℝ (returnMap μ) seed).toLinearMap.charpoly.eval lam=0) :
    lam≠0 ∧ |lam|≠1 := by
  obtain ⟨ls,lu,hs,hu,E,hscale,hE,hchar⟩ := actual_spectral_contract μ
  rw [hchar] at hroot
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,mul_eq_zero,pow_eq_zero_iff (by decide : (2 : ℕ)≠0),sub_eq_zero] at hroot
  have hrs := source_ratio_pos_lt_one
  have hra : 1 < seedRatio⁻¹ := (one_lt_inv₀ hrs.1).mpr hrs.2
  have hls : 0 < ls := by linarith [hs.1]
  have hlu : 0 < lu := by linarith [hu.1]
  rcases hroot with ((h|h)|h)|h
  · subst lam
    rw [abs_of_pos (inv_pos.mpr hrs.1)]
    exact ⟨(inv_pos.mpr hrs.1).ne',ne_of_gt hra⟩
  · subst lam
    rw [abs_of_pos hls]
    exact ⟨hls.ne',ne_of_lt (by linarith [hs.2])⟩
  · subst lam
    rw [abs_of_pos hlu]
    exact ⟨hlu.ne',ne_of_gt (by linarith [hu.1])⟩
  · subst lam
    rw [abs_of_pos hrs.1]
    exact ⟨hrs.1.ne',ne_of_lt hrs.2⟩

/-- Hyperbolicity is checked over the complex roots of the actual real
characteristic polynomial, not just its real zeros. -/
theorem actual_no_unit_complex_root (μ : ℝ) {z : ℂ} (hz : ‖z‖=1) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (fderiv ℝ (returnMap μ) seed).toLinearMap.charpoly≠0 := by
  intro hroot
  obtain ⟨ls,lu,hs,hu,E,hscale,hE,hchar⟩ := actual_spectral_contract μ
  rw [hchar] at hroot
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_sub,Polynomial.eval₂_X,
    Polynomial.eval₂_C,mul_eq_zero,pow_eq_zero_iff (by decide : (2 : ℕ)≠0),sub_eq_zero] at hroot
  have hrs := source_ratio_pos_lt_one
  have hra : 1 < seedRatio⁻¹ := (one_lt_inv₀ hrs.1).mpr hrs.2
  have hls : 0 < ls := by linarith [hs.1]
  have hlu : 0 < lu := by linarith [hu.1]
  rcases hroot with ((h|h)|h)|h
  · rw [h] at hz
    change ‖(↑(seedRatio⁻¹) : ℂ)‖=1 at hz
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hrs.1)] at hz
    linarith
  · rw [h] at hz
    change ‖(↑ls : ℂ)‖=1 at hz
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hls] at hz
    linarith [hs.2]
  · rw [h] at hz
    change ‖(↑lu : ℂ)‖=1 at hz
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlu] at hz
    linarith [hu.1]
  · rw [h] at hz
    change ‖(↑seedRatio : ℂ)‖=1 at hz
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrs.1] at hz
    linarith [hrs.2]

end BfgsVerification.LReturnSpectrum
