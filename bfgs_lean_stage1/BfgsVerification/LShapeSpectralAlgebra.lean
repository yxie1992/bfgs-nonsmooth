import BfgsVerification.LNormalizedReturn
import BfgsVerification.IntervalBounds

noncomputable section
open scoped Topology
open Set Matrix
namespace BfgsVerification.LShapeSpectralAlgebra

def characteristic (J : Mat 2) (lam : ℝ) : ℝ :=
  lam^2-(J 0 0+J 1 1)*lam+(J 0 0*J 1 1-J 0 1*J 1 0)

theorem characteristic_eq_det (J : Mat 2) (lam : ℝ) :
    characteristic J lam=(J-lam • (1 : Mat 2)).det := by
  simp [characteristic,Matrix.det_fin_two]
  ring

theorem signs_of_entry_bounds {J : Mat 2}
    (h00 : IntervalBounds.Bounds (11123986249/10^10) (J 0 0) (11123986253/10^10))
    (h01 : IntervalBounds.Bounds (6459701025/10^10) (J 0 1) (6459701029/10^10))
    (h10 : IntervalBounds.Bounds (7515015701/10^10) (J 1 0) (7515015708/10^10))
    (h11 : IntervalBounds.Bounds (4905136882/10^10) (J 1 1) (4905136890/10^10)) :
    0 < characteristic J (38/1000) ∧ characteristic J (39/1000) < 0 ∧
      characteristic J (1564/1000) < 0 ∧ 0 < characteristic J (1565/1000) := by
  have ht := IntervalBounds.add h00 h11
  have hd := IntervalBounds.sub
    (IntervalBounds.mul_nn h00 h11 (by norm_num) (by norm_num))
    (IntervalBounds.mul_nn h01 h10 (by norm_num) (by norm_num))
  have hb (lam : ℝ) (hl : 0 ≤ lam) := IntervalBounds.add
    (IntervalBounds.sub (IntervalBounds.exact (lam^2))
      (IntervalBounds.mul_nn ht (IntervalBounds.exact lam) (by norm_num) hl)) hd
  have h0 := hb (38/1000) (by norm_num)
  have h1 := hb (39/1000) (by norm_num)
  have h2 := hb (1564/1000) (by norm_num)
  have h3 := hb (1565/1000) (by norm_num)
  change IntervalBounds.Bounds _ (characteristic J (38/1000)) _ at h0
  change IntervalBounds.Bounds _ (characteristic J (39/1000)) _ at h1
  change IntervalBounds.Bounds _ (characteristic J (1564/1000)) _ at h2
  change IntervalBounds.Bounds _ (characteristic J (1565/1000)) _ at h3
  norm_num [IntervalBounds.Bounds] at h0 h1 h2 h3
  norm_num at ⊢
  exact ⟨by linarith only [h0.1],by linarith only [h1.2],
    by linarith only [h2.2],by linarith only [h3.1]⟩

theorem two_roots_of_signs {J : Mat 2}
    (hs0 : 0 < characteristic J (38/1000)) (hs1 : characteristic J (39/1000) < 0)
    (hu0 : characteristic J (1564/1000) < 0) (hu1 : 0 < characteristic J (1565/1000)) :
    ∃ ls lu : ℝ, (38/1000 < ls ∧ ls < 39/1000) ∧
      (1564/1000 < lu ∧ lu < 1565/1000) ∧
      characteristic J ls=0 ∧ characteristic J lu=0 ∧
      ∀ lam, characteristic J lam=(lam-ls)*(lam-lu) := by
  have hc : Continuous (characteristic J) := by unfold characteristic; fun_prop
  obtain ⟨ls,hls,hs⟩ := intermediate_value_Icc' (by norm_num : (38/1000 : ℝ) ≤ 39/1000)
    hc.continuousOn (show (0 : ℝ)∈Icc (characteristic J (39/1000)) (characteristic J (38/1000)) from ⟨hs1.le,hs0.le⟩)
  obtain ⟨lu,hlu,hu⟩ := intermediate_value_Icc (by norm_num : (1564/1000 : ℝ) ≤ 1565/1000)
    hc.continuousOn (show (0 : ℝ)∈Icc (characteristic J (1564/1000)) (characteristic J (1565/1000)) from ⟨hu0.le,hu1.le⟩)
  have hls' : 38/1000 < ls ∧ ls < 39/1000 := by
    constructor
    · apply lt_of_le_of_ne hls.1
      intro he
      rw [← he] at hs
      exact hs0.ne' hs
    · apply lt_of_le_of_ne hls.2
      intro he
      rw [he] at hs
      exact hs1.ne hs
  have hlu' : 1564/1000 < lu ∧ lu < 1565/1000 := by
    constructor
    · apply lt_of_le_of_ne hlu.1
      intro he
      rw [← he] at hu
      exact hu0.ne hu
    · apply lt_of_le_of_ne hlu.2
      intro he
      rw [he] at hu
      exact hu1.ne' hu
  have hne : ls-lu ≠ 0 := by linarith [hls'.2,hlu'.1]
  have hmul : (ls-lu)*((J 0 0+J 1 1)-ls-lu)=0 := by
    dsimp [characteristic] at hs hu
    nlinarith [hs,hu]
  have htrace : J 0 0+J 1 1=ls+lu := by
    have h := (mul_eq_zero.mp hmul).resolve_left hne
    linarith
  have hdet : J 0 0*J 1 1-J 0 1*J 1 0=ls*lu := by
    dsimp [characteristic] at hs
    rw [htrace] at hs
    nlinarith
  refine ⟨ls,lu,hls',hlu',hs,hu,?_⟩
  intro lam
  rw [characteristic,htrace,hdet]
  ring

def eigenvector (J : Mat 2) (lam : ℝ) : Vec 2 := ![J 0 1,lam-J 0 0]

theorem eigenvector_nonzero {J : Mat 2} (hJ : J 0 1 ≠ 0) (lam : ℝ) : eigenvector J lam ≠ 0 := by
  intro h
  exact hJ (congrFun h 0)

theorem eigenvector_equation {J : Mat 2} {lam : ℝ} (hlam : characteristic J lam=0) :
    J.mulVec (eigenvector J lam)=lam • eigenvector J lam := by
  ext i
  fin_cases i
  · simp [eigenvector,Matrix.mulVec,dotProduct,Fin.sum_univ_two]; ring
  · simp [eigenvector,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    dsimp [characteristic] at hlam
    nlinarith

end BfgsVerification.LShapeSpectralAlgebra
