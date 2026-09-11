import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.ParametricFixedPoint

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def oneSubEquiv (C : E →L[ℝ] E) (hC : ‖C‖<1) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub C hC)

theorem oneSubEquiv_apply (C : E →L[ℝ] E) (hC : ‖C‖<1) (x : E) :
    oneSubEquiv C hC x=x-C x := rfl

def triangularEquiv (P : S →L[ℝ] E) (M : E ≃L[ℝ] E) : (S×E) ≃L[ℝ] (S×E) where
  toFun p := (p.1,M p.2-P p.1)
  invFun p := (p.1,M.symm (p.2+P p.1))
  map_add' p q := by ext <;> simp <;> abel
  map_smul' c p := by ext <;> simp [smul_sub]
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk
    ((M.continuous.comp continuous_snd).sub (P.continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk
    (M.symm.continuous.comp (continuous_snd.add (P.continuous.comp continuous_fst)))

theorem triangularEquiv_apply (P : S →L[ℝ] E) (M : E ≃L[ℝ] E) (p : S×E) :
    triangularEquiv P M p=(p.1,M p.2-P p.1) := rfl

theorem triangularEquiv_symm_apply (P : S →L[ℝ] E) (M : E ≃L[ℝ] E) (p : S×E) :
    (triangularEquiv P M).symm p=(p.1,M.symm (p.2+P p.1)) := rfl

def residualMap (Φ : S×E → E) (p : S×E) : S×E := (p.1,p.2-Φ p)

theorem residualMap_hasFDerivAt {Φ : S×E → E} (P : S →L[ℝ] E) (C : E →L[ℝ] E)
    (hC : ‖C‖<1) (hΦ : HasFDerivAt Φ (P.coprod C) 0) :
    HasFDerivAt (residualMap Φ) (triangularEquiv P (oneSubEquiv C hC)).toContinuousLinearMap 0 := by
  have hraw := ((ContinuousLinearMap.fst ℝ S E).hasFDerivAt (x := (0 : S×E))).prodMk
    (((ContinuousLinearMap.snd ℝ S E).hasFDerivAt (x := (0 : S×E))).sub hΦ)
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  apply Prod.ext
  · rfl
  · change p.2-(P p.1+C p.2)=oneSubEquiv C hC p.2-P p.1
    rw [oneSubEquiv_apply]
    abel

theorem residualMap_contDiffAt {Φ : S×E → E} {n : WithTop ℕ∞}
    (hΦ : ContDiffAt ℝ n Φ 0) : ContDiffAt ℝ n (residualMap Φ) 0 :=
  contDiffAt_fst.prodMk (contDiffAt_snd.sub hΦ)

theorem residualMap_zero {Φ : S×E → E} (hΦ : Φ 0=0) : residualMap Φ 0=0 := by
  simp [residualMap,hΦ]

end BfgsVerification.ParametricFixedPoint
