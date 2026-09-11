import BfgsVerification.AffineWhiteningLimits
import BfgsVerification.RadialHessian

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection
variable {n : ℕ}

def secondMap (A : Mat n) (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ) :
    Vec n →L[ℝ] Vec n →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Vec n) (Vec n) ℝ).flip (matrixCLM A)).comp (B.comp (matrixCLM A))

@[simp] theorem secondMap_apply (A : Mat n) (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ) (u v : Vec n) :
    secondMap A B u v=B (A.mulVec u) (A.mulVec v) := rfl

theorem fderiv_objective (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x : Vec n) :
    fderiv ℝ (objective A F) x=(fderiv ℝ F (A.mulVec x)).comp (matrixCLM A) :=
  (linearEquiv A hA).comp_right_fderiv

theorem second_hasFDerivAt (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x : Vec n)
    (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ) (hB : HasFDerivAt (fderiv ℝ F) B (A.mulVec x)) :
    HasFDerivAt (fderiv ℝ (objective A F)) (secondMap A B) x := by
  have he : fderiv ℝ (objective A F)=fun z =>
      ((ContinuousLinearMap.compL ℝ (Vec n) (Vec n) ℝ).flip (matrixCLM A)) (fderiv ℝ F (A.mulVec z)) := by
    funext z
    exact fderiv_objective A hA F z
  rw [he]
  exact ((ContinuousLinearMap.compL ℝ (Vec n) (Vec n) ℝ).flip (matrixCLM A)).hasFDerivAt.comp x
    (hB.comp x (matrixCLM A).hasFDerivAt)

theorem bilinearMatrix_pairing (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ) (u v : Vec n) :
    dot u ((RadialHessian.bilinearMatrix B).mulVec v)=B u v := by
  have hl (l : Vec n →L[ℝ] ℝ) (w : Vec n) : l w=∑i,l (Pi.single i 1)*w i := by
    have h := congrArg (fun l : Vec n →L[ℝ] ℝ => l w) (gradientFunctional_coordinates l)
    simpa only [gradientFunctional_apply,dot] using h.symm
  have hB : B u=∑i,u i • B (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h : Pi.single i (u i)=u i • (Pi.single i 1 : Vec n) := by
      simpa only [smul_eq_mul,mul_one] using Pi.single_smul' i (u i) (1 : ℝ)
    rw [h,map_smul]
  rw [hB]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp only [dot,Matrix.mulVec,dotProduct,RadialHessian.bilinearMatrix]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => u i*z) (hl (B (Pi.single i 1)) v).symm)

theorem bilinearMatrix_secondMap (A : Mat n) (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ) :
    RadialHessian.bilinearMatrix (secondMap A B)=Aᵀ*RadialHessian.bilinearMatrix B*A := by
  ext i j
  let Q := RadialHessian.bilinearMatrix B
  have hp : dot (Pi.single i 1) ((Aᵀ*Q*A).mulVec (Pi.single j 1))=
      dot (A.mulVec (Pi.single i 1)) (Q.mulVec (A.mulVec (Pi.single j 1))) := by
    simp only [← Matrix.mulVec_mulVec]
    calc
      dot (Pi.single i 1) (Aᵀ.mulVec (Q.mulVec (A.mulVec (Pi.single j 1)))) =
          dot (Aᵀ.mulVec (Q.mulVec (A.mulVec (Pi.single j 1)))) (Pi.single i 1) := dotProduct_comm _ _
      _ = dot (Q.mulVec (A.mulVec (Pi.single j 1))) (A.mulVec (Pi.single i 1)) := dot_transpose_mulVec _ _ _
      _ = _ := dotProduct_comm _ _
  change B (A.mulVec (Pi.single i 1)) (A.mulVec (Pi.single j 1))=(Aᵀ*Q*A) i j
  rw [← bilinearMatrix_pairing,← hp]
  simp only [dot,Matrix.mulVec_single_one,single_one_dotProduct,Matrix.transpose_apply]
  exact single_one_dotProduct i _

theorem second_differentiableAt_iff (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x : Vec n) :
    DifferentiableAt ℝ (fderiv ℝ (objective A F)) x ↔
      DifferentiableAt ℝ (fderiv ℝ F) (A.mulVec x) := by
  constructor
  · intro hT
    have hAi : (A⁻¹).det≠0 := by rw [Matrix.det_nonsing_inv]; simpa only [Ring.inverse_eq_inv] using inv_ne_zero hA
    have he : objective A⁻¹ (objective A F)=F := by
      funext z
      exact congrArg F (map_point A hA z)
    have ht : DifferentiableAt ℝ (fderiv ℝ (objective A F)) (A⁻¹.mulVec (A.mulVec x)) := by
      simpa only [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hA.isUnit,Matrix.one_mulVec] using hT
    have hh := (second_hasFDerivAt A⁻¹ hAi (objective A F) (A.mulVec x) _ ht.hasFDerivAt).differentiableAt
    rwa [he] at hh
  · intro hF
    exact (second_hasFDerivAt A hA F x _ hF.hasFDerivAt).differentiableAt

theorem hessian_formula (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x : Vec n)
    (hF : DifferentiableAt ℝ (fderiv ℝ F) (A.mulVec x)) :
    RadialHessian.matrix (objective A F) x=Aᵀ*RadialHessian.matrix F (A.mulVec x)*A := by
  rw [RadialHessian.matrix,(second_hasFDerivAt A hA F x _ hF.hasFDerivAt).fderiv,
    bilinearMatrix_secondMap]
  rfl

theorem hessian_quadratic (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x v : Vec n)
    (hF : DifferentiableAt ℝ (fderiv ℝ F) (A.mulVec x)) :
    metricEnergy (RadialHessian.matrix (objective A F) x) v=
      metricEnergy (RadialHessian.matrix F (A.mulVec x)) (A.mulVec v) := by
  rw [hessian_formula A hA F x hF]
  exact (project_energy Aᵀ _ v).symm

theorem hessian_bounds_whitening [NeZero n] (H : Mat n) (hH : H.PosDef)
    (F : Vec n → ℝ) (x : Vec n) (hF : DifferentiableAt ℝ (fderiv ℝ F) ((squareRoot H hH).mulVec x))
    (μ L : ℝ) (hμ : 0 ≤ μ) (hL : 0 ≤ L)
    (hb : ∀v,μ*sqNorm v ≤ metricEnergy (RadialHessian.matrix F ((squareRoot H hH).mulVec x)) v ∧
      metricEnergy (RadialHessian.matrix F ((squareRoot H hH).mulVec x)) v ≤ L*sqNorm v) (v : Vec n) :
    (μ*minEigenvalue H hH.1)*sqNorm v ≤
        metricEnergy (RadialHessian.matrix (objective (squareRoot H hH) F) x) v ∧
      metricEnergy (RadialHessian.matrix (objective (squareRoot H hH) F) x) v ≤
        (L*maxEigenvalue H hH.1)*sqNorm v := by
  rw [hessian_quadratic _ (squareRoot_det_ne_zero _ hH) F x v hF]
  have hs := squareRoot_norm_bounds H hH v
  obtain ⟨hl,hu⟩ := hb ((squareRoot H hH).mulVec v)
  constructor
  · calc
      (μ*minEigenvalue H hH.1)*sqNorm v ≤ μ*sqNorm ((squareRoot H hH).mulVec v) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs.1 hμ
      _ ≤ _ := hl
  · calc
      _ ≤ L*sqNorm ((squareRoot H hH).mulVec v) := hu
      _ ≤ (L*maxEigenvalue H hH.1)*sqNorm v := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs.2 hL

end BfgsVerification.AffineWhitening
