import BfgsVerification.LEmbeddingGeometryTargets

noncomputable section
open Matrix
namespace BfgsVerification.LEmbedding

theorem branch_last_second_hasFDerivAt (x : Vec 2) :
    HasFDerivAt (fderiv ℝ (branch 3)) (mu • LQuadraticSeed.pairingMap) x := by
  have he : fderiv ℝ (branch 3)=fun z => (mu • LQuadraticSeed.pairingMap) z+
      gradientFunctional (![0,1] : Vec 2) := by
    funext z
    rw [(branch_hasGradient 3 z).fderiv]
    have hz : branchGradient 3 z=mu • z+![0,1] := rfl
    ext v
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,LQuadraticSeed.pairingMap_apply,
      gradientFunctional_apply,hz,dot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  exact (mu • LQuadraticSeed.pairingMap).hasFDerivAt.add_const _

theorem branch_last_hessian (x : Vec 2) : RadialHessian.matrix (branch 3) x=mu • (1 : Mat 2) := by
  rw [RadialHessian.matrix,(branch_last_second_hasFDerivAt x).fderiv]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [RadialHessian.bilinearMatrix,ContinuousLinearMap.smul_apply,
      LQuadraticSeed.pairingMap_apply,gradientFunctional_apply,dot,Fin.sum_univ_two]

end BfgsVerification.LEmbedding
