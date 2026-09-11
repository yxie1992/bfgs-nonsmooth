import BfgsVerification.FiniteAffineLocal
import BfgsVerification.LQuadraticSeed

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.FiniteAffineLocal

/-- An actual affine perturbation of the literal Euclidean quadratic. -/
def affineQuadratic (μ : ℝ) (A : Vec 2 →L[ℝ] ℝ) (c : ℝ) (z : Vec 2) : ℝ :=
  LQuadraticSeed.quadratic μ z+A z+c

theorem affineQuadratic_hasFDerivAt (μ : ℝ) (A : Vec 2 →L[ℝ] ℝ) (c : ℝ) (x : Vec 2) :
    HasFDerivAt (affineQuadratic μ A c)
      ((μ • LQuadraticSeed.pairingMap) x+A) x := by
  convert ((LQuadraticSeed.quadratic_hasGradient μ x).add A.hasFDerivAt).add_const c using 1
  ext v
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    LQuadraticSeed.pairingMap_apply,gradientFunctional_apply,dot,Pi.smul_apply,smul_eq_mul,
    mul_assoc,Finset.mul_sum]

theorem affineQuadratic_second (μ : ℝ) (A : Vec 2 →L[ℝ] ℝ) (c : ℝ) (x : Vec 2) :
    HasFDerivAt (fderiv ℝ (affineQuadratic μ A c)) (μ • LQuadraticSeed.pairingMap) x := by
  have he : fderiv ℝ (affineQuadratic μ A c)=fun z => (μ • LQuadraticSeed.pairingMap) z+A := by
    funext z
    exact (affineQuadratic_hasFDerivAt μ A c z).fderiv
  rw [he]
  exact (μ • LQuadraticSeed.pairingMap).hasFDerivAt.add_const A

theorem affineQuadratic_hessian (μ : ℝ) (A : Vec 2 →L[ℝ] ℝ) (c : ℝ) (x : Vec 2) :
    RadialHessian.matrix (affineQuadratic μ A c) x=μ • (1 : Mat 2) := by
  rw [RadialHessian.matrix,(affineQuadratic_second μ A c x).fderiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RadialHessian.bilinearMatrix,ContinuousLinearMap.smul_apply,
      LQuadraticSeed.pairingMap_apply,gradientFunctional_apply,dot,Fin.sum_univ_two]

theorem hessian_of_affine_residual {p : Vec 2 → ℝ} {x : Vec 2} (μ : ℝ)
    (hp : AffineGerm p x) :
    HasFDerivAt (fderiv ℝ (fun z => LQuadraticSeed.quadratic μ z+p z))
      (μ • LQuadraticSeed.pairingMap) x ∧
    RadialHessian.matrix (fun z => LQuadraticSeed.quadratic μ z+p z) x=μ • (1 : Mat 2) := by
  obtain ⟨A,c,he⟩ := hp
  have hf : (fun z => LQuadraticSeed.quadratic μ z+p z) =ᶠ[𝓝 x] affineQuadratic μ A c := by
    filter_upwards [he] with z hz
    simp only [affineQuadratic,hz]
    ring
  refine ⟨(affineQuadratic_second μ A c x).congr_of_eventuallyEq hf.fderiv,?_⟩
  change RadialHessian.bilinearMatrix _=_
  rw [hf.fderiv.fderiv_eq]
  exact affineQuadratic_hessian μ A c x

end BfgsVerification.FiniteAffineLocal
