import BfgsVerification.AffineRankLossObjective
import BfgsVerification.DEmbeddingObjective
import BfgsVerification.FixedNormalStrongConvex

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix Polynomial
namespace BfgsVerification.AffineRankLoss

def sign (i : Fin 2) : ℝ := if i=0 then 1 else -1
def hessian (i : Fin 2) : Mat 2 := !![2,sign i;sign i,2]
def secondMap (i : Fin 2) : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ :=
  ((2 • (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ)+sign i • ContinuousLinearMap.proj 1).smulRight
    (ContinuousLinearMap.proj 0))+
  ((sign i • (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ)+2 • ContinuousLinearMap.proj 1).smulRight
    (ContinuousLinearMap.proj 1))

theorem branch_contDiff (i : Fin 2) : ContDiff ℝ ⊤ (branch i) := by
  unfold branch
  fun_prop

theorem branch_second_hasFDerivAt (i : Fin 2) (x : Vec 2) :
    HasFDerivAt (fderiv ℝ (branch i)) (secondMap i) x := by
  have he : fderiv ℝ (branch i)=fun z => secondMap i z+(ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ) := by
    funext z
    rw [(branch_hasGradient i z).fderiv]
    ext v
    fin_cases i <;> simp [secondMap,sign,branchGradient,gradientFunctional_apply,dot,Fin.sum_univ_two] <;> ring
  rw [he]
  exact (secondMap i).hasFDerivAt.add_const _

theorem branch_hessian (i : Fin 2) (x : Vec 2) : RadialHessian.matrix (branch i) x=hessian i := by
  rw [RadialHessian.matrix,(branch_second_hasFDerivAt i x).fderiv]
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [RadialHessian.bilinearMatrix,secondMap,hessian,sign]

theorem hessian_isSymm (i : Fin 2) : (hessian i).IsSymm := by
  ext j k
  fin_cases j <;> fin_cases k <;> rfl

theorem hessian_charpoly (i : Fin 2) : (hessian i).charpoly=(X-1)*(X-3) := by
  rw [Matrix.charpoly,Matrix.det_fin_two]
  fin_cases i <;> norm_num [Matrix.charmatrix_apply,hessian,sign,Matrix.diagonal_apply,map_ofNat] <;> ring

theorem shifted_determinant (i : Fin 2) (r : ℝ) : (hessian i-r • (1 : Mat 2)).det=(r-1)*(r-3) := by
  rw [Matrix.det_fin_two]
  fin_cases i <;> norm_num [hessian,sign] <;> ring

theorem hessian_eigenvalues (i : Fin 2) (r : ℝ) :
    (∃v : Vec 2,v≠0 ∧ (hessian i).mulVec v=r • v) ↔ r=1 ∨ r=3 := by
  constructor
  · rintro ⟨v,hv,he⟩
    have hz : (hessian i-r • (1 : Mat 2)).mulVec v=0 := by
      rw [Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,he,sub_self]
    have hd : (hessian i-r • (1 : Mat 2)).det=0 := by
      by_contra hd
      exact hv (Matrix.eq_zero_of_mulVec_eq_zero hd hz)
    rw [shifted_determinant] at hd
    rcases mul_eq_zero.mp hd with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · intro h
    rcases h with rfl|rfl
    · refine ⟨![1,-sign i],?_,?_⟩
      · intro he
        have hh := congrFun he 0
        norm_num at hh
      · ext j
        fin_cases i <;> fin_cases j <;> norm_num [hessian,sign,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    · refine ⟨![1,sign i],?_,?_⟩
      · intro he
        have hh := congrFun he 0
        norm_num at hh
      · ext j
        fin_cases i <;> fin_cases j <;> norm_num [hessian,sign,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem branch_strongConvex (i : Fin 2) : FixedNormal.EuclideanStrongConvexOn univ 1 (branch i) := by
  let v : Vec 2 := ![1,sign i]
  have hp : (outer v v).PosSemidef := by
    simpa only [one_smul] using DEmbedding.rankOne_posSemidef (by norm_num : (0 : ℝ)≤1) v
  have hc := (((ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ) : Vec 2 →L[ℝ] ℝ).toLinearMap.convexOn convex_univ).add
    (QuadraticGauge.quadratic_convex (outer v v) hp)
  unfold FixedNormal.EuclideanStrongConvexOn
  convert hc using 1
  funext x
  fin_cases i <;> simp [FixedNormal.EuclideanStrongConvexOn,branch,v,sign,metricEnergy,
    dot,outer,Matrix.mulVec,dotProduct,sqNorm,Fin.sum_univ_two] <;> ring

theorem objective_strongConvex : FixedNormal.EuclideanStrongConvexOn univ 1 objective := by
  have he : (fun x => objective x-(1/2 : ℝ)*sqNorm x)=
      fun x => max (branch 0 x-(1/2 : ℝ)*sqNorm x) (branch 1 x-(1/2 : ℝ)*sqNorm x) := by
    funext x
    rw [objective_eq_max,max_sub_sub_right]
  unfold FixedNormal.EuclideanStrongConvexOn
  norm_num only [one_div]
  rw [he]
  exact (branch_strongConvex 0).sup (branch_strongConvex 1)

end BfgsVerification.AffineRankLoss
