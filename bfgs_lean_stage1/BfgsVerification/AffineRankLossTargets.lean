import BfgsVerification.AffineRankLossHessian

noncomputable section
open Set Matrix
namespace BfgsVerification.AffineRankLoss

/-- Module A's literal two-quadratic rank-loss objective, with actual
second derivative matrices and exact eigenvalues, and modulus one. -/
def RankLossCurvatureTarget : Prop :=
  (∀i : Fin 2,ContDiff ℝ ⊤ (branch i) ∧
    FixedNormal.EuclideanStrongConvexOn univ 1 (branch i) ∧
    (∀x,RadialHessian.matrix (branch i) x=hessian i) ∧
    (hessian i).IsSymm ∧
    (∀r : ℝ,(∃v : Vec 2,v≠0 ∧ (hessian i).mulVec v=r • v) ↔ r=1 ∨ r=3)) ∧
    FixedNormal.EuclideanStrongConvexOn univ 1 objective

theorem rankLossCurvature : RankLossCurvatureTarget :=
  ⟨fun i => ⟨branch_contDiff i,branch_strongConvex i,branch_hessian i,hessian_isSymm i,
    hessian_eigenvalues i⟩,objective_strongConvex⟩

end BfgsVerification.AffineRankLoss
