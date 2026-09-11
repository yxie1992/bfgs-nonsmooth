import BfgsVerification.LStepEmbeddingCopies
import BfgsVerification.LStepEmbeddingEnvelope

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification

def LStepEmbeddingGeometryTarget : Prop :=
  (∀ x : Vec 2, LStepEmbedding.objective x=
    Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => LStepEmbedding.branch i x)) ∧
  (∀ i, ConvexOn ℝ univ (LStepEmbedding.branch i) ∧
    FixedNormal.EuclideanStrongConvexOn univ LEmbedding.mu (LStepEmbedding.branch i)) ∧
  ConvexOn ℝ univ LStepEmbedding.objective ∧
  FixedNormal.EuclideanStrongConvexOn univ LEmbedding.mu LStepEmbedding.objective ∧
  (∀ x, LEmbedding.mu/2*sqNorm x≤LStepEmbedding.objective x) ∧
  LStepEmbedding.objective 0=0 ∧
  (∀ x, LStepEmbedding.objective x=0 → x=0) ∧
  (∀ a, IsCompact {x | LStepEmbedding.objective x≤a}) ∧
  ¬DifferentiableAt ℝ LStepEmbedding.objective (0 : Vec 2)

theorem lStepEmbeddingGeometry : LStepEmbeddingGeometryTarget :=
  ⟨LStepEmbedding.objective_eq_max,fun i => ⟨LStepEmbedding.branch_convex i,LStepEmbedding.branch_strongConvex i⟩,
    LStepEmbedding.objective_convex,LStepEmbedding.objective_strongConvex,LStepEmbedding.objective_lower,
    LStepEmbedding.objective_zero,fun _ hx => LStepEmbedding.objective_unique_zero hx,
    LStepEmbedding.objective_sublevels_compact,LStepEmbedding.objective_not_differentiable_zero⟩

def LStepEmbeddingPolyhedralTarget : Prop :=
  Countable LStepEmbedding.CountableIndex ∧
  (∀ x : Vec 2, IsGreatest (range (fun j : LStepEmbedding.CountableIndex =>
    LStepEmbedding.countableLinear j x+LStepEmbedding.countableOffset j)) (LStepEmbedding.residual x)) ∧
  (∀ x : Vec 2, x≠0 → FiniteAffineLocal.PolyhedralGerm LStepEmbedding.residual x) ∧
  ∀ x : Vec 2, DifferentiableAt ℝ LStepEmbedding.objective x →
    FiniteAffineLocal.AffineGerm LStepEmbedding.residual x ∧
    HasFDerivAt (fderiv ℝ LStepEmbedding.objective) (LEmbedding.mu • LQuadraticSeed.pairingMap) x ∧
    RadialHessian.matrix LStepEmbedding.objective x=LEmbedding.mu • (1 : Mat 2)

theorem lStepEmbeddingPolyhedral : LStepEmbeddingPolyhedralTarget := by
  refine ⟨LStepEmbedding.countable_index,LStepEmbedding.residual_countable_max,fun _ hx => LStepEmbedding.residual_polyhedral_of_ne_zero hx,?_⟩
  intro x hd
  exact ⟨LStepEmbedding.residual_affine_at_differentiable hd,LStepEmbedding.objective_actual_hessian hd⟩

def LStepEmbeddingCopiesTarget : Prop :=
  IsOpen LStepEmbedding.copyNeighborhood ∧ (0 : Vec 2) ∈ LStepEmbedding.copyNeighborhood ∧
  0<LStepEmbedding.copyConstant ∧
  ∀ n : ℕ,
    (∀ y∈LStepEmbedding.copyNeighborhood, LStepEmbedding.objective (LStepEmbedding.copyPoint n y)=
      (LScalarGeometric.scale n)^2*(LStepEmbedding.copyConstant+LQuadraticSeed.objective LEmbedding.mu y)) ∧
    (∀ y∈LStepEmbedding.copyNeighborhood,
      LStepEmbedding.branch 3 (LStepEmbedding.copyPoint n y)<LStepEmbedding.branch 0 (LStepEmbedding.copyPoint n y)) ∧
    LStepEmbedding.objective (LStepEmbedding.copyPoint n 0)=(LScalarGeometric.scale n)^2*LStepEmbedding.copyConstant ∧
    0<LStepEmbedding.objective (LStepEmbedding.copyPoint n 0) ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential LStepEmbedding.objective (LStepEmbedding.copyPoint n 0)

theorem lStepEmbeddingCopies : LStepEmbeddingCopiesTarget := by
  refine ⟨LStepEmbedding.copyNeighborhood_open,LStepEmbedding.copyNeighborhood_zero,LStepEmbedding.copyConstant_positive,?_⟩
  intro n
  exact ⟨fun _ hy => LStepEmbedding.objective_copy n hy,fun _ hy => LStepEmbedding.fourth_lt_first_copy n hy,
    LStepEmbedding.objective_copy_center n,LStepEmbedding.objective_copy_center_positive n,
    LStepEmbedding.copy_center_nonstationary n⟩

end BfgsVerification
