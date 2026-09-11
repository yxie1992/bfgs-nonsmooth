import BfgsVerification.LEmbeddingGeometry

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.LEmbedding

/-- Literal four globally C1,1 branches with the source Euclidean constants. -/
def RegularityTarget : Prop :=
  mu=(1/4096 : ℝ) ∧ (∀i : Fin 3,17/10<parameter i ∧ parameter i<34) ∧
    (∀i : Fin 4,ContDiff ℝ 1 (branch i) ∧ FixedNormal.EuclideanStrongConvexOn univ mu (branch i) ∧
      (∀x,HasFDerivAt (branch i) (gradientFunctional (branchGradient i x)) x) ∧
      ∀x y,sqNorm (branchGradient i x-branchGradient i y)≤512^2*sqNorm (x-y)) ∧
    (∀x,objective x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch i x)) ∧
    FixedNormal.EuclideanStrongConvexOn univ mu objective ∧
    ∀i : Fin 3,gradientBound i < ![439,446,27] i

theorem regularity : RegularityTarget :=
  ⟨rfl,parameter_bounds,fun i => ⟨branch_contDiff i,branch_strongConvex i,branch_hasGradient i,
    branch_gradient_bound i⟩,objective_eq_max,objective_strongConvex,gradientBound_source⟩

def OriginTarget : Prop :=
  ConvexOn ℝ univ objective ∧ objective 0=0 ∧
    (∀x,mu/2*sqNorm x≤objective x) ∧ (∀x,objective x=0→x=0) ∧
    (∀a,IsCompact {x | objective x≤a}) ∧ ¬DifferentiableAt ℝ objective (0 : Vec 2) ∧
    ∀h : Vec 2,Tendsto (fun t : ℝ => (objective (t • h)-objective 0)/t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1)))

theorem origin : OriginTarget :=
  ⟨objective_convex,objective_zero,objective_lower,fun _ => objective_unique_zero,
    objective_sublevels_compact,objective_not_differentiable_zero,objective_directional_derivative_zero⟩

/-- Both derivatives are actual derivatives: the first exists nearby and its
field has a derivative at x. No global smoothness of the maximum is asserted. -/
def HessianTarget : Prop :=
  (∀x : Vec 2,(∀ᶠ z in 𝓝 x,DifferentiableAt ℝ objective z) →
    DifferentiableAt ℝ (fderiv ℝ objective) x →
    (RadialHessian.matrix objective x).IsSymm ∧ ∀v,
      mu*sqNorm v≤dot v ((RadialHessian.matrix objective x).mulVec v) ∧
      dot v ((RadialHessian.matrix objective x).mulVec v)≤512*sqNorm v) ∧
  (∀x g : Vec 2,HasFDerivAt objective (gradientFunctional g) x →
    ∀ᶠ z in 𝓝 x,objective z≤objective x+dot g (z-x)+256*sqNorm (z-x)) ∧
  ∀i : Fin 3,∀x : Vec 2,DifferentiableAt ℝ (fderiv ℝ (branch i.castSucc)) x →
    (RadialHessian.matrix (branch i.castSucc) x).IsSymm ∧ ∀v,
      mu*sqNorm v≤dot v ((RadialHessian.matrix (branch i.castSucc) x).mulVec v) ∧
      dot v ((RadialHessian.matrix (branch i.castSucc) x).mulVec v)≤gradientBound i*sqNorm v

theorem hessian : HessianTarget :=
  ⟨fun _ => actual_hessian_bounds,fun _ _ => local_upper_taylor,fun i _ => branch_old_actual_hessian_bounds i⟩

/-- Exact scaled copies on one fixed open neighborhood, independent of scale.
Existence of an actual bad orbit contained there is a separate dynamics result. -/
def LocalModelTarget : Prop :=
  IsOpen localDomain ∧ (0 : Vec 2)∈localDomain ∧ 0<offset ∧
    (∀n : ℕ,∀y∈localDomain,objective (copyPoint n y)=
      (LScalarGeometric.scale n)^2*(offset+LQuadraticSeed.objective mu y)) ∧
    (∀n : ℕ,objective (copyCenter n)=(LScalarGeometric.scale n)^2*offset ∧
      0<objective (copyCenter n) ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential objective (copyCenter n)) ∧
    Tendsto copyCenter atTop (𝓝 (0 : Vec 2)) ∧
    ∀y : Vec 2,Tendsto (fun n => copyPoint n y) atTop (𝓝 (0 : Vec 2))

theorem localModel : LocalModelTarget :=
  ⟨localDomain_open,zero_mem_localDomain,offset_pos,fun n _ => local_model n,
    fun n => ⟨center_value n,center_value_pos n,center_nonstationary n⟩,
    copyCenter_tendsto,copyPoint_tendsto⟩

end BfgsVerification.LEmbedding
