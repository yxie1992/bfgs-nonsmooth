import BfgsVerification.NormalSpikeSeparation
import BfgsVerification.NormalSpikeInterface
import BfgsVerification.NormalSpikeHessian

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

def SpikeObjectiveConvergenceTarget : Prop :=
  ∀ n : ℕ, ∀ R : AdmissibleBFGSRun (n+2) (objective (normal n)),
    Tendsto (fun k => objective (normal n) (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)

theorem spikeObjectiveConvergence : SpikeObjectiveConvergenceTarget :=
  fun n R => objective_fullBFGS_convergence (normal n) (normal_unit n) R

def SpikeRadialSeparationTarget : Prop :=
  ∀ n : ℕ, ∀ K : Set (Vec (n+2)), K ∈ 𝓝 0 →
    ¬ HasRadialSecantBounds (objective (normal n)) K 0

theorem spikeRadialSeparation : SpikeRadialSeparationTarget :=
  fun n _ hK => not_radial_secant_neighborhood n hK

def SpikeObjectiveGeometryTarget : Prop :=
  ∀ n : ℕ,
    ConvexOn ℝ univ (objective (normal n)) ∧
    EuclideanStrongConvexOn univ 1 (objective (normal n)) ∧
    Tendsto (objective (normal n)) (cocompact (Vec (n+2))) atTop ∧
    objective (normal n) 0 = 0 ∧
    (∀ x, objective (normal n) 0 ≤ objective (normal n) x ∧
      (objective (normal n) x = objective (normal n) 0 → x = 0) ∧
      (DifferentiableAt ℝ (objective (normal n)) x ↔ x 0 ≠ 0)) ∧
    (∀ x g, Homogeneous.Supports (objective (normal n)) x g →
      tangentProjection (normal n) g = tangentProjection (normal n) x) ∧
    LipschitzWith 1 (tangentProjection (normal n)) ∧
    (∀ v : ℝ, ∀ u : Vec (n+1), objective (normal n) (Fin.cons v u) =
      (1/2 : ℝ)*sqNorm u+(1/2 : ℝ)*v^2+|v|+sourcePrimitive v)

theorem spikeObjectiveGeometry : SpikeObjectiveGeometryTarget := by
  intro n
  refine ⟨objective_convex (normal n), objective_strongConvex (normal n), objective_coercive (normal n),
    objective_zero (normal n), ?_, objective_support_tangent (normal n) (normal_unit n),
    normal_tangent_lipschitz n, printed_objective_split n⟩
  intro x
  refine ⟨objective_minimum (normal n) x, objective_unique_minimum (normal n) x, ?_⟩
  simpa only [normal_coordinate] using objective_differentiable_iff (normal n) (normal_unit n) x

def SpikeHessianPeakTarget : Prop :=
  ∀ n : ℕ, ∀ u : ℝ,
    (∀ N : ℕ, dot (sample n u (scale N))
      ((RadialHessian.matrix (objective (normal n)) (sample n u (scale N))).mulVec (sample n u (scale N))) =
        u^2+(scale N)^2+(scale N)⁻¹) ∧
    Tendsto (fun N => dot (sample n u (scale N))
      ((RadialHessian.matrix (objective (normal n)) (sample n u (scale N))).mulVec (sample n u (scale N))))
      atTop atTop ∧
    Tendsto (fun N => objective (normal n) (sample n u (scale N))) atTop (𝓝 ((1/2 : ℝ)*u^2))

theorem spikeHessianPeaks : SpikeHessianPeakTarget := by
  intro n u
  refine ⟨printed_radial_hessian_peak n u, ?_, sample_objective_limit n u⟩
  simpa only [printed_radial_hessian_peak, sample_radial_curvature_peak] using sample_radial_curvature_unbounded n u

end BfgsVerification.NormalSpike
