import BfgsVerification.SpatialQuadraticRadial

/-! Exact original-objective contracts for C's three-dimensional warning. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
open SpatialQuadraticWarning TransportedCertificate RadialCertificate

def SpatialCanonicalWarningTarget : Prop :=
  Q.PosDef ∧ ConvexOn ℝ univ objective ∧
  (∀ N : WithTop ℕ∞, ContDiff ℝ N objective) ∧
  (∀ x : Vec 3, HasFDerivAt objective (gradientFunctional (gradient x)) x) ∧
  ∀ ε : ℝ, 0 < ε → ε < 1/10 →
    EligiblePair objective (1/4) (1/2) base (next ε) (gradient base) (gradient (next ε)) ∧
    pairDecrease base (next ε) (gradient base) = ε^2 ∧
    pairCurvature base (next ε) (gradient base) (gradient (next ε)) = ε^2*(ε^2+2*ε+4)/3 ∧
    (tripleColumns (gradient base) (step ε) (change ε)).det = (4/3 : ℝ)*ε^2*(1+ε) ∧
    (∃ H : Mat 3, H.PosDef ∧ bfgsStep H (gradient base) 1 = step ε ∧
      metricEnergy H (gradient base) = ε^2) ∧
    (∀ N : WithTop ℕ∞, ContDiffAt ℝ N canonicalField base ∧
      ContDiffAt ℝ N canonicalField (next ε)) ∧
    (dot (gradient base) (canonicalField base) = 1 ∧
      dot (gradient (next ε)) (canonicalField (next ε)) = 1) ∧
    canonicalField (next ε) ∉ Submodule.span ℝ ({canonicalField base,step ε} : Set (Vec 3)) ∧
    (∀ a : ℝ, ¬(a • (stepProjector (step ε) * outer (canonicalField base) (canonicalField base) *
        stepProjector (step ε)) -
      stepProjector (step ε) * outer (canonicalField (next ε)) (canonicalField (next ε)) *
        stepProjector (step ε)).PosSemidef)

theorem spatialCanonicalWarning : SpatialCanonicalWarningTarget := by
  refine ⟨Q_posDef,objective_convex,fun _ => objective_contDiff,objective_hasGradient,?_⟩
  intro ε hε hsmall
  exact ⟨actual_pair_eligible hε hsmall,pair_decrease ε,pair_curvature ε,printed_determinant ε,
    actual_pair_realizable hε hsmall,fun _ => canonicalField_smooth_at_pair ε,
    canonicalField_equal_rate_at_pair ε,canonicalField_not_in_span hε,
    canonicalField_projected_transport_fails hε⟩

def SpatialQuadraticRadialTarget : Prop :=
  (∀ x : Vec 3, dot (gradient x) x = 2*objective x) ∧
  (∀ ε : ℝ, next ε = base+step ε) ∧
  (∀ b : ℝ, HasRadialSecantBounds objective {x | objective x ≤ b} 0) ∧
  ∀ R : AdmissibleBFGSRun 3 objective,
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)

theorem spatialQuadraticRadial : SpatialQuadraticRadialTarget :=
  ⟨radial_field_pairing,radial_field_exact_transport,actual_radial_certificate,actual_fullBFGS_convergence⟩

end BfgsVerification
