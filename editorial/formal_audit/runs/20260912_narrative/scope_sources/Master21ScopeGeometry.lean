import BfgsVerification.PlanarPrincipalEndToEnd
import BfgsVerification.SemialgebraicCriticalTargets
import BfgsVerification.AffineCriticalSemialgebraicPathComponents
import Lean

/-! Independent claim audit, not a new algorithm or a main-library change.
The raw contracts below expand actual supports, semialgebraicity and every
run field. They are compiled against the existing main proofs. -/
noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology ContDiff
open BfgsVerification BfgsVerification.AffineCriticalObjective
  BfgsVerification.ConvexSubdifferential BfgsVerification.RealAlgebraicGeometry
  BfgsVerification.PlanarCornerCharts BfgsVerification.HomogeneousPlanar

namespace GeometryClaimReview20

def rawCritical {n : ℕ} (F : Vec n → ℝ) (p : Vec n) : Prop :=
  (0 : Vec n) ∈ affineSpan ℝ {g : Vec n | ∀ z, dot g (z-p) ≤ F z-F p}

theorem rawCritical_iff {n : ℕ} (F : Vec n → ℝ) (p : Vec n) :
    rawCritical F p ↔ IsAffineCritical F p := by
  exact (isAffineCritical_iff_coordinate_affineSpan F p).symm

/-- Raw graph definability is only a finite Boolean polynomial formula. -/
theorem raw_A_finite_values_and_gap {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F)
    (hSA : ∃ φ : PolynomialFormula (Option (Fin n)), ∀ v,
      v none = F (fun i => v (some i)) ↔ φ.Holds v) :
    (F '' {p | (0 : Vec n) ∈ affineSpan ℝ
      {g : Vec n | ∀ z, dot g (z-p) ≤ F z-F p}}).Finite ∧
    ∀ star : Vec n, (∀ z, F star ≤ F z) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ p, F p < F star+ε →
        (0 : Vec n) ∈ affineSpan ℝ {g : Vec n | ∀ z, dot g (z-p) ≤ F z-F p} →
        ∀ z, F p ≤ F z := by
  have hs : IsSemialgebraicObjective F := hSA
  have he : {p | rawCritical F p} = {p | IsAffineCritical F p} := by
    ext p
    exact rawCritical_iff F p
  constructor
  · change (F '' {p | rawCritical F p}).Finite
    rw [he]
    exact semialgebraic_affine_critical_values hF hs
  · intro star hmin
    obtain ⟨ε,hε,hgap⟩ := semialgebraic_low_affine_critical_gap hF hs star hmin
    refine ⟨ε,hε,fun p hp hc => ?_⟩
    exact zero_mem_iff_global_minimum.mp (hgap p hp ((rawCritical_iff F p).mp hc))

/-- The finite cover has actual curves and actual finite exceptional sets;
neither the cover nor connectivity is assumed by this adapter. -/
theorem raw_semialgebraic_finite_path_cover {n : ℕ} (S : Set (Vec n))
    (hS : ∃ φ : PolynomialFormula (Fin n), ∀ x, x∈S ↔ φ.Holds x) :
    ∃ C : Finset (Set (Vec n)), (⋃ T∈C, T)=S ∧
      ∀ T∈C, IsSemialgebraic T ∧ ∀ x∈T, ∀ y∈T,
        ∃ p : ℝ → Vec n, ContinuousOn p (Icc 0 1) ∧ p 0=x ∧ p 1=y ∧
          (∀ t∈Icc (0:ℝ) 1, p t∈T) ∧ ∃ E : Finset ℝ,
            ∀ t∈Ioo (0:ℝ) 1, t∉E → ContDiffAt ℝ ∞ p t := by
  obtain ⟨C,hC,hcover⟩ := semialgebraic_finite_smooth_cover hS
  refine ⟨C,hcover,fun T hT => ⟨(hC T hT).1,?_⟩⟩
  intro x hx y hy
  obtain ⟨p⟩ := (hC T hT).2 x hx y hy
  exact ⟨p.curve,p.continuousOn,p.source,p.target,p.mapsTo,p.exceptions,p.smoothAt⟩

/-- A's regularity statement is about the identical input curve and identical
objective composition. No derivative, smooth-piece or graph-lift assumption is
silently supplied for either of them. Endpoints are continuous, not required
to admit an ambient smooth extension. -/
theorem raw_A_path_and_composition {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F)
    (hSA : ∃ φ : PolynomialFormula (Option (Fin n)), ∀ v,
      v none=F (fun i => v (some i)) ↔ φ.Holds v)
    (p : ℝ → Vec n) (hc : ContinuousOn p (Icc 0 1))
    (hp : ∃ ψ : PolynomialFormula (Option (Fin n)), ∀ v,
      (v none∈Icc (0:ℝ) 1 ∧ (fun i => v (some i))=p (v none)) ↔ ψ.Holds v) :
    ContinuousOn (F ∘ p) (Icc 0 1) ∧ ∃ E : Finset ℝ,
      ∀ t∈Ioo (0:ℝ) 1, t∉E → ContDiffAt ℝ ∞ p t ∧ ContDiffAt ℝ ∞ (F ∘ p) t := by
  classical
  obtain ⟨E,hE⟩ := semialgebraic_curve_smooth_except_finite hp
  obtain ⟨_,hcont,D,hD⟩ := convex_semialgebraic_objective_curve_piecewise_smooth hF hSA hc hp
  refine ⟨hcont,E ∪ D,?_⟩
  intro t ht he
  have hn := Finset.not_mem_union.mp he
  exact ⟨hE t ⟨ht.1.le,ht.2.le⟩ hn.1,hD t ht hn.2⟩

/-- Every source run assumption is displayed separately, including the full
inverse update. There is no accepted-run record premise, no all-k SPD premise,
and no convergence, summability, bounded-gradient, or field premise. -/
theorem raw_C_cluster_and_convergence
    (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F)
    (x : ℕ → Vec 2) (H : ℕ → Mat 2) (g : ℕ → Vec 2) (α : ℕ → ℝ)
    (c₁ c₂ : ℝ) (hc₁ : 0<c₁) (hc₁₂ : c₁<c₂) (hc₂ : c₂<1)
    (hH : (H 0).PosDef) (hα : ∀ k, 0<α k) (hg : ∀ k, g k≠0)
    (hgrad : ∀ k, HasFDerivAt F
      (∑ i : Fin 2, g k i • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) (x k))
    (hstep : ∀ k, x (k+1)=x k+(-α k) • (H k).mulVec (g k))
    (hupdate : ∀ k,
      let s := (-α k) • (H k).mulVec (g k)
      let y := g (k+1)-g k
      let t := dot y s
      H (k+1) = ((1 : Mat 2)-(t⁻¹ • Matrix.of (fun i j => s i*y j) : Mat 2)) * H k *
        ((1 : Mat 2)-(t⁻¹ • Matrix.of (fun i j => y i*s j) : Mat 2)) +
          (t⁻¹ • Matrix.of (fun i j => s i*s j) : Mat 2))
    (harmijo : ∀ k, F (x (k+1)) ≤ F (x k)+c₁*dot (g k) ((-α k) • (H k).mulVec (g k)))
    (hwolfe : ∀ k, c₂*dot (g k) ((-α k) • (H k).mulVec (g k)) ≤
      dot (g (k+1)) ((-α k) • (H k).mulVec (g k)))
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {z : Vec 2 | F z≤b}) (hstart : F (x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b → ∀ u v : Vec 2,
      segment ℝ u v ⊆ frontier {w | F w≤ℓ} → u=v)
    (hregular : ∀ p : Vec 2, F p≤b →
      ¬((0 : Vec 2) ∈ affineSpan ℝ {v : Vec 2 | ∀ z, dot v (z-p)≤F z-F p}) →
      ContDiffAt ℝ 2 F p ∨
        ∃ f : Fin 2 → Vec 2 → ℝ, ∃ U : Set (Vec 2), IsOpen U ∧ p∈U ∧
          (∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U) ∧
          (∀ z∈U, IsGreatest (range (fun i => f i z)) (F z)) ∧
          (∀ i, f i p=F p) ∧
          pairDet (coordinateGradient (f 0) p) (coordinateGradient (f 1) p) ≠ 0) :
    (∃ p : Vec 2, MapClusterPt p atTop x ∧ F p≤b ∧
      (0 : Vec 2) ∈ affineSpan ℝ {v : Vec 2 | ∀ z, dot v (z-p)≤F z-F p}) ∧
    ((∀ p : Vec 2, F p≤b →
      (0 : Vec 2) ∈ affineSpan ℝ {v : Vec 2 | ∀ z, dot v (z-p)≤F z-F p} →
      ∀ z, F p≤F z) →
      Tendsto (fun k => F (x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (euclideanVector (x k))
        (euclideanVector '' {z | ∀ w, F z≤F w})) atTop (𝓝 0) ∧
      ((∀ z, F z=F star → z=star) → Tendsto x atTop (𝓝 star))) := by
  let R : AdmissibleBFGSRun 2 F := {
    convex := hF, x := x, H := H, g := g, α := α, c₁ := c₁, c₂ := c₂
    c₁_pos := hc₁, c₁_lt_c₂ := hc₁₂, c₂_lt_one := hc₂
    initial_posDef := hH, alpha_pos := hα, gradient_nonzero := hg
    hasGradient := by simpa only [gradientFunctional] using hgrad
    step := hstep, update := hupdate
    armijo := harmijo, weak_wolfe := hwolfe }
  have hr : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p := by
    intro p hp hn
    exact hregular p hp (fun hc => hn ((rawCritical_iff F p).mp hc))
  constructor
  · obtain ⟨p,hp,hpb,hpc⟩ := planarAffineCriticalCluster R star hmin b hK hstart hstrict hr
    exact ⟨p,hp,hpb,(rawCritical_iff F p).mpr hpc⟩
  · intro hcorrect
    have hc : ∀ p : Vec 2, F p≤b → AffineCorrectAt F p := by
      intro p hp ha
      exact zero_mem_iff_global_minimum.mpr
        (hcorrect p hp ((rawCritical_iff F p).mpr ha))
    have hv := planarConvergence R star hmin b hK hstart hstrict hr hc
    exact ⟨hv.1,hv.2.2.1,hv.2.2.2⟩

/-- A separately written full signature for the central C cluster target. -/
def ExpectedCentralC : Prop := ∀ {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {x : Vec 2 | F x≤b}) (hstart : F (R.x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p),
    ∃ p : Vec 2, MapClusterPt p atTop R.x ∧ F p≤b ∧ IsAffineCritical F p

def ExpectedCentralAValues : Prop := ∀ {n : ℕ} {F : Vec n → ℝ},
  ConvexOn ℝ univ F → IsSemialgebraicObjective F → (F '' {p | IsAffineCritical F p}).Finite

def ExpectedCentralAGap : Prop := ∀ {n : ℕ} {F : Vec n → ℝ},
  ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    ∀ star : Vec n, (∀ z, F star≤F z) →
      ∃ ε : ℝ, 0<ε ∧ ∀ p, F p<F star+ε → IsAffineCritical F p →
        ∀ z, dot (0 : Vec n) (z-p)≤F z-F p

def ExpectedCentralCConvergence : Prop := ∀ {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {x : Vec 2 | F x≤b}) (hstart : F (R.x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p)
    (hcorrect : ∀ p : Vec 2, F p≤b → IsAffineCritical F p →
      ∀ z, dot (0 : Vec 2) (z-p)≤F z-F p),
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
    Tendsto (fun k => Metric.infDist (R.x k) {z | ∀ w, F z≤F w}) atTop (𝓝 0) ∧
    Tendsto (fun k => Metric.infDist (euclideanVector (R.x k))
      (euclideanVector '' {z | ∀ w, F z≤F w})) atTop (𝓝 0) ∧
    ((∀ z, F z=F star → z=star) → Tendsto R.x atTop (𝓝 star))

open Lean Elab Command Meta in
run_elab do
  for (actual, expected) in [
      (`BfgsVerification.planarAffineCriticalCluster, `GeometryClaimReview20.ExpectedCentralC),
      (`BfgsVerification.PlanarAffineCriticalClusterTarget, `GeometryClaimReview20.ExpectedCentralC),
      (`BfgsVerification.RealAlgebraicGeometry.semialgebraic_affine_critical_values,
        `GeometryClaimReview20.ExpectedCentralAValues),
      (`BfgsVerification.RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap,
        `GeometryClaimReview20.ExpectedCentralAGap),
      (`BfgsVerification.planarConvergence, `GeometryClaimReview20.ExpectedCentralCConvergence),
      (`BfgsVerification.PlanarConvergenceTarget, `GeometryClaimReview20.ExpectedCentralCConvergence)] do
    let info ← getConstInfo actual
    let lhs := if info.isTheorem then info.type else mkConst actual
    unless ← isDefEq lhs (mkConst expected) do
      throwError "Expanded source contract mismatch: {actual}"
    logInfo m!"GEOMETRY20_STRICT_OK {actual} {expected}"

end GeometryClaimReview20

/- Ordinary Lean axiom collector; no cached collector and no external answers. -/
#check @GeometryClaimReview20.rawCritical
#print axioms GeometryClaimReview20.rawCritical
#check @GeometryClaimReview20.rawCritical_iff
#print axioms GeometryClaimReview20.rawCritical_iff
#check @GeometryClaimReview20.raw_A_finite_values_and_gap
#print axioms GeometryClaimReview20.raw_A_finite_values_and_gap
#check @GeometryClaimReview20.raw_semialgebraic_finite_path_cover
#print axioms GeometryClaimReview20.raw_semialgebraic_finite_path_cover
#check @GeometryClaimReview20.raw_A_path_and_composition
#print axioms GeometryClaimReview20.raw_A_path_and_composition
#check @GeometryClaimReview20.raw_C_cluster_and_convergence
#print axioms GeometryClaimReview20.raw_C_cluster_and_convergence
#check @GeometryClaimReview20.ExpectedCentralC
#print axioms GeometryClaimReview20.ExpectedCentralC
#check @GeometryClaimReview20.ExpectedCentralAValues
#print axioms GeometryClaimReview20.ExpectedCentralAValues
#check @GeometryClaimReview20.ExpectedCentralAGap
#print axioms GeometryClaimReview20.ExpectedCentralAGap
#check @GeometryClaimReview20.ExpectedCentralCConvergence
#print axioms GeometryClaimReview20.ExpectedCentralCConvergence
#check @BfgsVerification.AdmissibleBFGSRun
#print axioms BfgsVerification.AdmissibleBFGSRun
#check @BfgsVerification.fullBFGS_positive_invariants
#print axioms BfgsVerification.fullBFGS_positive_invariants
#check @BfgsVerification.AffineCriticalObjective.IsAffineCritical
#print axioms BfgsVerification.AffineCriticalObjective.IsAffineCritical
#check @BfgsVerification.RealAlgebraicGeometry.IsSemialgebraicObjective
#print axioms BfgsVerification.RealAlgebraicGeometry.IsSemialgebraicObjective
#check @BfgsVerification.RealAlgebraicGeometry.coordinate_projection_semialgebraic
#print axioms BfgsVerification.RealAlgebraicGeometry.coordinate_projection_semialgebraic
#check @BfgsVerification.AffineSupportPath.isAffineCritical_iff_bounded_supports
#print axioms BfgsVerification.AffineSupportPath.isAffineCritical_iff_bounded_supports
#check @BfgsVerification.RealAlgebraicGeometry.supportGraph_semialgebraic
#print axioms BfgsVerification.RealAlgebraicGeometry.supportGraph_semialgebraic
#check @BfgsVerification.RealAlgebraicGeometry.affineCriticalGraph_semialgebraic
#print axioms BfgsVerification.RealAlgebraicGeometry.affineCriticalGraph_semialgebraic
#check @BfgsVerification.RealAlgebraicGeometry.semialgebraic_finite_smooth_cover
#print axioms BfgsVerification.RealAlgebraicGeometry.semialgebraic_finite_smooth_cover
#check @BfgsVerification.RealAlgebraicGeometry.finite_critical_values_of_smooth_graph_cover
#print axioms BfgsVerification.RealAlgebraicGeometry.finite_critical_values_of_smooth_graph_cover
#check @BfgsVerification.RealAlgebraicGeometry.affineCriticalGraph_path_project
#print axioms BfgsVerification.RealAlgebraicGeometry.affineCriticalGraph_path_project
#check @BfgsVerification.AffineSupportPath.supporting_path_derivative_eq
#print axioms BfgsVerification.AffineSupportPath.supporting_path_derivative_eq
#check @BfgsVerification.AffineSupportPath.objective_constant_on_piecewise_differentiable_path
#print axioms BfgsVerification.AffineSupportPath.objective_constant_on_piecewise_differentiable_path
#check @BfgsVerification.RealAlgebraicGeometry.semialgebraic_affine_critical_values
#print axioms BfgsVerification.RealAlgebraicGeometry.semialgebraic_affine_critical_values
#check @BfgsVerification.RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap
#print axioms BfgsVerification.RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap
#check @BfgsVerification.RealAlgebraicGeometry.continuous_semialgebraic_path_iff_piecewise_smooth
#print axioms BfgsVerification.RealAlgebraicGeometry.continuous_semialgebraic_path_iff_piecewise_smooth
#check @BfgsVerification.RealAlgebraicGeometry.affine_critical_continuous_semialgebraic_components
#print axioms BfgsVerification.RealAlgebraicGeometry.affine_critical_continuous_semialgebraic_components
#check @BfgsVerification.RealAlgebraicGeometry.convex_semialgebraic_objective_curve_piecewise_smooth
#print axioms BfgsVerification.RealAlgebraicGeometry.convex_semialgebraic_objective_curve_piecewise_smooth
#check @BfgsVerification.AdmissibleBFGSRun.positive_limit_of_no_affineCritical_cluster
#print axioms BfgsVerification.AdmissibleBFGSRun.positive_limit_of_no_affineCritical_cluster
#check @BfgsVerification.AdmissibleBFGSRun.steps_tendsto_zero_of_strict_contour
#print axioms BfgsVerification.AdmissibleBFGSRun.steps_tendsto_zero_of_strict_contour
#check @BfgsVerification.PlanarObjectiveField.exists_secant_structured_visible_field
#print axioms BfgsVerification.PlanarObjectiveField.exists_secant_structured_visible_field
#check @BfgsVerification.AdmissibleBFGSRun.scalar_log_transport_tail_incompatible
#print axioms BfgsVerification.AdmissibleBFGSRun.scalar_log_transport_tail_incompatible
#check @BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster
#print axioms BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster
#check @BfgsVerification.planarAffineCriticalCluster
#print axioms BfgsVerification.planarAffineCriticalCluster
#check @BfgsVerification.planarConvergence
#print axioms BfgsVerification.planarConvergence
#check @BfgsVerification.RealAlgebraicGeometry.semialgebraic_planar_low_basin
#print axioms BfgsVerification.RealAlgebraicGeometry.semialgebraic_planar_low_basin
