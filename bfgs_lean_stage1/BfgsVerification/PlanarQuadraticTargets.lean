import BfgsVerification.PlanarQuadraticSeparation

/-! Exact source contracts for C's explicit three-quadratic example. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
open PlanarQuadraticExample FixedNormal TransportedCertificate RadialCertificate

def PlanarQuadraticModelTarget : Prop :=
  ConvexOn ℝ univ objective ∧ EuclideanStrongConvexOn univ 1 objective ∧
  objective 0=0 ∧ (∀ x : Vec 2, sqNorm x≤objective x) ∧
  (∀ x : Vec 2, objective x=0 → x=0) ∧
  (∀ x : Vec 2, (∑ i : Fin 3, branch i x)/3=sqNorm x) ∧
  (∀ i : Fin 3, ∀ x : Vec 2,
    HasFDerivAt (branch i) (gradientFunctional (gradient i x)) x ∧
    RadialHessian.matrix (branch i) x=hessian i ∧
    (RadialHessian.matrix (branch i) x-1).PosSemidef ∧
    ((3 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch i) x).PosSemidef)

theorem planarQuadraticModel : PlanarQuadraticModelTarget := by
  refine ⟨objective_convex,objective_strongConvex,objective_zero,objective_lower,
    objective_unique_zero,branch_average,?_⟩
  intro i x
  exact ⟨branch_hasGradient i x,branch_actual_hessian i x,branch_actual_hessian_bounds i x⟩

def PlanarQuadraticCoefficientsTarget : Prop := ∀ x : Vec 2, |x 0|≤1/10 → |x 1|≤1/10 →
  267/100≤denominator x ∧ 23/100≤numerator x 0 ∧
    49/100≤numerator x 1 ∧ 45/100≤numerator x 2 ∧
  (∀ i : Fin 3, 0<coefficients x i) ∧ (∑ i : Fin 3, coefficients x i)=1 ∧
  (∑ i : Fin 3, coefficients x i • gradient i x)=0 ∧
  AffineIndependent ℝ (fun i : Fin 3 => gradient i x) ∧
  AffineCriticalObjective.AffineCorrectAt objective x ∧
  (∀ w : Vec 3, (∑ i, w i)=1 → (∑ i, w i • gradient i x)=0 → w=coefficients x)

theorem planarQuadraticCoefficients : PlanarQuadraticCoefficientsTarget := by
  intro x hx hy
  have hb : x∈box := ⟨hx,hy⟩
  have hD := (denominator_pos_on_box hb).ne'
  have h := coefficient_box_bounds hb
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,coefficients_pos_on_box hb,coefficients_sum hD,
    coefficients_zero hD,gradient_affineIndependent hD,affineCorrect_on_box hb,
    fun w hs hw => coefficients_unique hD w hs hw⟩

def PlanarQuadraticBasinTarget : Prop := ∀ R : AdmissibleBFGSRun 2 objective,
  objective (R.x 0)<1/100 →
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)

theorem planarQuadraticBasin : PlanarQuadraticBasinTarget := fullBFGS_explicit_basin

def PlanarQuadraticCurveTarget : Prop :=
  (fun u : ℝ => tieHeight u-u+u^2/2) =O[𝓝[>] 0] (fun u : ℝ => u^3) ∧
  ∀ u : ℝ, 0<u → u<1/10 →
    branch 0 (base u)=objective (base u) ∧ branch 1 (base u)=objective (base u) ∧
    branch 2 (base u)<objective (base u) ∧
    dot (gradient 0 (base u)-gradient 1 (base u)) (base u)=u^2/2-(tieHeight u)^2 ∧
    u^2/2-(tieHeight u)^2<0 ∧
    (∀ᶠ ε : ℝ in 𝓝[>] 0, EligiblePair objective (1/4) (1/2)
      (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε)) ∧
    Tendsto (fun ε => (radialNumerator 0 (newPoint u ε) (oldGradient u ε) (newGradient u ε))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε))
      (𝓝[>] 0) atTop

theorem planarQuadraticCurve : PlanarQuadraticCurveTarget := by
  refine ⟨tieHeight_expansion,?_⟩
  intro u hu hsmall
  have ht := tie_active hu hsmall
  exact ⟨ht.1,ht.2.1,ht.2.2,(tie_radial_jump hu.le).2,tie_radial_jump_neg hu hsmall,
    eventually_eligible hu hsmall,radial_quotient_tendsto hu hsmall⟩

def PlanarQuadraticSeparationTarget : Prop := ∀ K : Set (Vec 2), K∈𝓝 (0 : Vec 2) →
  ¬HasRadialSecantBounds objective K 0 ∧
  ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → ∀ C : ℝ,
    ∃ x z g h : Vec 2, ∃ H : Mat 2,
      x∈K ∧ z∈K ∧ η≤objective z ∧ objective z≤objective x ∧
      EligiblePair objective (1/4) (1/2) x z g h ∧ pairDecrease x z g≤δ ∧
      H.PosDef ∧ bfgsStep H g 1=pairStep x z ∧
      C*pairCurvature x z g h<(radialNumerator 0 z g h)^2

theorem planarQuadraticSeparation : PlanarQuadraticSeparationTarget := by
  intro K hK
  exact ⟨not_radial_secant_on_neighborhood hK,eligible_radial_unbounded_on_neighborhood hK⟩

end BfgsVerification
