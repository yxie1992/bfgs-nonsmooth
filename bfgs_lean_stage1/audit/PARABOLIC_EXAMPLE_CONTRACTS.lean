import BfgsVerification.ParabolicExampleContrast

noncomputable section
open scoped Topology
open Set Filter BfgsVerification
open TransportedCertificate RadialCertificate
open Parabolic.Example

/- The original exact finite maximum is a definition, not an abstract
counterexample objective with an assumed certificate failure. -/
example (x : Vec 2) : objective x =
    max (max ((x 0)^2+x 1) (3*(x 0)^2)) (2*(x 0)^2-x 1) := objective_eq_max x

/- Exact parameter-independent band quantifiers, with eligibility and an SPD
actual unit BFGS step in the conclusions, for every ordinary constant pair. -/
example {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℝ,
      ∃ x z g h : Vec 2, ∃ H : Mat 2,
        x ∈ K ∧ z ∈ K ∧ η ≤ objective z ∧ objective z ≤ objective x ∧
        EligiblePair objective c₁ c₂ x z g h ∧ pairDecrease x z g ≤ δ ∧
        H.PosDef ∧ bfgsStep H g 1 = pairStep x z ∧
        C*pairCurvature x z g h < (radialNumerator 0 z g h)^2 :=
  eligible_radial_unbounded_on_neighborhood hK (h12.trans hc₂) (hc₁.trans h12).le

/- Same objective: all actual full-BFGS runs converge, but the original RS
condition fails on every neighborhood. -/
example {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    (∀ R : AdmissibleBFGSRun 2 objective,
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ¬ HasRadialSecantBounds objective K 0 := converges_without_radial_secant hK

#check @printed_armijo_iff
#check @radial_quotient_tendsto
#check @source_compensated_log
