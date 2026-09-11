import BfgsVerification.CenteredRecentering

noncomputable section
open scoped Topology
open Set Filter BfgsVerification

/- These independent expected-type checks spell out the source regularity
instead of hiding it behind the LocallyC11On abbreviation. -/

example {n : ℕ} {F ψ γ : Vec n → ℝ} (A : AdmissibleBFGSRun n F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (U : Set (Vec n))
    (hU : IsOpen U) (hψ : ConvexOn ℝ U ψ)
    (hdiff : DifferentiableOn ℝ ψ U)
    (hlip : LocallyLipschitzOn U (fderiv ℝ ψ))
    (hγ : ConvexOn ℝ univ γ) (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    (hK : IsCompact A.initialSublevel) (hKU : A.initialSublevel ⊆ U) :
    Tendsto (fun k => F (A.x k)) atTop (𝓝 (F star)) :=
  A.centered_values star hmin hU hψ ⟨hdiff, hlip⟩ hγ hhom hrep hK hKU

example {n : ℕ} {F ψ γ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hunique : ∀ x, F x = F star → x = star) (U : Set (Vec n))
    (hU : IsOpen U) (hstar : star ∈ U) (hψ : ConvexOn ℝ U ψ)
    (hdiff : DifferentiableOn ℝ ψ U)
    (hlip : LocallyLipschitzOn U (fderiv ℝ ψ))
    (hγ : ConvexOn ℝ univ γ) (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : AdmissibleBFGSRun n F,
      F (A.x 0) ≤ F star + δ →
      (∀ k, A.x k ∈ U) ∧
      Tendsto (fun k => F (A.x k)) atTop (𝓝 (F star)) ∧ Tendsto A.x atTop (𝓝 star) :=
  CenteredSmoothSublinear.local_centered_basin hF star hmin hunique hU hstar
    hψ ⟨hdiff, hlip⟩ hγ hhom hrep

example {n : ℕ} {F ψ γ : Vec n → ℝ}
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (U : Set (Vec n))
    (hU : IsOpen U) (hstar : star ∈ U)
    (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    (p : Vec n) (hp : HasFDerivAt ψ (gradientFunctional p) star) :
    ∀ z, dot (-p) z ≤ γ z := by
  have hs := CenteredSmoothSublinear.center_support star hmin hU hstar hhom hrep hp
  simpa only [Homogeneous.Supports, sub_zero, Homogeneous.value_zero hhom] using hs

#check @CenteredSmoothSublinear.exists_pair_correction_bound
#check @AdmissibleBFGSRun.centered_uniform_correction
#check @CenteredSmoothSublinear.centered_rewriting
#check @CenteredSmoothSublinear.smoothRemainder_locallyC11
