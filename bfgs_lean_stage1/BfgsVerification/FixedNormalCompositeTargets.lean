import BfgsVerification.FixedNormalCompositeLocal
import BfgsVerification.FixedNormalFullComposite

/-! Exact original-objective contracts for the U.1.1 and U.6 composite
results. Their full and projected curvature hypotheses are stated separately;
frame bounds and convergence assumptions are absent from every target. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter
namespace BfgsVerification
open FixedNormal

def TangentialCompositeConvergenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {ψ : Vec n → ℝ} {h : ℝ → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel)
    (hKΩ : R.initialSublevel ⊆ Ω) (hψ : ConvexOn ℝ Ω ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection a x)))
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star) (hplane : dot a star = b)
    (hcontour : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ F (R.x 0) → StrictConvex ℝ {x : Vec n | F x ≤ ℓ}),
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

def TangentialCompositeLocalBasinTarget : Prop :=
  ∀ {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    (hψ : ConvexOn ℝ Ω ψ) (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection a x)))
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (hplane : dot a star = b) {c : ℝ} (hc : F star < c)
    (hcontour : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ c → StrictConvex ℝ {x : Vec n | F x ≤ ℓ}),
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

def StrongCompositeConvergenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {ψ : Vec n → ℝ} {h : ℝ → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel)
    (hKΩ : R.initialSublevel ⊆ Ω) (hψ : ConvexOn ℝ Ω ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : EuclideanStrongConvexOn Ω μ F)
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star) (hplane : dot a star = b),
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

def StrongCompositeLocalBasinTarget : Prop :=
  ∀ {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    (hψ : ConvexOn ℝ Ω ψ) (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : EuclideanStrongConvexOn Ω μ F)
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (hplane : dot a star = b),
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

end BfgsVerification
