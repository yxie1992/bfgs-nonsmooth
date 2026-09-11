import BfgsVerification.FixedNormalSourceWrappers

/-! Exact objective-level contracts for Module U's principal theorems.
The weaker tangential-only composite extension and explicit spike examples are
separate obligations and are not asserted by these contracts. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter
namespace BfgsVerification
open FixedNormal ClusterSetGeometry

def FixedNormalHyperplaneTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b {0}) F)
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star) (hplane : dot a star = b),
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

def ParallelInterfacesClusterTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    (hsingular : ∀ p ∈ Ω, normalCoordinate a b p ∈ E → ¬DifferentiableAt ℝ F p),
    ∃ p ∈ clusterSet R.x,
      (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p)

def ParallelInterfacesConvergenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    (hsingular : ∀ p ∈ Ω, normalCoordinate a b p ∈ E → ¬DifferentiableAt ℝ F p)
    (hcorrect : ∀ p ∈ R.initialSublevel,
      (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) →
        Homogeneous.Supports F p 0)
    (star : Vec n) (hmin : ∀ z, F star ≤ F z),
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      ((∀ z, F z = F star → z = star) → Tendsto R.x atTop (𝓝 star))

def FixedNormalLocalBasinTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n)
    (hmin : ∀ z, F star ≤ F z) (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) (hplane : dot a star = b)
    {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b {0}) F),
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

def ParallelInterfacesLocalBasinTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n)
    (hmin : ∀ z, F star ≤ F z) (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    (hsingular : ∀ p ∈ Ω, normalCoordinate a b p ∈ E → ¬DifferentiableAt ℝ F p)
    (hcorrect : ∀ p ∈ Ω, (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) →
      Homogeneous.Supports F p 0),
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

end BfgsVerification
