import BfgsVerification.FixedNormalRunBounds
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix BfgsVerification BfgsVerification.FixedNormal

/- Actual objective strong convexity, without a step-summability assumption. -/
example {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    {Ω : Set (Vec n)} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => F x - (μ / 2) * sqNorm x))
    (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω) :
    Summable (fun k => sqNorm (R.displacement k)) ∧ Tendsto R.displacement atTop (𝓝 0) :=
  ⟨R.summable_sq_displacement_of_strong_convexity hμ hstrong hK hKΩ,
    R.displacement_tendsto_zero_of_strong_convexity hμ hstrong hK hKΩ⟩

/- An actual orthonormal representation is derived in arbitrary dimension. -/
example {n : ℕ} {a : Vec n} (ha : sqNorm a = 1) :
    ∃ r : ℕ, ∃ U : Matrix (Fin n) (Fin r) ℝ,
      Uᵀ * U = 1 ∧ Uᵀ.mulVec a = 0 ∧
      ∀ v, (U * Uᵀ).mulVec v = v - dot a v • a :=
  exists_tangent_matrix ha

/- Genuinely nondifferentiable points supply the required distinct supports. -/
example {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) {x a A : Vec n}
    (hA : ∀ g, Homogeneous.Supports F x g → g - dot a g • a = A)
    (hx : ¬DifferentiableAt ℝ F x) :
    (0 : Vec n) ∈ affineSpan ℝ {g | Homogeneous.Supports F x g} ↔ A = 0 :=
  affine_critical_iff_tangent_zero hF hA hx

/- Exact transport, no nonzero normal-increment condition. -/
example {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (a x z : Vec n)
    (b : ℝ) (τ : ℝ → ℝ) :
    let β := cutoffSlope τ (dot a x - b) (dot a z - b)
    cutoffFrame U a (τ (dot a z - b)) =
      cutoffFrame U a (τ (dot a x - b)) * (1 : Mat (r + 1)) +
      EnergyIdentities.rectOuter (z - x) (normalCoefficient β) + cutoffResidual a (z - x) β :=
  cutoffFrame_transport U a x z b τ

/- The original BFGS Hessian trace growth follows from objective projection
regularity and local strong convexity, without a Hessian growth premise. -/
example {n r : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    {Ω : Set (Vec n)} {a : Vec n} {A : Vec n → Vec n} {μ : ℝ}
    (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (hx : ∀ k, R.x k ∈ Ω)
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = tangentProjection a v) (k : ℕ) :
    (metricGram (R.hessian k) U).trace ≤ (metricGram (R.hessian 0) U).trace +
      ((n : ℝ) * (L : ℝ) ^ 2 / μ) * (k : ℝ) :=
  R.fixed_normal_hessian_trace_budget hμ hstrong hx hA hLip U hU hproj k
