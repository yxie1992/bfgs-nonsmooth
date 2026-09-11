import BfgsVerification.FixedNormalConvergence

/-! Source-level sublevel and local-basin wrappers. The basin is chosen before
any admissible run, and therefore before its initial SPD metric or fixed
Armijo/weak-Wolfe parameters. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter

namespace BfgsVerification
namespace FixedNormal

/-- U.1's local objective theorem, uniformly over every initial SPD matrix and
every fixed valid line-search pair carried by an actual admissible run. -/
theorem local_hyperplane_convergence_basin {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n)
    (hmin : ∀ z, F star ≤ F z) (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) (hplane : dot a star = b)
    {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b {0}) F) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ε, hε, hsub⟩ := Localization.neighborhood_basin hF star hmin hunique (hΩ.mem_nhds hstar)
  refine ⟨ε, hε, ?_⟩
  intro R hstart
  have hKΩ : R.initialSublevel ⊆ Ω := fun x hx => hsub (hx.trans hstart.le)
  exact R.fixed_normal_hyperplane_convergence hΩ
    (R.initialSublevel_compact_of_unique_minimizer star hmin hunique) hKΩ
    hμ hstrong ha b hA hLip hsmooth star hmin hunique hplane

/-- The parallel-interface local basin under affine-critical correctness on the
structural neighborhood. No BFGS initialization parameter enters its radius. -/
theorem local_parallel_interfaces_convergence_basin {n : ℕ} {F : Vec n → ℝ}
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
      Homogeneous.Supports F p 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ε, hε, hsub⟩ := Localization.neighborhood_basin hF star hmin hunique (hΩ.mem_nhds hstar)
  refine ⟨ε, hε, ?_⟩
  intro R hstart
  have hKΩ : R.initialSublevel ⊆ Ω := fun x hx => hsub (hx.trans hstart.le)
  have hconv := R.parallel_interfaces_convergence_of_affine_correctness hΩ
    (R.initialSublevel_compact_of_unique_minimizer star hmin hunique) hKΩ
    hμ hstrong ha b hA hLip hE hsmooth hsingular (fun p hp => hcorrect p (hKΩ hp)) star hmin
  exact ⟨hconv.1, hconv.2.2 hunique⟩

end FixedNormal

namespace AdmissibleBFGSRun
open FixedNormal ClusterSetGeometry
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Source U.2 with any compact trapping sublevel, which derives compactness of
the run's smaller initial sublevel rather than assuming it separately. -/
theorem parallel_interfaces_affineCritical_cluster_on_sublevel (c : ℝ)
    (hK : IsCompact {x : Vec n | F x ≤ c}) (hstart : F (R.x 0) ≤ c)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hKΩ : {x : Vec n | F x ≤ c} ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    (hsingular : ∀ p ∈ Ω, normalCoordinate a b p ∈ E → ¬DifferentiableAt ℝ F p) :
    ∃ p, MapClusterPt p atTop R.x ∧
      (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) := by
  have hsub : R.initialSublevel ⊆ {x : Vec n | F x ≤ c} := fun x hx => hx.trans hstart
  have hc : IsClosed R.initialSublevel := isClosed_le (convex_continuous R.convex) continuous_const
  exact R.parallel_interfaces_affineCritical_cluster hΩ (hK.of_isClosed_subset hc hsub)
    (hsub.trans hKΩ) hμ hstrong ha b hA hLip hE hsmooth hsingular

end AdmissibleBFGSRun
end BfgsVerification
