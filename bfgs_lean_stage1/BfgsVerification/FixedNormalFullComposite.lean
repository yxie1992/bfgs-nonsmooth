import BfgsVerification.FixedNormalCompositeConvergence

/-! The full-strong-convexity composite family from source U.1.1. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix
namespace BfgsVerification
namespace FixedNormal

/-- Full Euclidean strong convexity implies the exact projected version. -/
theorem full_strong_to_projected {n : ℕ} {F : Vec n → ℝ} {Ω : Set (Vec n)}
    {a : Vec n} (ha : sqNorm a = 1) {μ : ℝ} (hμ : 0 ≤ μ)
    (hstrong : EuclideanStrongConvexOn Ω μ F) :
    ConvexOn ℝ Ω (fun x => F x - (μ / 2) * sqNorm (tangentProjection a x)) := by
  have hsq : ConvexOn ℝ univ (fun t : ℝ => t ^ 2) := (even_two).convexOn_pow
  have hc := ((convex_normal_composite hsq a 0).subset (subset_univ Ω) hstrong.1).smul
    (show 0 ≤ μ / 2 by positivity)
  apply (hstrong.add hc).congr
  intro x hx
  simp only [Pi.add_apply, smul_eq_mul, normalCoordinate, sub_zero]
  rw [← tangentProjection_pythagorean ha x]
  ring

end FixedNormal
namespace AdmissibleBFGSRun
open FixedNormal ClusterSetGeometry
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The fully coupled composite illustration U.1.1. Strong convexity concerns
the full objective, and no positive-curvature premise is imposed on the smooth
summand alone. -/
theorem strongly_convex_composite_convergence {ψ : Vec n → ℝ} {h : ℝ → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel)
    (hKΩ : R.initialSublevel ⊆ Ω) (hψ : ConvexOn ℝ Ω ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : EuclideanStrongConvexOn Ω μ F)
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star) (hplane : dot a star = b) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  let A : Vec n → Vec n := fun x => tangentProjection a (coordinateGradient ψ x)
  have hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x := by
    intro x hx g hg
    exact composite_support_projection hh hΩ ha b hrep hx hg
      (hasFDerivAt_coordinateGradient ((hsmooth.1 x hx).differentiableAt (hΩ.mem_nhds hx)))
  have hAc : ContinuousOn A Ω := (continuous_tangentProjection a).comp_continuousOn
    (CenteredSmoothSublinear.continuousOn_coordinateGradient hsmooth.2)
  have hstrongF := full_strong_to_projected ha hμ.le hstrong
  have hfullsmooth := composite_locallyC11_off_interface hΩ hsmooth a b isClosed_singleton hhsm hrep
  obtain ⟨L, hL, hsec⟩ := exists_composite_tangent_secant hΩ hψ hsmooth hh ha b hrep hK hKΩ
  have htan (k : ℕ) : sqNorm (tangentProjection a (R.gradientChange k)) ≤ L * R.curvature k := by
    have he : R.x (k+1) - R.x k = R.displacement k := by rw [R.step]; simp [displacement]
    have hh := hsec (R.x k) (R.iterate_mem_initialSublevel k) (R.x (k+1))
      (R.iterate_mem_initialSublevel (k+1)) (R.g k) (R.g (k+1))
      (convex_supporting_inequality R.convex (R.hasGradient k))
      (convex_supporting_inequality R.convex (R.hasGradient (k+1)))
    rwa [he] at hh
  obtain ⟨ℓ, hℓ⟩ := R.objective_value_limit_of_lower_bound (F star) (fun k => hmin _)
  have hle : F star ≤ ℓ := ge_of_tendsto hℓ (Eventually.of_forall (fun k => hmin _))
  have heq : ℓ = F star := by
    by_contra hne
    have hlt : F star < ℓ := lt_of_le_of_ne hle (fun h => hne h.symm)
    have hsteps := R.displacement_tendsto_zero_of_strong_convexity hμ hstrong hK hKΩ
    have hΓΩ : clusterSet R.x ⊆ Ω := (clusterSet_subset_of_closed R.x hK.isClosed
      R.iterate_mem_initialSublevel).trans hKΩ
    have hstar : star ∈ Ω := hKΩ (hmin (R.x 0))
    apply R.tangential_cluster_geometry_incompatible hΩ hK hKΩ ha b hμ hstrongF hA hAc
      hL.le htan hsteps isClosed_singleton hfullsmooth
    · intro p hp hAp he
      have hpplane : dot a p = dot a star := by
        have he0 : normalCoordinate a b p = 0 := he
        dsimp only [normalCoordinate] at he0
        rw [hplane]
        linarith
      have heq := tangent_zero_on_minimizer_plane_of_projected_strong R.convex hμ hstrongF
        hstar (hΓΩ hp) hmin hpplane (fun g hg => (hA p (hΓΩ hp) g hg).trans hAp)
      have hv := R.value_of_cluster hℓ hp
      rw [heq] at hv
      linarith
    · intro p hp hdiff hz
      have hg := hasFDerivAt_coordinateGradient hdiff
      rw [hz] at hg
      have hm := global_minimum_of_zero_gradient R.convex hg star
      have hv := R.value_of_cluster hℓ hp
      rw [hv] at hm
      linarith
  have hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) := by rwa [heq] at hℓ
  exact ⟨hv, R.iterates_tendsto_unique_min_of_values star hmin hunique hv⟩

end AdmissibleBFGSRun
namespace FixedNormal

/-- The source's strongly convex composite family has a local basin for every
coupled SPD initialization and every fixed valid line search. -/
theorem local_strongly_convex_composite_basin {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    (hψ : ConvexOn ℝ Ω ψ) (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : EuclideanStrongConvexOn Ω μ F)
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (hplane : dot a star = b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ε, hε, hsub⟩ := Localization.neighborhood_basin hF star hmin hunique (hΩ.mem_nhds hstar)
  refine ⟨ε, hε, ?_⟩
  intro R hstart
  have hKΩ : R.initialSublevel ⊆ Ω := fun x hx => hsub (hx.trans hstart.le)
  exact R.strongly_convex_composite_convergence hΩ
    (R.initialSublevel_compact_of_unique_minimizer star hmin hunique) hKΩ hψ hsmooth hh hhsm
    ha b hμ hstrong hrep star hmin hunique hplane

end FixedNormal

end BfgsVerification
