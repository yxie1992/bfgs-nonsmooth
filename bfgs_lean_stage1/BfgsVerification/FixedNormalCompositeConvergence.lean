import BfgsVerification.FixedNormalTangentialFrames
import BfgsVerification.FixedNormalConvergence
import BfgsVerification.FixedNormalCompositeCalculus
import BfgsVerification.FixedNormalCompositeSmooth
import BfgsVerification.StrictContours

/-! The tangential residual contradiction and actual U.6 objective assembly. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix
namespace BfgsVerification.AdmissibleBFGSRun
open FixedNormal ClusterSetGeometry
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The common contradiction behind U.1 and U.2. Only objective/cluster geometry
is supplied; the frame hypotheses and Hessian recurrence are derived. -/
theorem tangential_cluster_geometry_incompatible {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ)
    {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => F x - (μ / 2) * sqNorm (tangentProjection a x)))
    {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    (hAc : ContinuousOn A Ω) {L : ℝ} (hL : 0 ≤ L)
    (htan : ∀ k, sqNorm (tangentProjection a (R.gradientChange k)) ≤ L * R.curvature k)
    (hsteps : Tendsto R.displacement atTop (𝓝 0)) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    (hdis : ∀ p ∈ clusterSet R.x, A p = 0 → normalCoordinate a b p ∉ E)
    (hnonstat : ∀ p ∈ clusterSet R.x, DifferentiableAt ℝ F p → coordinateGradient F p ≠ 0) :
    False := by
  let Γ := clusterSet R.x
  have hΓ : IsCompact Γ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  have hΓn : Γ.Nonempty := clusterSet_nonempty R.x hK R.iterate_mem_initialSublevel
  have hΓΩ : Γ ⊆ Ω := (clusterSet_subset_of_closed R.x hK.isClosed
    R.iterate_mem_initialSublevel).trans hKΩ
  obtain ⟨r, U, hU, _, hproj⟩ := exists_tangent_matrix ha
  obtain ⟨δ, hδ, Lτ, τ, hτ, hτb, hone, hzero⟩ :=
    exists_cutoff_for_compact_set hΓ hΓΩ hAc a b hE hdis
  have hc := continuousOn_visibilityFunction hΩ hAc a b hE hsmooth
    hτ.continuous hδ hzero
  have hpos : ∀ p ∈ Γ, 0 < visibilityFunction F A a b τ p := by
    intro p hp
    apply visibilityFunction_pos R.convex ha (hA p (hΓΩ hp))
    intro hAp
    have hpreg : p ∈ regularRegion Ω a b E := ⟨hΓΩ hp, hdis p hp hAp⟩
    have hdiff := (hsmooth.1 p hpreg).differentiableAt
      ((isOpen_regularRegion hΩ a b hE).mem_nhds hpreg)
    exact ⟨hone p hp hAp, hdiff, hnonstat p hp hdiff⟩
  obtain ⟨m, hm, N, hNopen, hΓN, hNΩ, hvis⟩ :=
    exists_visibility_neighborhood hΩ hΓ hΓn hΓΩ hc hpos
  have hpair : ∀ᶠ k in atTop,
      m ≤ sqNorm ((cutoffFrame U a (τ (normalCoordinate a b (R.x k))))ᵀ.mulVec (R.g k)) := by
    filter_upwards [eventually_mem_of_open_superset R.x hK R.iterate_mem_initialSublevel
      hNopen hΓN] with k hk
    rw [cutoffFrame_pairing_eq_visibility R.convex U hU hproj (R.hasGradient k)
      (hA _ (hNΩ hk))]
    exact hvis _ hk
  obtain ⟨C₀, hC₀, hsec⟩ := R.eventually_tangential_frame_secant hΩ hK hKΩ ha b hL htan hsteps hE hsmooth hτb hδ hzero U hU hproj
  obtain ⟨J, htail⟩ := eventually_atTop.mp (hpair.and hsec)
  let Q := R.shift J
  have hxQ (k : ℕ) : Q.x k ∈ Ω := hKΩ (R.iterate_mem_initialSublevel (J + k))
  let β : ℕ → ℝ := fun k => cutoffSlope τ
    (normalCoordinate a b (Q.x k)) (normalCoordinate a b (Q.x (k + 1)))
  let V : ℕ → Matrix (Fin n) (Fin (r + 1)) ℝ :=
    fun k => cutoffFrame U a (τ (normalCoordinate a b (Q.x k)))
  let Z : ℕ → Matrix (Fin n) (Fin (r + 1)) ℝ :=
    fun k => cutoffResidual a (Q.displacement k) (β k)
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  apply R.residual_frames_on_tail_incompatible J G hG hg
    (R.summable_predicted_decreases_of_compact_sublevel hK) U hU
    L m C₀ 0 (2 * (Lτ : ℝ) ^ 2 / μ)
    hL hm hC₀ (by norm_num) (by positivity)
    (fun k => (tangent_matrix_sqNorm a U hU hproj (Q.gradientChange k)).le.trans (htan (J+k)))
    V Z (fun _ => 1) (fun k => normalCoefficient (β k))
  · intro k
    exact (htail (J + k) (Nat.le_add_right J k)).1
  · intro k
    exact (htail (J + k) (Nat.le_add_right J k)).2
  · intro k
    have he : Q.x (k + 1) - Q.x k = Q.displacement k := by
      rw [Q.step]
      simp [displacement]
    have ht := cutoffFrame_transport U a (Q.x k) (Q.x (k + 1)) b τ
    dsimp only at ht
    rw [he] at ht
    exact ht
  · intro k v
    simp only [transpose_one, one_mulVec, zero_mul, add_zero, one_mul]
    exact le_rfl
  · intro k
    exact cutoffResidual_tangential ha U hproj (Q.displacement k) (β k)
  · intro k
    exact Q.tangential_cutoff_residual_budget hμ hstrong hxQ hτ b k


/-- The weaker-curvature theorem U.6 for the actual composite objective.
Only tangential strong convexity is assumed; strict convexity of the positive
sublevels derives vanishing full steps. No frame, gradient split, secant bound,
matrix recurrence or convergence assumption is present. -/
theorem tangential_composite_convergence {ψ : Vec n → ℝ} {h : ℝ → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel)
    (hKΩ : R.initialSublevel ⊆ Ω) (hψ : ConvexOn ℝ Ω ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection a x)))
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star) (hplane : dot a star = b)
    (hcontour : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ F (R.x 0) → StrictConvex ℝ {x : Vec n | F x ≤ ℓ}) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  let A : Vec n → Vec n := fun x => tangentProjection a (coordinateGradient ψ x)
  have hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x := by
    intro x hx g hg
    exact composite_support_projection hh hΩ ha b hrep hx hg
      (hasFDerivAt_coordinateGradient ((hsmooth.1 x hx).differentiableAt (hΩ.mem_nhds hx)))
  have hAc : ContinuousOn A Ω := (continuous_tangentProjection a).comp_continuousOn
    (CenteredSmoothSublinear.continuousOn_coordinateGradient hsmooth.2)
  have hstrongF := composite_projected_strong_convex hh a b hstrong hrep
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
  have hle0 : ℓ ≤ F (R.x 0) := le_of_tendsto hℓ (Eventually.of_forall R.iterate_mem_initialSublevel)
  have heq : ℓ = F star := by
    by_contra hne
    have hlt : F star < ℓ := lt_of_le_of_ne hle (fun h => hne h.symm)
    have hsteps : Tendsto R.displacement atTop (𝓝 0) := by
      apply R.steps_tendsto_zero_of_strict_contour hK ℓ hℓ ⟨star, hlt⟩
      intro x z hxz
      have hclosed : IsClosed {x : Vec n | F x ≤ ℓ} :=
        isClosed_le (convex_continuous R.convex) continuous_const
      exact (hcontour ℓ hlt hle0).eq_of_openSegment_subset_frontier
        (hclosed.frontier_subset (hxz (left_mem_segment ℝ x z)))
        (hclosed.frontier_subset (hxz (right_mem_segment ℝ x z)))
        ((openSegment_subset_segment ℝ x z).trans hxz)
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

end BfgsVerification.AdmissibleBFGSRun
