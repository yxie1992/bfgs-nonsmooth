import BfgsVerification.FixedNormalSmoothStrip
import BfgsVerification.TransportedCertificateConvergence

/-! Actual full-BFGS contradiction from the entire fixed-normal cluster geometry.
All cutoffs, frames, visibility and matrix growth bounds are derived internally. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix

namespace BfgsVerification.AdmissibleBFGSRun
open FixedNormal ClusterSetGeometry
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The common contradiction behind U.1 and U.2. Only objective/cluster geometry
is supplied; the frame hypotheses and Hessian recurrence are derived. -/
theorem fixed_normal_cluster_geometry_incompatible {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
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
    exists_cutoff_for_compact_set hΓ hΓΩ hLip.continuousOn a b hE hdis
  have hc := continuousOn_visibilityFunction hΩ hLip.continuousOn a b hE hsmooth
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
  obtain ⟨C₀, hC₀, hsec⟩ := R.eventually_fixed_normal_frame_secant hΩ hK hKΩ hμ hstrong
    ha b hA hLip hE hsmooth hτb hδ hzero U hU hproj
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
    ((n : ℝ) * (L : ℝ) ^ 2 / μ) m C₀ 0 (2 * (Lτ : ℝ) ^ 2 / μ)
    (by positivity) hm hC₀ (by norm_num) (by positivity)
    (Q.fixed_normal_tangent_secant hμ hstrong hxQ hA hLip U hU hproj)
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
    exact Q.fixed_normal_cutoff_residual_budget hμ hstrong hxQ ha hτ b k

/-- Theorem U.2: an actual affine-critical cluster point is forced by the
objective's fixed-normal geometry, including infinitely many closed interfaces. -/
theorem parallel_interfaces_affineCritical_cluster {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    (hsingular : ∀ p ∈ Ω, normalCoordinate a b p ∈ E → ¬DifferentiableAt ℝ F p) :
    ∃ p ∈ clusterSet R.x,
      (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) := by
  by_contra hn
  push_neg at hn
  have hΓΩ : clusterSet R.x ⊆ Ω := (clusterSet_subset_of_closed R.x hK.isClosed
    R.iterate_mem_initialSublevel).trans hKΩ
  apply R.fixed_normal_cluster_geometry_incompatible hΩ hK hKΩ hμ hstrong ha b hA hLip hE hsmooth
  · intro p hp hAp he
    apply hn p hp
    exact (affine_critical_iff_tangent_zero R.convex (hA p (hΓΩ hp))
      (hsingular p (hΓΩ hp) he)).mpr hAp
  · intro p hp hdiff hz
    apply hn p hp
    apply subset_affineSpan ℝ _
    have hs := convex_supporting_inequality R.convex (hasFDerivAt_coordinateGradient hdiff)
    rw [hz] at hs
    exact hs

/-- Theorem U.1: a single exceptional hyperplane through the unique optimizer
allows smooth exceptional points and unbounded nearby normal curvature. -/
theorem fixed_normal_hyperplane_convergence {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b {0}) F)
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star) (hplane : dot a star = b) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ℓ, hℓ⟩ := R.objective_value_limit_of_lower_bound (F star) (fun k => hmin _)
  have hle : F star ≤ ℓ := ge_of_tendsto hℓ (Eventually.of_forall (fun k => hmin _))
  have heq : ℓ = F star := by
    by_contra hne
    have hlt : F star < ℓ := lt_of_le_of_ne hle (fun h => hne h.symm)
    have hΓΩ : clusterSet R.x ⊆ Ω := (clusterSet_subset_of_closed R.x hK.isClosed
      R.iterate_mem_initialSublevel).trans hKΩ
    have hstar : star ∈ Ω := hKΩ (hmin (R.x 0))
    apply R.fixed_normal_cluster_geometry_incompatible hΩ hK hKΩ hμ hstrong ha b hA hLip
      isClosed_singleton hsmooth
    · intro p hp hAp he
      have hpplane : dot a p = dot a star := by
        have he0 : normalCoordinate a b p = 0 := he
        dsimp only [normalCoordinate] at he0
        rw [hplane]
        linarith
      have heq := tangent_zero_on_minimizer_plane R.convex hμ hstrong hstar (hΓΩ hp) hmin
        hpplane (fun g hg => (hA p (hΓΩ hp) g hg).trans hAp)
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

/-- U.2 plus actual affine-critical correctness gives minimum-value and
solution-set convergence; uniqueness then gives convergence of all iterates. -/
theorem parallel_interfaces_convergence_of_affine_correctness {Ω : Set (Vec n)}
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
    (star : Vec n) (hmin : ∀ z, F star ≤ F z) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      ((∀ z, F z = F star → z = star) → Tendsto R.x atTop (𝓝 star)) := by
  obtain ⟨p, hp, hc⟩ := R.parallel_interfaces_affineCritical_cluster hΩ hK hKΩ hμ hstrong
    ha b hA hLip hE hsmooth hsingular
  have hpK := clusterSet_subset_of_closed R.x hK.isClosed R.iterate_mem_initialSublevel hp
  have hpmin := ConvexSubdifferential.zero_mem_iff_global_minimum.mp (hcorrect p hpK hc)
  obtain ⟨ℓ, hℓ⟩ := R.objective_value_limit_of_lower_bound (F star) (fun k => hmin _)
  have hpvalue : F p = F star := le_antisymm (hpmin star) (hmin p)
  have heq : ℓ = F star := (R.value_of_cluster hℓ hp).symm.trans hpvalue
  have hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) := by rwa [heq] at hℓ
  exact ⟨hv, R.distance_to_argmin_of_values star hmin hK R.iterate_mem_initialSublevel hv,
    fun hu => R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

end BfgsVerification.AdmissibleBFGSRun
