import BfgsVerification.PlanarEndpointTransport
import BfgsVerification.PlanarRunTransversality

/-! Actual full-BFGS trajectory assembly for C's logarithmic transport. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Metric
namespace BfgsVerification
namespace AdmissibleBFGSRun
open ClusterSetGeometry PlanarObjectiveField ConvexSubdifferential
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Compactness and vanishing actual displacements put every late full
accepted segment in any open neighborhood of the entire cluster set. -/
theorem eventually_segments_in_cluster_neighborhood
    (hK : IsCompact R.initialSublevel) (hsteps : Tendsto R.displacement atTop (𝓝 0))
    {N : Set (Vec n)} (hN : IsOpen N) (hΓN : clusterSet R.x ⊆ N) :
    ∃ J : ℕ, ∀ k, J≤k → ∀ t ∈ Icc (0:ℝ) 1, R.x k+t • R.displacement k ∈ N := by
  have hΓ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  obtain ⟨δ,hδ,hsub⟩ := hΓ.exists_cthickening_subset_open hN hΓN
  have hx := eventually_mem_of_open_superset R.x hK R.iterate_mem_initialSublevel
    (isOpen_thickening : IsOpen (thickening (δ/2) (clusterSet R.x)))
    (self_subset_thickening (by linarith) _)
  have hn : Tendsto (fun k => ‖R.displacement k‖) atTop (𝓝 0) := by simpa using hsteps.norm
  have hsmall : ∀ᶠ k in atTop, ‖R.displacement k‖<δ/2 := hn.eventually (gt_mem_nhds (by linarith))
  apply eventually_atTop.mp
  filter_upwards [hx,hsmall] with k hxk hsk
  intro t ht
  obtain ⟨p,hp,hxp⟩ := mem_thickening_iff.mp hxk
  apply hsub
  apply thickening_subset_cthickening
  apply mem_thickening_iff.mpr
  refine ⟨p,hp,?_⟩
  calc
    dist (R.x k+t • R.displacement k) p ≤
        dist (R.x k+t • R.displacement k) (R.x k)+dist (R.x k) p := dist_triangle _ _ _
    _ < δ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      have hh : t*‖R.displacement k‖ ≤ ‖R.displacement k‖ := by nlinarith [ht.2,norm_nonneg (R.displacement k)]
      linarith

end AdmissibleBFGSRun
namespace AdmissibleBFGSRun
open ClusterSetGeometry PlanarObjectiveField ConvexSubdifferential PlanarCornerCharts AffineCriticalObjective
variable {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)

/-- Actual full-BFGS steps admit logarithmic transport for one fixed chosen
structured comparison field. All field, derivative and segment bounds are
derived from the neighborhood data and compactness. -/
theorem eventually_structured_field_transport
    (hK : IsCompact R.initialSublevel) (hsteps : Tendsto R.displacement atTop (𝓝 0))
    {m : ℕ} {χ : Fin m → Vec 2 → ℝ} {v : Fin m → ℝ → Vec 2}
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    {N : Set (Vec 2)} (hN : IsOpen N) (hΓN : clusterSet R.x ⊆ N) {η : ℝ} (hη : 0<η)
    (hLip : ∀ x ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (field R.convex χ v) U)
    (hvis : ∀ x ∈ N, ∀ g ∈ subdifferential F x, η ≤ dot g (field R.convex χ v x))
    (hv : ∀ x ∈ N, ∀ i, ContDiffAt ℝ 1 (v i) (F x))
    (hstruct : ∀ x ∈ N, ContDiffAt ℝ 2 F x ∨ ∃ i,
      ∀ᶠ z in 𝓝 x, field R.convex χ v z=v i (F z))
    (hcommon : ∀ x ∈ clusterSet R.x, ∀ g ∈ subdifferential F x, ∀ h ∈ subdifferential F x,
      dot g (field R.convex χ v x)=dot h (field R.convex χ v x)) :
    ∃ C : ℝ, 0≤C ∧ ∃ J : ℕ, ∀ k, J≤k → ∃ lam β : ℝ, 0<lam ∧
      field R.convex χ v (R.x (k+1))=lam • field R.convex χ v (R.x k)+β • R.displacement k ∧
      |Real.log lam| ≤ C*R.d k := by
  have hΓ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  obtain ⟨V,Q,hV,hΓV,hVQ,hQ,hQN,M,ρ,hρ,G,hG,hballs,hW,hM⟩ :=
    exists_compact_uniform_field_buffer hΓ hN hΓN hLip
  have hcont : ∀ p ∈ N, ContinuousAt (field R.convex χ v) p := by
    intro p hp
    obtain ⟨L,U,hU,hLU⟩ := hLip p hp
    exact hLU.continuousOn.continuousAt hU
  obtain ⟨A,hA,hvel⟩ := compact_velocity_derivative_bound (convex_continuous R.convex) hQ
    (fun p hp => hv p (hQN hp))
  obtain ⟨κ,hκ,Jt,htrans⟩ := R.eventually_planar_segment_transverse_length hK hsteps
    (field R.convex χ v) (fun p hp => hcont p (hΓN hp))
    (fun p hp g hg => hη.trans_le (hvis p (hΓN hp) g hg)) hcommon
  obtain ⟨Js,hseg⟩ := R.eventually_segments_in_cluster_neighborhood hK hsteps hV hΓV
  let C : ℝ := 2*max (6*(M:ℝ)/(κ*(η/G))) (A/κ)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,max Jt Js,?_⟩
  intro k hk
  have htk : Jt≤k := (le_max_left _ _).trans hk
  have hsk : Js≤k := (le_max_right _ _).trans hk
  have hsQ : ∀ t ∈ Icc (0:ℝ) 1, R.x k+t • R.displacement k ∈ Q :=
    fun t ht => hVQ (subset_closure (hseg k hsk t ht))
  have hgd : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
  have hnext : R.x (k+1)=R.x k+R.displacement k := by rw [R.step]; rfl
  obtain ⟨lam,β,hlam,he,hlog⟩ := structured_field_segment_transport R.convex hχ
    (R.accepted_displacement_ne_zero k) (fun p hp => hv p (hQN hp))
    (fun p hp => hstruct p (hQN hp)) (fun p hp => hcont p (hQN hp))
    hη hG hA.le hκ (fun p hp => hvis p (hQN hp)) hW hM hvel hsQ
    (htrans k htk) (R.hasGradient k) (R.d_pos k).le hgd
    (by rw [← hnext]; exact R.objective_antitone (Nat.le_succ k))
  exact ⟨lam,β,hlam,by rwa [← hnext] at he,hlog⟩

/-- The source compactness, strict limiting contour, regular switching and
absence of affine-critical clusters produce actual positive logarithmic
transport. No field, matrix regularity or step convergence is a premise. -/
theorem exists_log_transported_planar_field
    (hK : IsCompact R.initialSublevel) {ℓ : ℝ}
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (hlower : ∃ y, F y<ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p ∈ clusterSet R.x, ContDiffAt ℝ 2 F p ∨ TwoBranchRegularAt F p)
    (hnoncritical : ∀ p ∈ clusterSet R.x, ¬IsAffineCritical F p) :
    ∃ W : Vec 2 → Vec 2,
      (∃ N : Set (Vec 2), ∃ η : ℝ, 0<η ∧ IsOpen N ∧ clusterSet R.x ⊆ N ∧
        (∀ p ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith L W U) ∧
        (∀ p ∈ N, ∀ g ∈ subdifferential F p, η ≤ dot g (W p))) ∧
      ∃ C : ℝ, 0≤C ∧ ∃ J : ℕ, ∀ k, J≤k → ∃ lam β : ℝ,
        0<lam ∧ W (R.x (k+1))=lam • W (R.x k)+β • R.displacement k ∧
        |Real.log lam| ≤ C*R.d k := by
  have hΓ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  obtain ⟨m,χ,v,hχ,N,η,hη,hN,hΓN,hLip,hvis,hv,hstruct,hcommon⟩ :=
    exists_structured_visible_comparison_field R.convex hΓ
      (fun p hp => R.value_of_cluster hlim hp) hstrict hregular hnoncritical
  exact ⟨field R.convex χ v,⟨N,η,hη,hN,hΓN,hLip,hvis⟩,R.eventually_structured_field_transport hK
    (R.steps_tendsto_zero_of_strict_contour hK ℓ hlim hlower hstrict)
    hχ hN hΓN hη hLip hvis hv hstruct hcommon⟩

/-- Source-only contradiction-trajectory version: the finite objective limit
and positive limiting gap are derived from compactness and an actual minimizer. -/
theorem exists_log_transported_planar_field_of_no_affineCritical_cluster
    (hK : IsCompact R.initialSublevel) (star : Vec 2) (hmin : ∀ z, F star≤F z)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤F (R.x 0) →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p ∈ clusterSet R.x, ContDiffAt ℝ 2 F p ∨ TwoBranchRegularAt F p)
    (hnoncritical : ∀ p ∈ clusterSet R.x, ¬IsAffineCritical F p) :
    ∃ W : Vec 2 → Vec 2,
      (∃ N : Set (Vec 2), ∃ η : ℝ, 0<η ∧ IsOpen N ∧ clusterSet R.x ⊆ N ∧
        (∀ p ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith L W U) ∧
        (∀ p ∈ N, ∀ g ∈ subdifferential F p, η ≤ dot g (W p))) ∧
      ∃ C : ℝ, 0≤C ∧ ∃ J : ℕ, ∀ k, J≤k → ∃ lam β : ℝ,
        0<lam ∧ W (R.x (k+1))=lam • W (R.x k)+β • R.displacement k ∧
        |Real.log lam| ≤ C*R.d k := by
  obtain ⟨ℓ,hℓ,hlim,_⟩ := R.positive_limit_of_no_affineCritical_cluster hK
    R.iterate_mem_initialSublevel star hmin hnoncritical
  have hℓ0 : ℓ≤F (R.x 0) := le_of_tendsto hlim (Eventually.of_forall R.objective_le_initial)
  exact R.exists_log_transported_planar_field hK hlim ⟨star,hℓ⟩
    (hstrict ℓ hℓ hℓ0) hregular hnoncritical

end AdmissibleBFGSRun
end BfgsVerification
