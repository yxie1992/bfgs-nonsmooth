import BfgsVerification.PlanarSecantField
import BfgsVerification.ScalarTransportEnergy

/-! The actual-run secant budget and scalar BFGS contradiction from C's
objective-constructed field. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification
namespace AdmissibleBFGSRun
open ClusterSetGeometry ConvexSubdifferential PlanarCornerCharts PlanarObjectiveField
open AffineCriticalObjective PlanarCrossing
variable {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)

theorem eventually_planar_field_secant
    (hK : IsCompact R.initialSublevel) (hsteps : Tendsto R.displacement atTop (𝓝 0))
    {W : Vec 2 → Vec 2}
    (hlocal : ∀ p∈clusterSet R.x, LocalSecantControl F W (1-R.c₂) p) :
    ∃ C0 : ℝ, 0≤C0 ∧ ∃ J : ℕ, ∀ k, J≤k →
      (dot (R.gradientChange k) (W (R.x (k+1))))^2/R.curvature k≤C0 := by
  have hΓ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  obtain ⟨N,δ,C,hN,hΓN,hδ,hC,hbound⟩ := compact_uniform_secant hΓ hlocal
  have hx := eventually_mem_of_open_superset R.x hK R.iterate_mem_initialSublevel hN hΓN
  have hn : Tendsto (fun k => ‖R.displacement k‖) atTop (𝓝 0) := by simpa using hsteps.norm
  have hs : ∀ᶠ k in atTop, ‖R.displacement k‖<δ := hn.eventually (gt_mem_nhds hδ)
  refine ⟨C,hC,?_⟩
  apply eventually_atTop.mp
  filter_upwards [hx,hs] with k hxk hsk
  have he : R.x (k+1)-R.x k=R.displacement k := by rw [R.step,add_sub_cancel_left]; rfl
  have hd : dot (R.g k) (R.x (k+1)-R.x k) = -R.d k := by
    rw [he]
    exact R.dot_step_eq_neg_d k
  have ht : R.curvature k=dot (R.g (k+1)-R.g k) (R.x (k+1)-R.x k) := by rw [he]; rfl
  have hb := hbound (R.x k) hxk (R.x (k+1)) (by simpa only [he] using hsk.le)
    (R.g k) (R.g (k+1)) (R.hasGradient k) (R.hasGradient (k+1))
    (R.d k) (R.curvature k) (R.d_pos k).le (R.curvature_pos k) hd ht (R.curvature_lower_bound k)
  exact hb

set_option maxHeartbeats 600000 in
/-- All scalar-energy inputs are derived from one actual structured field.
No secant correction, transport multiplier, or matrix budget is assumed. -/
theorem structured_secant_field_incompatible
    (hK : IsCompact R.initialSublevel) (hsteps : Tendsto R.displacement atTop (𝓝 0))
    {m : ℕ} {χ : Fin m → Vec 2 → ℝ} {v : Fin m → ℝ → Vec 2}
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    {N : Set (Vec 2)} (hN : IsOpen N) (hΓN : clusterSet R.x⊆N) {η : ℝ} (hη : 0<η)
    (hLip : ∀ x∈N, ∃ L : ℝ≥0, ∃ U∈𝓝 x, LipschitzOnWith L (field R.convex χ v) U)
    (hvis : ∀ x∈N, ∀ g∈subdifferential F x, η≤dot g (field R.convex χ v x))
    (hv : ∀ x∈N, ∀ i, ContDiffAt ℝ 1 (v i) (F x))
    (hstruct : ∀ x∈N, ContDiffAt ℝ 2 F x ∨ ∃ i,
      ∀ᶠ z in 𝓝 x, field R.convex χ v z=v i (F z))
    (hcommon : ∀ x∈clusterSet R.x, ∀ g∈subdifferential F x, ∀ h∈subdifferential F x,
      dot g (field R.convex χ v x)=dot h (field R.convex χ v x))
    (hlocal : ∀ p∈clusterSet R.x, LocalSecantControl F (field R.convex χ v) (1-R.c₂) p) : False := by
  obtain ⟨C,hC,Jt,htransport⟩ := R.eventually_structured_field_transport hK hsteps hχ hN hΓN
    hη hLip hvis hv hstruct hcommon
  obtain ⟨C0,hC0,Js,hsecant⟩ := R.eventually_planar_field_secant hK hsteps hlocal
  obtain ⟨Jv,hvisible⟩ := eventually_atTop.mp
    (eventually_mem_of_open_superset R.x hK R.iterate_mem_initialSublevel hN hΓN)
  have hcoeff : ∀ k : ℕ, ∃ a b : ℝ, Jt≤k → 0<a ∧
      field R.convex χ v (R.x (k+1))=a • field R.convex χ v (R.x k)+b • R.displacement k ∧
      |Real.log a|≤C*R.d k := by
    intro k
    by_cases hk : Jt≤k
    · obtain ⟨a,b,ha,hframe,hlog⟩ := htransport k hk
      exact ⟨a,b,fun _ => ⟨ha,hframe,hlog⟩⟩
    · exact ⟨1,0,fun h => (hk h).elim⟩
  choose a b hab using hcoeff
  let J := max Jt (max Js Jv)
  have ht (k : ℕ) (hk : J≤k) : Jt≤k := (le_max_left _ _).trans hk
  have hs (k : ℕ) (hk : J≤k) : Js≤k := (le_max_left Js Jv).trans ((le_max_right _ _).trans hk)
  have hv' (k : ℕ) (hk : J≤k) : Jv≤k := (le_max_right Js Jv).trans ((le_max_right _ _).trans hk)
  apply R.scalar_log_transport_tail_incompatible hK J (fun k => field R.convex χ v (R.x k)) a b
    (fun k hk => (hab k (ht k hk)).2.1) η C C0 hη hC hC0
  · intro k hk
    exact hvis _ (hvisible k (hv' k hk)) _ (convex_supporting_inequality R.convex (R.hasGradient k))
  · exact fun k hk => (hab k (ht k hk)).1
  · exact fun k hk => (hab k (ht k hk)).2.2
  · exact fun k hk => hsecant k (hs k hk)

/-- The objective assumptions force an affine-critical cluster point. The
regularity premise is imposed only away from affine criticality. -/
theorem planar_affineCritical_cluster
    (hK : IsCompact R.initialSublevel) (star : Vec 2) (hmin : ∀ z, F star≤F z)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤F (R.x 0) →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p∈clusterSet R.x, ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) :
    ∃ p∈clusterSet R.x, IsAffineCritical F p := by
  by_contra hn
  have hno : ∀ p∈clusterSet R.x, ¬IsAffineCritical F p := by
    intro p hp hc
    exact hn ⟨p,hp,hc⟩
  obtain ⟨ℓ,hℓ,hlim,hlevel⟩ := R.positive_limit_of_no_affineCritical_cluster hK
    R.iterate_mem_initialSublevel star hmin hno
  have hℓ0 : ℓ≤F (R.x 0) := le_of_tendsto hlim (Eventually.of_forall R.objective_le_initial)
  have hs := hstrict ℓ hℓ hℓ0
  have hsteps := R.steps_tendsto_zero_of_strict_contour hK ℓ hlim ⟨star,hℓ⟩ hs
  have hΓ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  obtain ⟨m,χ,v,hχ,N,η,hη,hN,hΓN,hLip,hvis,hv,hstruct,hcommon,hlocal⟩ :=
    exists_secant_structured_visible_field R.convex hΓ (fun p hp => R.value_of_cluster hlim hp)
      hs (fun p hp => hregular p hp (hno p hp)) hno (sub_pos.mpr R.c₂_lt_one)
  exact R.structured_secant_field_incompatible hK hsteps hχ hN hΓN hη hLip hvis hv hstruct hcommon hlocal

end AdmissibleBFGSRun
end BfgsVerification
