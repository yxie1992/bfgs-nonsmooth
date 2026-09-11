import BfgsVerification.PlanarTransversality
import BfgsVerification.TransportedCertificateRun
import BfgsVerification.ClusterSetGeometry
import BfgsVerification.StrictContours

/-! Actual-trajectory endpoint transversality, derived from compactness and
the common positive support comparison at the full cluster set. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification
namespace AdmissibleBFGSRun
open HomogeneousPlanar PlanarTransversality PlanarNormalGeometry ConvexSubdifferential
open ClusterSetGeometry
variable {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)

theorem normalized_displacement_descent (k : ℕ) :
    dot (R.g k) (normalized (R.displacement k)) ≤ 0 := by
  have hd : dot (R.g k) (R.displacement k)=-R.d k := R.dot_step_eq_neg_d k
  rw [normalized,dot_smul_right,hd]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) (neg_nonpos.mpr (R.d_pos k).le)

theorem normalized_displacement_weak_wolfe (k : ℕ) :
    (1-R.c₂)*(-dot (R.g k) (normalized (R.displacement k))) ≤
      dot (R.g (k+1)-R.g k) (normalized (R.displacement k)) := by
  have hc := mul_le_mul_of_nonneg_left (R.curvature_lower_bound k)
    (inv_nonneg.mpr (norm_nonneg (euclideanVector (R.displacement k))))
  have hd : dot (R.g k) (R.displacement k)=-R.d k := R.dot_step_eq_neg_d k
  rw [normalized,dot_smul_right,dot_smul_right,hd]
  convert hc using 1 <;> dsimp [displacement] <;> ring

/-- Uniform transversality along every sufficiently late accepted segment.
The field needs only actual local continuity and its common positive support
pairing at cluster points; no iterate or matrix limit is assumed. -/
theorem eventually_planar_segment_transverse
    (hK : IsCompact R.initialSublevel) (hsteps : Tendsto R.displacement atTop (𝓝 0))
    (W : Vec 2 → Vec 2)
    (hW : ∀ p ∈ clusterSet R.x, ContinuousAt W p)
    (hpos : ∀ p ∈ clusterSet R.x, ∀ g ∈ subdifferential F p, 0<dot g (W p))
    (hcommon : ∀ p ∈ clusterSet R.x, ∀ g ∈ subdifferential F p, ∀ h ∈ subdifferential F p,
      dot g (W p)=dot h (W p)) :
    ∃ κ : ℝ, 0<κ ∧ ∃ J : ℕ, ∀ k, J≤k → ∀ θ ∈ Icc (0 : ℝ) 1,
      κ ≤ |pairDet (normalized (R.displacement k)) (W (R.x k+θ • R.displacement k))| := by
  classical
  by_contra hn
  push_neg at hn
  have hchoose (j : ℕ) : ∃ k : ℕ, j≤k ∧ ∃ θ : ℝ, θ ∈ Icc (0 : ℝ) 1 ∧
      |pairDet (normalized (R.displacement k)) (W (R.x k+θ • R.displacement k))| < 1/((j : ℝ)+1) :=
    hn (1/((j : ℝ)+1)) (by positivity) j
  choose index hindex θ hθ hbad using hchoose
  have hindexTop : Tendsto index atTop atTop := tendsto_atTop_mono hindex tendsto_id
  obtain ⟨G,hG,hbound⟩ := R.bounded_gradients_of_compact_sublevel hK
  let Q : Set (Vec 2 × Vec 2 × Vec 2 × Vec 2 × ℝ) := R.initialSublevel ×ˢ closedBall (0 : Vec 2) G ×ˢ closedBall (0 : Vec 2) G ×ˢ
    CertificateGeometry.euclideanUnitBall ×ˢ Icc (0 : ℝ) 1
  have hQ : IsCompact Q := hK.prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (CertificateGeometry.euclideanUnitBall_compact.prod isCompact_Icc)))
  let sample (j : ℕ) := (R.x (index j),R.g (index j),R.g (index j+1),normalized (R.displacement (index j)),θ j)
  have hsample (j : ℕ) : sample j ∈ Q := by
    refine ⟨R.iterate_mem_initialSublevel _,?_,?_,?_,hθ j⟩
    · rw [mem_closedBall,dist_zero_right]
      exact norm_le_of_sqNorm_le hG.le (hbound (index j))
    · rw [mem_closedBall,dist_zero_right]
      exact norm_le_of_sqNorm_le hG.le (hbound (index j+1))
    · exact (PlanarObjectiveField.normalized_sqNorm (R.accepted_displacement_ne_zero _)).le
  obtain ⟨limit,hlimit,φ,hφ,hconv⟩ := hQ.tendsto_subseq hsample
  let idx (j : ℕ) := index (φ j)
  have hidx : Tendsto idx atTop atTop := hindexTop.comp hφ.tendsto_atTop
  let p := limit.1
  let g0 := limit.2.1
  let g1 := limit.2.2.1
  let e := limit.2.2.2.1
  let angle := limit.2.2.2.2
  have hx : Tendsto (fun j => R.x (idx j)) atTop (𝓝 p) := (continuous_fst.tendsto limit).comp hconv
  have hg : Tendsto (fun j => R.g (idx j)) atTop (𝓝 g0) := ((continuous_fst.comp continuous_snd).tendsto limit).comp hconv
  have hh : Tendsto (fun j => R.g (idx j+1)) atTop (𝓝 g1) := ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto limit).comp hconv
  have he : Tendsto (fun j => normalized (R.displacement (idx j))) atTop (𝓝 e) := ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto limit).comp hconv
  have hθlim : Tendsto (fun j => θ (φ j)) atTop (𝓝 angle) := ((continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto limit).comp hconv
  have hp : p ∈ clusterSet R.x := MapClusterPt.of_comp hidx hx.mapClusterPt
  have hs : Tendsto (fun j => R.displacement (idx j)) atTop (𝓝 0) := hsteps.comp hidx
  have hz : Tendsto (fun j => R.x (idx j+1)) atTop (𝓝 p) := by
    have heq (k : ℕ) : R.x (k+1)=R.x k+R.displacement k := by rw [R.step]; rfl
    simpa only [heq,add_zero] using hx.add hs
  have hg0 : g0 ∈ subdifferential F p := (isClosed_graph (convex_continuous R.convex)).mem_of_tendsto
    (hx.prodMk_nhds hg) (Eventually.of_forall (fun j => convex_supporting_inequality R.convex (R.hasGradient (idx j))))
  have hg1 : g1 ∈ subdifferential F p := (isClosed_graph (convex_continuous R.convex)).mem_of_tendsto
    (hz.prodMk_nhds hh) (Eventually.of_forall (fun j => convex_supporting_inequality R.convex (R.hasGradient (idx j+1))))
  have heunit : sqNorm e=1 := by
    have hl := continuous_sqNorm.tendsto e |>.comp he
    have hone : Tendsto (fun j => sqNorm (normalized (R.displacement (idx j)))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [PlanarObjectiveField.normalized_sqNorm (R.accepted_displacement_ne_zero _)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hl hone
  have hene : e ≠ 0 := by intro hez; simp [hez,sqNorm] at heunit
  have hmid : Tendsto (fun j => R.x (idx j)+θ (φ j) • R.displacement (idx j)) atTop (𝓝 p) := by
    simpa only [smul_zero,add_zero] using hx.add (hθlim.smul hs)
  have hw := (hW p hp).tendsto.comp hmid
  have hdet : pairDet e (W p) ≠ 0 := limiting_determinant_ne_zero
    (fun j => R.g (idx j)) (fun j => R.g (idx j+1))
    (fun j => normalized (R.displacement (idx j)))
    (fun j => W (R.x (idx j)+θ (φ j) • R.displacement (idx j)))
    hg hh he hw (sub_pos.mpr R.c₂_lt_one) hene (hpos p hp g0 hg0) (hcommon p hp g0 hg0 g1 hg1)
    (Eventually.of_forall (fun j => R.normalized_displacement_descent (idx j)))
    (Eventually.of_forall (fun j => R.normalized_displacement_weak_wolfe (idx j)))
  have hdetlim : Tendsto (fun j => |pairDet (normalized (R.displacement (idx j)))
      (W (R.x (idx j)+θ (φ j) • R.displacement (idx j)))|) atTop (𝓝 |pairDet e (W p)|) := by
    have hc : Continuous (fun v : Vec 2 × Vec 2 => |pairDet v.1 v.2|) := by unfold pairDet; fun_prop
    exact (hc.tendsto _).comp (he.prodMk_nhds hw)
  have hzero : Tendsto (fun j => |pairDet (normalized (R.displacement (idx j)))
      (W (R.x (idx j)+θ (φ j) • R.displacement (idx j)))|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun j => (hbad (φ j)).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  exact hdet (abs_eq_zero.mp (tendsto_nhds_unique hdetlim hzero))

/-- The normalized bound is the literal source determinant lower bound with
actual Euclidean step length. -/
theorem eventually_planar_segment_transverse_length
    (hK : IsCompact R.initialSublevel) (hsteps : Tendsto R.displacement atTop (𝓝 0))
    (W : Vec 2 → Vec 2)
    (hW : ∀ p ∈ clusterSet R.x, ContinuousAt W p)
    (hpos : ∀ p ∈ clusterSet R.x, ∀ g ∈ subdifferential F p, 0<dot g (W p))
    (hcommon : ∀ p ∈ clusterSet R.x, ∀ g ∈ subdifferential F p, ∀ h ∈ subdifferential F p,
      dot g (W p)=dot h (W p)) :
    ∃ κ : ℝ, 0<κ ∧ ∃ J : ℕ, ∀ k, J≤k → ∀ θ ∈ Icc (0 : ℝ) 1,
      κ * ‖euclideanVector (R.displacement k)‖ ≤
        |pairDet (R.displacement k) (W (R.x k+θ • R.displacement k))| := by
  obtain ⟨κ,hκ,J,hbound⟩ := R.eventually_planar_segment_transverse hK hsteps W hW hpos hcommon
  refine ⟨κ,hκ,J,?_⟩
  intro k hk θ hθ
  have hn : 0<‖euclideanVector (R.displacement k)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact R.accepted_displacement_ne_zero k (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => fun i => v i) hz)
  have he : pairDet (normalized (R.displacement k)) (W (R.x k+θ • R.displacement k)) =
      ‖euclideanVector (R.displacement k)‖⁻¹ * pairDet (R.displacement k) (W (R.x k+θ • R.displacement k)) := by
    simp only [pairDet,normalized,Pi.smul_apply,smul_eq_mul]
    ring
  have hb := hbound k hk θ hθ
  rw [he,abs_mul,abs_inv,abs_of_pos hn] at hb
  apply (le_div_iff₀ hn).mp
  simpa only [div_eq_mul_inv,mul_comm] using hb

/-- Source-only actual-run assembly of the comparison field and the complete
late-segment transversality bound. Vanishing steps are derived from the actual
strict limiting contour. -/
theorem exists_visible_transverse_planar_field
    (hK : IsCompact R.initialSublevel) {ℓ : ℝ}
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (hlower : ∃ y, F y<ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p ∈ clusterSet R.x, ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.TwoBranchRegularAt F p)
    (hnoncritical : ∀ p ∈ clusterSet R.x, ¬AffineCriticalObjective.IsAffineCritical F p) :
    ∃ W : Vec 2 → Vec 2,
      (∃ η : ℝ, 0<η ∧ ∃ N : Set (Vec 2), IsOpen N ∧ clusterSet R.x ⊆ N ∧
        (∀ p ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith L W U) ∧
        (∀ p ∈ N, ∀ g ∈ subdifferential F p, η ≤ dot g (W p))) ∧
      ∃ κ : ℝ, 0<κ ∧ ∃ J : ℕ, ∀ k, J≤k → ∀ θ ∈ Icc (0 : ℝ) 1,
        κ * ‖euclideanVector (R.displacement k)‖ ≤
          |pairDet (R.displacement k) (W (R.x k+θ • R.displacement k))| := by
  have hΓ := isCompact_clusterSet R.x hK R.iterate_mem_initialSublevel
  obtain ⟨W,hcommon,η,hη,N,hN,hΓN,hLip,hvis⟩ :=
    PlanarObjectiveField.exists_visible_comparison_field_on_compact_level R.convex hΓ
      (fun p hp => R.value_of_cluster hlim hp) hstrict hregular hnoncritical
  have hW : ∀ p ∈ clusterSet R.x, ContinuousAt W p := by
    intro p hp
    obtain ⟨L,U,hU,hLU⟩ := hLip p (hΓN hp)
    exact hLU.continuousOn.continuousAt hU
  have hpos : ∀ p ∈ clusterSet R.x, ∀ g ∈ subdifferential F p, 0<dot g (W p) :=
    fun p hp g hg => hη.trans_le (hvis p (hΓN hp) g hg)
  refine ⟨W,⟨η,hη,N,hN,hΓN,hLip,hvis⟩,?_⟩
  exact R.eventually_planar_segment_transverse_length hK
    (R.steps_tendsto_zero_of_strict_contour hK ℓ hlim hlower hstrict) W hW hpos hcommon

/-- Under the contradiction hypothesis of no affine-critical cluster point,
the objective limit and strict-contour step convergence are both derived. -/
theorem exists_visible_transverse_planar_field_of_no_affineCritical_cluster
    (hK : IsCompact R.initialSublevel) (star : Vec 2) (hmin : ∀ z, F star≤F z)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤F (R.x 0) →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p ∈ clusterSet R.x, ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.TwoBranchRegularAt F p)
    (hnoncritical : ∀ p ∈ clusterSet R.x, ¬AffineCriticalObjective.IsAffineCritical F p) :
    ∃ W : Vec 2 → Vec 2,
      (∃ η : ℝ, 0<η ∧ ∃ N : Set (Vec 2), IsOpen N ∧ clusterSet R.x ⊆ N ∧
        (∀ p ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith L W U) ∧
        (∀ p ∈ N, ∀ g ∈ subdifferential F p, η ≤ dot g (W p))) ∧
      ∃ κ : ℝ, 0<κ ∧ ∃ J : ℕ, ∀ k, J≤k → ∀ θ ∈ Icc (0 : ℝ) 1,
        κ * ‖euclideanVector (R.displacement k)‖ ≤
          |pairDet (R.displacement k) (W (R.x k+θ • R.displacement k))| := by
  obtain ⟨ℓ,hℓ,hlim,_⟩ := R.positive_limit_of_no_affineCritical_cluster hK
    R.iterate_mem_initialSublevel star hmin hnoncritical
  have hℓ0 : ℓ≤F (R.x 0) := le_of_tendsto hlim (Eventually.of_forall R.objective_le_initial)
  exact R.exists_visible_transverse_planar_field hK hlim ⟨star,hℓ⟩ (hstrict ℓ hℓ hℓ0) hregular hnoncritical

end AdmissibleBFGSRun
end BfgsVerification
