import BfgsVerification.PlanarCrossingSecant

/-! All local secant constants are derived from the actual convex C² branch
chart and local Lipschitz comparison field. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Metric
namespace BfgsVerification
namespace PlanarCrossing
open PlanarCornerCharts ConvexSubdifferential HomogeneousPlanar

theorem contDiffAt_coordinateGradient {f : Vec 2 → ℝ} {x : Vec 2}
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (coordinateGradient f) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  apply contDiffAt_pi.mpr
  intro i
  exact hd.clm_apply contDiffAt_const

theorem locallyC11_of_contDiffOn {f : Vec 2 → ℝ} {U : Set (Vec 2)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) : CenteredSmoothSublinear.LocallyC11On U f := by
  refine ⟨hf.differentiableOn (by norm_num),?_⟩
  intro x hx
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (by norm_num)
  obtain ⟨L,V,hV,hLip⟩ := hd.exists_lipschitzOnWith
  exact ⟨L,V,mem_nhdsWithin_of_mem_nhds hV,hLip⟩

structure CornerSecantData (F : Vec 2 → ℝ) (c : Vec 2) (f : Fin 2 → Vec 2 → ℝ)
    (W : Vec 2 → Vec 2) where
  radius : ℝ
  radius_pos : 0<radius
  L : ℝ
  G : ℝ
  H : ℝ
  B : ℝ
  A : ℝ
  D : ℝ
  L_nonneg : 0≤L
  G_nonneg : 0≤G
  H_nonneg : 0≤H
  B_nonneg : 0≤B
  A_pos : 0<A
  D_pos : 0<D
  representation : ∀ x ∈ closedBall c radius, LocalFiniteMax F f x
  differentiable : ∀ i, ∀ x ∈ closedBall c radius, DifferentiableAt ℝ (f i) x
  gradLip : ∀ i, ∀ x ∈ closedBall c radius, ∀ z ∈ closedBall c radius,
    ‖coordinateGradient (f i) z-coordinateGradient (f i) x‖≤L*‖z-x‖
  fieldBound : ∀ x ∈ closedBall c radius, ‖W x‖≤G
  gradBound : ∀ i, ∀ x ∈ closedBall c radius, ‖coordinateGradient (f i) x‖≤H
  fieldLip : ∀ x ∈ closedBall c radius, ∀ z ∈ closedBall c radius,
    ‖W z-W x‖≤B*‖z-x‖
  common : ∀ p ∈ closedBall c radius, ∀ g ∈ subdifferential F p,
    ∀ h ∈ subdifferential F p, dot g (W p)=dot h (W p)
  pair : ∀ x ∈ closedBall c radius, ∀ v,
    ‖v‖≤A*(|dot (coordinateGradient (f 0) x) v|+|dot (coordinateGradient (f 1) x) v|)
  cocoercive : ∀ i, ∀ x ∈ closedBall c radius, ∀ z ∈ closedBall c radius,
    sqNorm (coordinateGradient (f i) z-coordinateGradient (f i) x)≤
      D*dot (coordinateGradient (f i) z-coordinateGradient (f i) x) (z-x)

set_option maxHeartbeats 800000 in
/-- The source's convex C² chart supplies every entry of the local data.
The field is the same one appearing in the actual inverse-curve identity. -/
theorem convexCornerChart_nonempty_secantData {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {x : Vec 2} (c : ConvexCornerChart F x) {W : Vec 2 → Vec 2}
    (hW : ∀ᶠ z in 𝓝 x, W z=deriv c.curve (F z))
    (hWLip : ∃ B : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith B W U) :
    Nonempty (CornerSecantData F x c.branches W) := by
  obtain ⟨B,UW,hUW,hBW⟩ := hWLip
  obtain ⟨L₀,U₀,hU₀,hLip₀⟩ := (contDiffAt_coordinateGradient (c.branchesC2 0)).exists_lipschitzOnWith
  obtain ⟨L₁,U₁,hU₁,hLip₁⟩ := (contDiffAt_coordinateGradient (c.branchesC2 1)).exists_lipschitzOnWith
  obtain ⟨A,hA,hpair⟩ := convexCornerChart_eventually_pair_control c
  have hgood : ∀ᶠ z in 𝓝 x, z∈c.region ∧ z∈UW ∧ z∈U₀ ∧ z∈U₁ ∧
      (∀ g∈subdifferential F z, ∀ h∈subdifferential F z, dot g (W z)=dot h (W z)) ∧
      (∀ s, ‖s‖≤A*(|dot (coordinateGradient (c.branches 0) z) s|+
        |dot (coordinateGradient (c.branches 1) z) s|)) := by
    filter_upwards [c.region_open.mem_nhds c.point_mem,hUW,hU₀,hU₁,c.common_pairing_near hF hW,hpair]
      with z hz hzw hz0 hz1 hzc hzp
    exact ⟨hz,hzw,hz0,hz1,hzc,hzp⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r : ℝ := δ/2
  have hr : 0<r := by dsimp [r]; positivity
  let K := closedBall x r
  have hK : IsCompact K := isCompact_closedBall x r
  have hsub (z : Vec 2) (hz : z∈K) : z∈ball x δ := by
    have hz' : dist z x≤δ/2 := hz
    exact show dist z x<δ from by linarith
  have hKU : K⊆c.region := fun z hz => (hball (hsub z hz)).1
  have hKW : K⊆UW := fun z hz => (hball (hsub z hz)).2.1
  have hK₀ : K⊆U₀ := fun z hz => (hball (hsub z hz)).2.2.1
  have hK₁ : K⊆U₁ := fun z hz => (hball (hsub z hz)).2.2.2.1
  obtain ⟨G₀,hG₀⟩ := hK.bddAbove_image ((hBW.mono hKW).continuousOn.norm)
  obtain ⟨H₀,hH₀⟩ := hK.bddAbove_image ((hLip₀.mono hK₀).continuousOn.norm)
  obtain ⟨H₁,hH₁⟩ := hK.bddAbove_image ((hLip₁.mono hK₁).continuousOn.norm)
  have hC11 (i : Fin 2) := locallyC11_of_contDiffOn c.region_open (c.branch_C2 i)
  obtain ⟨D₀,hD₀,hc₀⟩ := CenteredSmoothSublinear.exists_cocoercivity_constant_on_compact
    c.region_open (c.branch_convex 0) (hC11 0) hK hKU
  obtain ⟨D₁,hD₁,hc₁⟩ := CenteredSmoothSublinear.exists_cocoercivity_constant_on_compact
    c.region_open (c.branch_convex 1) (hC11 1) hK hKU
  refine ⟨{
    radius := r
    radius_pos := hr
    L := (L₀:ℝ)+(L₁:ℝ)
    G := |G₀|+1
    H := |H₀|+|H₁|+1
    B := B
    A := A
    D := D₀+D₁
    L_nonneg := by positivity
    G_nonneg := by positivity
    H_nonneg := by positivity
    B_nonneg := B.coe_nonneg
    A_pos := hA
    D_pos := by positivity
    representation := ?_
    differentiable := ?_
    gradLip := ?_
    fieldBound := ?_
    gradBound := ?_
    fieldLip := ?_
    common := ?_
    pair := ?_
    cocoercive := ?_ }⟩
  · intro z hz
    filter_upwards [c.region_open.mem_nhds (hKU hz)] with p hp
    exact c.representation p hp
  · intro i z hz
    exact ((c.branch_C2 i).contDiffAt (c.region_open.mem_nhds (hKU hz))).differentiableAt (by norm_num)
  · intro i z hz q hq
    fin_cases i
    · exact (hLip₀.norm_sub_le (hK₀ hq) (hK₀ hz)).trans (by gcongr; exact le_add_of_nonneg_right L₁.coe_nonneg)
    · exact (hLip₁.norm_sub_le (hK₁ hq) (hK₁ hz)).trans (by gcongr; exact le_add_of_nonneg_left L₀.coe_nonneg)
  · intro z hz
    exact (hG₀ ⟨z,hz,rfl⟩).trans (by linarith [le_abs_self G₀])
  · intro i z hz
    fin_cases i
    · exact (hH₀ ⟨z,hz,rfl⟩).trans (by linarith [le_abs_self H₀,abs_nonneg H₁])
    · exact (hH₁ ⟨z,hz,rfl⟩).trans (by linarith [le_abs_self H₁,abs_nonneg H₀])
  · intro z hz q hq
    exact hBW.norm_sub_le (hKW hq) (hKW hz)
  · intro z hz
    exact (hball (hsub z hz)).2.2.2.2.1
  · intro z hz
    exact (hball (hsub z hz)).2.2.2.2.2
  · intro i z hz q hq
    fin_cases i
    · have hc := hc₀ z hz q hq
      have ht : 0≤dot (coordinateGradient (c.branches 0) q-coordinateGradient (c.branches 0) z) (q-z) := by
        nlinarith [sqNorm_nonneg (coordinateGradient (c.branches 0) q-coordinateGradient (c.branches 0) z)]
      exact hc.trans (mul_le_mul_of_nonneg_right (by linarith) ht)
    · have hc := hc₁ z hz q hq
      have ht : 0≤dot (coordinateGradient (c.branches 1) q-coordinateGradient (c.branches 1) z) (q-z) := by
        nlinarith [sqNorm_nonneg (coordinateGradient (c.branches 1) q-coordinateGradient (c.branches 1) z)]
      exact hc.trans (mul_le_mul_of_nonneg_right (by linarith) ht)

end PlanarCrossing
end BfgsVerification
