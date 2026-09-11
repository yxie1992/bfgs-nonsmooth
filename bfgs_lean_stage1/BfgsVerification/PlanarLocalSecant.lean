import BfgsVerification.PlanarCornerBounds

/-! Local all-eligible-pair secant correction bounds. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric
namespace BfgsVerification
namespace PlanarCrossing
open ConvexSubdifferential PlanarCornerCharts

theorem smooth_secant_correction {g h w s : Vec 2} {D G t : ℝ}
    (hD : 0≤D) (hG : 0≤G) (ht : 0<t)
    (hcurv : t=dot (h-g) s) (hcoco : sqNorm (h-g)≤D*dot (h-g) s)
    (hw : ‖w‖≤G) : (dot (h-g) w)^2/t≤4*D*G^2 := by
  have hwn : sqNorm w≤(2*G)^2 := by
    have he : ‖euclideanVector w‖^2=sqNorm w := FrameNorms.euclidean_norm_sq (euclideanVector w)
    rw [← he]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    exact (euclidean_norm_le_two_pi_norm w).trans (by gcongr)
  apply (div_le_iff₀ ht).mpr
  calc
    _≤sqNorm (h-g)*sqNorm w := dot_sq_le_sqNorm_mul_sqNorm _ _
    _≤(D*t)*(2*G)^2 := mul_le_mul (by rwa [← hcurv] at hcoco) hwn
      (sqNorm_nonneg _) (by positivity)
    _=_ := by ring

set_option maxHeartbeats 800000 in
/-- Uniformity is over all sufficiently close eligible pairs in this one
actual corner neighborhood, not only over a prescribed trajectory. -/
theorem cornerData_secant_bound {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {p : Vec 2} {f : Fin 2 → Vec 2 → ℝ} {W : Vec 2 → Vec 2}
    (c : CornerSecantData F p f W) {σ : ℝ} (hσ : 0<σ) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x z g h : Vec 2,
      x∈closedBall p c.radius → z∈closedBall p c.radius → ‖z-x‖≤δ →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      ∀ d t : ℝ, 0≤d → 0<t → dot g (z-x) = -d → t=dot (h-g) (z-x) → σ*d≤t →
      (dot (h-g) (W z))^2/t≤C := by
  have hL := c.L_nonneg
  have hA := c.A_pos
  have hD := c.D_pos
  let Q : ℝ := 1+8*c.A*c.L
  have hQ : 0<Q := by dsimp [Q]; nlinarith [mul_nonneg c.A_pos.le c.L_nonneg]
  let δ : ℝ := 1/Q
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    dsimp [δ]
    apply (div_le_iff₀ hQ).mpr
    dsimp [Q]
    nlinarith [mul_nonneg c.A_pos.le c.L_nonneg]
  have hδsmall : c.A*(4*c.L)*δ≤1/2 := by
    change c.A*(4*c.L)*(1/Q)≤1/2
    rw [mul_one_div]
    apply (div_le_iff₀ hQ).mpr
    dsimp [Q]
    ring_nf
    norm_num
  let C₁ : ℝ := (8*(c.L*c.G+c.H*c.B))^2*(2*c.A*(1+2/σ))
  let C₂ : ℝ := 4*c.D*c.G^2
  have hC₁ : 0≤C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0≤C₂ := by dsimp [C₂]; positivity
  refine ⟨δ,C₁+C₂,hδ,add_nonneg hC₁ hC₂,?_⟩
  intro x z g h hx hz hstep hg hh d t hd ht hdescent hcurv hwolfe
  obtain ⟨i,hi,hgi⟩ := exists_actual_active_gradient hF (c.representation x hx)
    (fun k => c.differentiable k x hx) hg
  obtain ⟨j,hj,hgj⟩ := exists_actual_active_gradient hF (c.representation z hz)
    (fun k => c.differentiable k z hz) hh
  by_cases hij : i=j
  · subst j
    have hcoco := c.cocoercive i x hx z hz
    rw [hgi,hgj] at hcoco
    exact (smooth_secant_correction c.D_pos.le c.G_nonneg ht hcurv hcoco
      (c.fieldBound z hz)).trans (by dsimp [C₂]; linarith)
  · have hs : c.A*(4*c.L)*‖z-x‖≤1/2 :=
      (mul_le_mul_of_nonneg_left hstep (by positivity)).trans hδsmall
    have hc := actual_crossing_secant_bound hF (convex_closedBall p c.radius)
      c.representation c.differentiable c.L_nonneg c.G_nonneg c.H_nonneg c.B_nonneg
      c.A_pos hσ c.gradLip c.fieldBound c.gradBound c.fieldLip c.common c.pair
      hx hz hg hh hij hi hj hd ht hdescent hcurv hwolfe hs
    exact hc.trans ((mul_le_of_le_one_right hC₁ (hstep.trans hδ1)).trans (le_add_of_nonneg_right hC₂))

/-- Source corner hypotheses discharge the complete local secant bound with
no assumption about Hessian definiteness beyond the actual BFGS run contract. -/
theorem convexCornerChart_local_secant {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {p : Vec 2} (c : ConvexCornerChart F p) {W : Vec 2 → Vec 2}
    (hW : ∀ᶠ z in 𝓝 p, W z=deriv c.curve (F z))
    (hWLip : ∃ B : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith B W U)
    {σ : ℝ} (hσ : 0<σ) :
    ∃ r δ C : ℝ, 0<r ∧ 0<δ ∧ 0≤C ∧ ∀ x z g h : Vec 2,
      x∈ball p r → z∈ball p r → ‖z-x‖≤δ →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      ∀ d t : ℝ, 0≤d → 0<t → dot g (z-x) = -d → t=dot (h-g) (z-x) → σ*d≤t →
      (dot (h-g) (W z))^2/t≤C := by
  let data := Classical.choice (convexCornerChart_nonempty_secantData hF c hW hWLip)
  obtain ⟨δ,C,hδ,hC,hb⟩ := cornerData_secant_bound hF data hσ
  exact ⟨data.radius,δ,C,data.radius_pos,hδ,hC,
    fun x z g h hx hz => hb x z g h (ball_subset_closedBall hx) (ball_subset_closedBall hz)⟩

/-- Smooth points also supply a full local objective-pair bound from actual
C² regularity and convexity, without a uniform positive Hessian premise. -/
theorem smooth_local_secant {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {p : Vec 2} (hC : ContDiffAt ℝ 2 F p) {W : Vec 2 → Vec 2}
    (hWLip : ∃ B : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith B W U) :
    ∃ r C : ℝ, 0<r ∧ 0≤C ∧ ∀ x z g h : Vec 2,
      x∈ball p r → z∈ball p r →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      ∀ t : ℝ, 0<t → t=dot (h-g) (z-x) → (dot (h-g) (W z))^2/t≤C := by
  obtain ⟨B,U,hU,hBW⟩ := hWLip
  have hn : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 2 F x ∧ x∈U :=
    (hC.eventually (by norm_num)).and hU
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  let r : ℝ := δ/2
  have hr : 0<r := by dsimp [r]; positivity
  have hsub : closedBall p r ⊆ ball p δ := by
    intro z hz
    have hh : dist z p≤δ/2 := hz
    exact show dist z p<δ from by linarith
  have hCOn : ContDiffOn ℝ 2 F (ball p δ) :=
    fun z hz => (hball hz).1.contDiffWithinAt
  obtain ⟨D,hD,hcoco⟩ := CenteredSmoothSublinear.exists_cocoercivity_constant_on_compact
    isOpen_ball (hF.subset (subset_univ _) (convex_ball p δ))
    (locallyC11_of_contDiffOn isOpen_ball hCOn) (isCompact_closedBall p r) hsub
  have hsubU : closedBall p r ⊆ U := fun z hz => (hball (hsub hz)).2
  obtain ⟨M,hM⟩ := (isCompact_closedBall p r).bddAbove_image ((hBW.mono hsubU).continuousOn.norm)
  let G : ℝ := |M|+1
  have hG : 0≤G := by dsimp [G]; positivity
  have hb : ∀ z∈closedBall p r, ‖W z‖≤G := fun z hz =>
    (hM ⟨z,hz,rfl⟩).trans (by dsimp [G]; linarith [le_abs_self M])
  refine ⟨r,4*D*G^2,hr,by positivity,?_⟩
  intro x z g h hx hz hg hh t ht hcurv
  have hgx : coordinateGradient F x=g := supporting_vector_eq_gradient
    (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hg.differentiableAt)) hg
  have hhz : coordinateGradient F z=h := supporting_vector_eq_gradient
    (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hh.differentiableAt)) hh
  have hc := hcoco x (ball_subset_closedBall hx) z (ball_subset_closedBall hz)
  rw [hgx,hhz] at hc
  exact smooth_secant_correction hD.le hG ht hcurv hc (hb z (ball_subset_closedBall hz))

end PlanarCrossing
end BfgsVerification
