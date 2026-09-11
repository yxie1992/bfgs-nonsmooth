import BfgsVerification.PlanarFieldStructure

/-! The source's local convex two-branch hypothesis, retaining the same
branches, inverse chart and level velocities for the crossing secant proof. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter
namespace BfgsVerification
namespace PlanarCornerCharts
open HomogeneousPlanar ConvexSubdifferential

def ConvexTwoBranchRegularAt (F : Vec 2 → ℝ) (x : Vec 2) : Prop :=
  ∃ f : Fin 2 → Vec 2 → ℝ, ∃ U : Set (Vec 2), IsOpen U ∧ x ∈ U ∧
    (∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U) ∧
    (∀ z ∈ U, IsGreatest (range (fun i => f i z)) (F z)) ∧
    (∀ i, f i x=F x) ∧
    pairDet (coordinateGradient (f 0) x) (coordinateGradient (f 1) x) ≠ 0

theorem ConvexTwoBranchRegularAt.to_regular {F : Vec 2 → ℝ} {x : Vec 2}
    (hx : ConvexTwoBranchRegularAt F x) : TwoBranchRegularAt F x := by
  obtain ⟨f,U,hU,hxU,hf,hrep,hact,hdet⟩ := hx
  have hC (i : Fin 2) := (hf i).2.contDiffAt (hU.mem_nhds hxU)
  have hloc : LocalFiniteMax F f x := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact hrep z hz
  exact ⟨f,_,_,hloc,hC,
    hasFDerivAt_coordinateGradient ((hC 0).differentiableAt (by norm_num)),
    hasFDerivAt_coordinateGradient ((hC 1).differentiableAt (by norm_num)),hdet,hact 0,hact 1⟩

structure ConvexCornerChart (F : Vec 2 → ℝ) (x : Vec 2) extends CornerChart F x where
  region : Set (Vec 2)
  region_open : IsOpen region
  point_mem : x ∈ region
  branch_convex : ∀ i, ConvexOn ℝ region (branches i)
  branch_C2 : ∀ i, ContDiffOn ℝ 2 (branches i) region
  representation : ∀ z ∈ region, IsGreatest (range (fun i => branches i z)) (F z)
  independent : pairDet (coordinateGradient (branches 0) x) (coordinateGradient (branches 1) x) ≠ 0
  inverse : ∀ᶠ z in 𝓝 x, (∀ i, branches i z=branches 0 z) → z=curve (branches 0 z)

theorem nonempty_convexCornerChart {F : Vec 2 → ℝ} {x : Vec 2}
    (hx : ConvexTwoBranchRegularAt F x) : Nonempty (ConvexCornerChart F x) := by
  obtain ⟨f,U,hU,hxU,hf,hrep,hact,hdet⟩ := hx
  have hC (i : Fin 2) := (hf i).2.contDiffAt (hU.mem_nhds hxU)
  have hg (i : Fin 2) := hasFDerivAt_coordinateGradient ((hC i).differentiableAt (by norm_num))
  obtain ⟨p,hp,hpC,hlevel,hinv⟩ := exists_corner_chart hC (hg 0) (hg 1) hdet (hact 0) (hact 1)
  have hgrad (i : Fin 2) : HasFDerivAt (f i)
      (gradientFunctional (coordinateGradient (f i) x)) (p (F x)) := by rw [hp]; exact hg i
  have hvel := curve_velocity_pairing ((hpC.differentiableAt (by norm_num)).hasDerivAt) hgrad hlevel
  have hloc : LocalFiniteMax F f x := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact hrep z hz
  exact ⟨{
    branches := f
    curve := p
    localMax := hloc
    branchesC2 := hC
    active := hact
    curveAt := hp
    curveC2 := hpC
    defining := hlevel
    commonRate := hvel
    region := U
    region_open := hU
    point_mem := hxU
    branch_convex := fun i => (hf i).1
    branch_C2 := fun i => (hf i).2
    representation := hrep
    independent := hdet
    inverse := hinv }⟩

/-- Finite source convex corner charts retain all local data needed by both
transport and secant estimates, including when the corner family is empty. -/
theorem exists_finite_convexCornerCharts {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec 2)} {ℓ : ℝ} (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ConvexTwoBranchRegularAt F x) :
    ∃ m : ℕ, ∃ points : Fin m → Vec 2, ∃ charts : ∀ i, ConvexCornerChart F (points i),
      Function.Injective points ∧ (∀ i, points i ∈ K ∧ ¬DifferentiableAt ℝ F (points i)) ∧
      ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ∃ i, x=points i := by
  have hweak : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ TwoBranchRegularAt F x := by
    intro x hx
    exact (hregular x hx).imp_right ConvexTwoBranchRegularAt.to_regular
  obtain ⟨m,points,_,hinj,hpoints,hcover⟩ := exists_finite_cornerCharts hF hK hlevel hweak
  have hc (i : Fin m) : Nonempty (ConvexCornerChart F (points i)) := by
    rcases hregular (points i) (hpoints i).1 with hs | hr
    · exact ((hpoints i).2 (hs.differentiableAt (by norm_num))).elim
    · exact nonempty_convexCornerChart hr
  exact ⟨m,points,fun i => Classical.choice (hc i),hinj,hpoints,hcover⟩

/-- Differentiating the actual defining curve at every nearby level gives
the exact common branch rate there, rather than only at the reference point. -/
theorem ConvexCornerChart.commonRate_near {F : Vec 2 → ℝ} {x : Vec 2}
    (c : ConvexCornerChart F x) :
    ∀ᶠ t in 𝓝 (F x), ∀ i,
      dot (coordinateGradient (c.branches i) (c.curve t)) (deriv c.curve t)=1 := by
  have hpcont : Tendsto c.curve (𝓝 (F x)) (𝓝 x) := by
    simpa only [ContinuousAt,c.curveAt] using c.curveC2.continuousAt
  have hbranch : ∀ᶠ t in 𝓝 (F x), ∀ i, ContDiffAt ℝ 2 (c.branches i) (c.curve t) := by
    apply eventually_all.mpr
    intro i
    exact hpcont.eventually ((c.branchesC2 i).eventually (by norm_num))
  filter_upwards [hbranch,c.curveC2.eventually (by norm_num),c.defining.eventually_nhds] with t ht hc he
  exact curve_velocity_pairing ((hc.differentiableAt (by norm_num)).hasDerivAt)
    (fun i => hasFDerivAt_coordinateGradient ((ht i).differentiableAt (by norm_num))) he

/-- The local inverse identity identifies every nearby tie point with its
actual common-level curve point, including without a nonsmoothness premise. -/
theorem ConvexCornerChart.tie_point_on_curve {F : Vec 2 → ℝ} {x : Vec 2}
    (c : ConvexCornerChart F x) :
    ∀ᶠ z in 𝓝 x, c.branches 0 z=c.branches 1 z → z=c.curve (F z) := by
  filter_upwards [c.inverse,local_pair_eq_max c.localMax] with z hz hm
  intro he
  have hall : ∀ i, c.branches i z=c.branches 0 z := by intro i; fin_cases i; rfl; exact he.symm
  have hFz : F z=c.branches 0 z := by simpa only [← he,max_self] using hm
  simpa only [hFz] using hz hall

/-- The source field cancels every actual support jump at every nearby
corner level. Smooth nearby points are handled by uniqueness of their support. -/
theorem ConvexCornerChart.common_pairing_near {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {x : Vec 2} (c : ConvexCornerChart F x) {W : Vec 2 → Vec 2}
    (hW : ∀ᶠ z in 𝓝 x, W z=deriv c.curve (F z)) :
    ∀ᶠ z in 𝓝 x, ∀ g ∈ subdifferential F z, ∀ h ∈ subdifferential F z,
      dot g (W z)=dot h (W z) := by
  have hvel : ∀ᶠ z in 𝓝 x, ∀ i,
      dot (coordinateGradient (c.branches i) (c.curve (F z))) (deriv c.curve (F z))=1 :=
    (convex_continuous hF).continuousAt.tendsto.eventually c.commonRate_near
  filter_upwards [hW,hvel,c.localMax.eventually_nhds,c.tie_point_on_curve,
    (c.branchesC2 0).eventually (by norm_num),(c.branchesC2 1).eventually (by norm_num)]
    with z hzW hzvel hzrep hzcurve hz0 hz1
  intro g hg h hh
  by_cases hdiff : DifferentiableAt ℝ F z
  · have hd := hasFDerivAt_coordinateGradient hdiff
    rw [supporting_vector_eq_gradient hg hd,supporting_vector_eq_gradient hh hd]
  · have he : c.branches 0 z=c.branches 1 z := by
      by_contra hn
      exact hdiff (two_branch_smooth_of_ne hzrep (hz0.differentiableAt (by norm_num))
        (hz1.differentiableAt (by norm_num)) hn)
    have hzcurve' := hzcurve he
    have hact : ∀ i, c.branches i z=F z := by
      have hm := (local_pair_eq_max hzrep).self_of_nhds
      have hf0 : c.branches 0 z=F z := by simpa only [← he,max_self] using hm.symm
      intro i
      fin_cases i
      · exact hf0
      · exact he.symm.trans hf0
    have hgrad (i : Fin 2) : HasFDerivAt (c.branches i)
        (gradientFunctional (coordinateGradient (c.branches i) z)) z := by
      fin_cases i
      · exact hasFDerivAt_coordinateGradient (hz0.differentiableAt (by norm_num))
      · exact hasFDerivAt_coordinateGradient (hz1.differentiableAt (by norm_num))
    have hr : ∀ i, dot (coordinateGradient (c.branches i) z) (W z)=1 := by
      intro i
      rw [hzW]
      calc
        dot (coordinateGradient (c.branches i) z) (deriv c.curve (F z)) =
            dot (coordinateGradient (c.branches i) (c.curve (F z))) (deriv c.curve (F z)) :=
          congrArg (fun p => dot (coordinateGradient (c.branches i) p) (deriv c.curve (F z))) hzcurve'
        _ = 1 := hzvel i
    rw [PlanarNormalGeometry.two_branch_support_pairing hF hzrep hgrad hact hr g hg,
      PlanarNormalGeometry.two_branch_support_pairing hF hzrep hgrad hact hr h hh]

end PlanarCornerCharts
end BfgsVerification
