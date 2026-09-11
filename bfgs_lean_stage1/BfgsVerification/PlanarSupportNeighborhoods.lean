import BfgsVerification.PlanarCornerData

/-! Upper neighborhood control of all actual supports, and the exact normal
sector of a two-branch corner. No regularity of a selected support is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarNormalGeometry
open ConvexSubdifferential

def normalized {n : ℕ} (g : Vec n) : Vec n := ‖euclideanVector g‖⁻¹ • g

theorem normalized_continuousAt {n : ℕ} {g : Vec n} (hg : g ≠ 0) :
    ContinuousAt (normalized : Vec n → Vec n) g := by
  have hn : euclideanVector g ≠ 0 := by
    intro he
    exact hg (congrArg (fun v : EuclideanSpace ℝ (Fin n) => fun i => v i) he)
  have he : Continuous (euclideanVector : Vec n → EuclideanSpace ℝ (Fin n)) :=
    PiLp.continuous_equiv_symm _ _
  exact (he.continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr hn)).smul continuousAt_id

/-- Finite convex subdifferentials are upper semicontinuous: every open set
containing all supports at the base point contains all supports nearby. -/
theorem supports_eventually_subset_open {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x : Vec n} {U : Set (Vec n)} (hU : IsOpen U)
    (hsub : subdifferential F x ⊆ U) :
    ∀ᶠ z in 𝓝 x, subdifferential F z ⊆ U := by
  obtain ⟨G,hG,hbound⟩ := convex_supporting_bound_on_compact hF
    (isCompact_closedBall x (1 : ℝ))
  let B : Set (Vec n × Vec n) :=
    (Metric.closedBall x 1 ×ˢ Metric.closedBall (0 : Vec n) G) ∩
      {zg | zg.2 ∈ subdifferential F zg.1} ∩ {zg | zg.2 ∉ U}
  have hB : IsCompact B :=
    ((isCompact_closedBall x 1).prod (isCompact_closedBall (0 : Vec n) G)).inter_right
      (isClosed_graph (convex_continuous hF)) |>.inter_right (hU.isClosed_compl.preimage continuous_snd)
  have hproj : IsClosed (Prod.fst '' B) := (hB.image continuous_fst).isClosed
  have hx : x ∉ Prod.fst '' B := by
    rintro ⟨⟨z,g⟩,hzg,he⟩
    have hz : z=x := he
    exact hzg.2 (hsub (by simpa only [← hz] using hzg.1.2))
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1),
    hproj.isOpen_compl.mem_nhds hx] with z hz hnot
  intro g hg
  by_contra hng
  apply hnot
  refine ⟨(z,g),⟨⟨⟨Metric.ball_subset_closedBall hz,?_⟩,hg⟩,hng⟩,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact norm_le_of_sqNorm_le hG.le (hbound z (Metric.ball_subset_closedBall hz) g hg)

/-- This controls every normalized actual support nearby, including at
nondifferentiable points and for arbitrary choices of a supporting vector. -/
theorem normalized_supports_eventually_mem {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x : Vec n} {U : Set (Vec n)} (hU : IsOpen U)
    (hne : ∀ g ∈ subdifferential F x, g ≠ 0)
    (hsub : ∀ g ∈ subdifferential F x, normalized g ∈ U) :
    ∀ᶠ z in 𝓝 x, ∀ g ∈ subdifferential F z, g ≠ 0 ∧ normalized g ∈ U := by
  let V : Set (Vec n) := {g | g ≠ 0 ∧ normalized g ∈ U}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro g hg
    have hn : {v : Vec n | v ≠ 0} ∈ 𝓝 g :=
      (isOpen_ne : IsOpen {v : Vec n | v ≠ 0}).mem_nhds hg.1
    exact inter_mem hn ((normalized_continuousAt hg.1).eventually (hU.mem_nhds hg.2))
  exact supports_eventually_subset_open hF hV (fun g hg => ⟨hne g hg,hsub g hg⟩)

/-- Both active branches give precisely the actual subgradient segment. -/
theorem two_branch_subdifferential_eq_segment {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x)
    (hact : ∀ i, f i x=F x) : subdifferential F x=segment ℝ (g 0) (g 1) := by
  have hactive : activeIndices F f x=Finset.univ := by
    apply Finset.eq_univ_of_forall
    exact fun i => mem_activeIndices.mpr (hact i)
  have hrange : range g={g 0,g 1} := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact mem_range_self 0
      · exact mem_range_self 1
  have he := subdifferential_eq_active_convexHull hF hrep hg
  simpa only [hactive,Finset.coe_univ,image_univ,hrange,convexHull_pair] using he

/-- The geometrically constructed sector is exactly the normalized image of
all actual subgradients at a two-active-branch corner. -/
theorem normalSector_eq_actual_normals {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x)
    (hact : ∀ i, f i x=F x) :
    normalized '' subdifferential F x=normalSector (g 0) (g 1) := by
  rw [two_branch_subdifferential_eq_segment hF hrep hg hact]
  ext w
  constructor
  · rintro ⟨z,⟨r,s,hr,hs,hrs,rfl⟩,rfl⟩
    have he : r=1-s := by linarith
    refine ⟨s,⟨hs,by linarith⟩,?_⟩
    simp only [unitBlend,blend,normalized,he]
  · rintro ⟨s,hs,rfl⟩
    refine ⟨blend (g 0) (g 1) s,?_,rfl⟩
    exact ⟨1-s,s,by linarith [hs.2],hs.1,by ring,rfl⟩

/-- Every actual subgradient has the same increase rate at a regular corner. -/
theorem two_branch_support_pairing {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x v : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x)
    (hact : ∀ i, f i x=F x) (hv : ∀ i, dot (g i) v=1) :
    ∀ a ∈ subdifferential F x, dot a v=1 := by
  intro a ha
  rw [two_branch_subdifferential_eq_segment hF hrep hg hact] at ha
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := ha
  change dotProduct (r • g 0+s • g 1) v=1
  rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
  change r*dot (g 0) v+s*dot (g 1) v=1
  rw [hv,hv,mul_one,mul_one,hrs]

/-- A sector plateau automatically covers every actual normalized support at
all nearby points, on both smooth branches and on the switching set. -/
theorem all_supports_in_corner_plateau {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x v : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x)
    (hact : ∀ i, f i x=F x) (hv : ∀ i, dot (g i) v=1) {χ : Vec 2 → ℝ}
    (hχ : ∀ᶠ w in 𝓝ˢ (normalSector (g 0) (g 1)), χ w=1) :
    ∀ᶠ z in 𝓝 x, ∀ a ∈ subdifferential F z,
      a ≠ 0 ∧ ∀ᶠ w in 𝓝 (normalized a), χ w=1 := by
  obtain ⟨U,hU,hsector,hplateau⟩ := mem_nhdsSet_iff_exists.mp hχ
  have hne : ∀ a ∈ subdifferential F x, a ≠ 0 := by
    intro a ha he
    have hv' := two_branch_support_pairing hF hrep hg hact hv a ha
    rw [he] at hv'
    norm_num [dot] at hv'
  have hsub : ∀ a ∈ subdifferential F x, normalized a ∈ U := by
    intro a ha
    apply hsector
    rw [← normalSector_eq_actual_normals hF hrep hg hact]
    exact mem_image_of_mem _ ha
  filter_upwards [normalized_supports_eventually_mem hF hU hne hsub] with z hz
  intro a ha
  exact ⟨(hz a ha).1,Filter.mem_of_superset (hU.mem_nhds (hz a ha).2) hplateau⟩

end PlanarNormalGeometry
end BfgsVerification
