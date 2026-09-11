import BfgsVerification.PlanarLocalSecant

/-! A finite buffered cover makes the local objective-pair estimates uniform,
including empty compact sets and without prescribing a trajectory. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric
namespace BfgsVerification
namespace PlanarCrossing

/-- The secant estimate on the actual differentiable eligible endpoints. -/
def PairSecantBound (F : Vec 2 → ℝ) (W : Vec 2 → Vec 2) (σ C : ℝ) (x z : Vec 2) : Prop :=
  ∀ g h : Vec 2, HasFDerivAt F (gradientFunctional g) x →
    HasFDerivAt F (gradientFunctional h) z →
    ∀ d t : ℝ, 0≤d → 0<t → dot g (z-x) = -d → t=dot (h-g) (z-x) → σ*d≤t →
    (dot (h-g) (W z))^2/t≤C

def LocalSecantControl (F : Vec 2 → ℝ) (W : Vec 2 → Vec 2) (σ : ℝ) (p : Vec 2) : Prop :=
  ∃ r δ C : ℝ, 0<r ∧ 0<δ ∧ 0≤C ∧ ∀ x z : Vec 2,
    x∈ball p r → z∈ball p r → ‖z-x‖≤δ → PairSecantBound F W σ C x z

theorem pairSecantBound_mono {F : Vec 2 → ℝ} {W : Vec 2 → Vec 2} {σ C D : ℝ}
    (hCD : C≤D) {x z : Vec 2} (h : PairSecantBound F W σ C x z) : PairSecantBound F W σ D x z := by
  intro g h' hg hh d t hd ht hdescent hcurv hwolfe
  exact (h g h' hg hh d t hd ht hdescent hcurv hwolfe).trans hCD

theorem localSecantControl_of_corner {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {p : Vec 2} (c : PlanarCornerCharts.ConvexCornerChart F p) {W : Vec 2 → Vec 2}
    (hW : ∀ᶠ z in 𝓝 p, W z=deriv c.curve (F z))
    (hWLip : ∃ B : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith B W U)
    {σ : ℝ} (hσ : 0<σ) : LocalSecantControl F W σ p := by
  obtain ⟨r,δ,C,hr,hδ,hC,hb⟩ := convexCornerChart_local_secant hF c hW hWLip hσ
  exact ⟨r,δ,C,hr,hδ,hC,fun x z hx hz hs g h hg hh => hb x z g h hx hz hs hg hh⟩

theorem localSecantControl_of_smooth {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {p : Vec 2} (hC : ContDiffAt ℝ 2 F p) {W : Vec 2 → Vec 2}
    (hWLip : ∃ B : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith B W U) (σ : ℝ) :
    LocalSecantControl F W σ p := by
  obtain ⟨r,C,hr,hC,hb⟩ := smooth_local_secant hF hC hWLip
  refine ⟨r,1,C,hr,zero_lt_one,hC,?_⟩
  intro x z hx hz _ g h hg hh d t _ ht _ hcurv _
  exact hb x z g h hx hz hg hh t ht hcurv

set_option maxHeartbeats 600000 in
/-- One open neighborhood, one positive distance threshold and one constant
work for every eligible pair. The finite family may be empty. -/
theorem compact_uniform_secant {F : Vec 2 → ℝ} {W : Vec 2 → Vec 2} {σ : ℝ}
    {K : Set (Vec 2)} (hK : IsCompact K) (hlocal : ∀ p∈K, LocalSecantControl F W σ p) :
    ∃ N : Set (Vec 2), ∃ δ C : ℝ, IsOpen N ∧ K⊆N ∧ 0<δ ∧ 0≤C ∧
      ∀ x∈N, ∀ z : Vec 2, ‖z-x‖≤δ → PairSecantBound F W σ C x z := by
  classical
  choose r δ C hr hδ hC hb using (fun p : K => hlocal p p.property)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover
    (fun p : K => ball (p : Vec 2) (r p/3)) (fun _ => isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self (div_pos (hr ⟨p,hp⟩) (by norm_num))⟩)
  obtain ⟨e,he,hes⟩ := CenteredSmoothSublinear.finite_positive_lower_bound s
    (fun p => min (δ p) (r p/3)) (fun p _ => lt_min (hδ p) (div_pos (hr p) (by norm_num)))
  let N : Set (Vec 2) := ⋃ p∈s, ball (p : Vec 2) (r p/3)
  let D : ℝ := ∑ p∈s, C p
  have hD : 0≤D := Finset.sum_nonneg (fun p _ => hC p)
  refine ⟨N,e,D,isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball)),hs,he,hD,?_⟩
  intro x hx z hz
  obtain ⟨p,hps,hxp⟩ := mem_iUnion₂.mp hx
  have hxe : x∈ball (p : Vec 2) (r p) := by
    have hx' := mem_ball.mp hxp
    exact show dist x (p : Vec 2)<r p from by linarith [hr p]
  have heδ : e≤δ p := (hes p hps).trans (min_le_left _ _)
  have her : e≤r p/3 := (hes p hps).trans (min_le_right _ _)
  have hze : z∈ball (p : Vec 2) (r p) := by
    have hzx : dist z x≤e := by simpa only [dist_eq_norm] using hz
    have hxp' := mem_ball.mp hxp
    have htri := dist_triangle z x (p : Vec 2)
    exact show dist z (p : Vec 2)<r p from by linarith [hr p]
  apply pairSecantBound_mono (C := C p) (D := D)
  · exact Finset.single_le_sum (f := C) (fun q _ => hC q) hps
  · exact hb p x z hxe hze (hz.trans heδ)

end PlanarCrossing
end BfgsVerification
