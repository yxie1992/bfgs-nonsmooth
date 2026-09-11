import BfgsVerification.PlanarCornerCharts

/-! Actual isolation and finiteness of regular nonsmooth points on one compact
planar level. Convexity of the branches is unnecessary for this local-chart
step; it is retained separately for the later secant estimates. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarCornerCharts
open HomogeneousPlanar ConvexSubdifferential

def TwoBranchRegularAt (F : Vec 2 → ℝ) (x : Vec 2) : Prop :=
  ∃ f : Fin 2 → Vec 2 → ℝ, ∃ a b : Vec 2,
    LocalFiniteMax F f x ∧ (∀ i, ContDiffAt ℝ 2 (f i) x) ∧
    HasFDerivAt (f 0) (gradientFunctional a) x ∧
    HasFDerivAt (f 1) (gradientFunctional b) x ∧
    pairDet a b ≠ 0 ∧ f 0 x=F x ∧ f 1 x=F x

theorem local_pair_eq_max {F : Vec 2 → ℝ} {f : Fin 2 → Vec 2 → ℝ} {x : Vec 2}
    (hrep : LocalFiniteMax F f x) : ∀ᶠ z in 𝓝 x, F z=max (f 0 z) (f 1 z) := by
  filter_upwards [hrep] with z hz
  apply le_antisymm
  · obtain ⟨i,hi⟩ := hz.1
    rw [← hi]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (hz.2 ⟨0,rfl⟩) (hz.2 ⟨1,rfl⟩)

theorem two_branch_smooth_of_ne {F : Vec 2 → ℝ} {f : Fin 2 → Vec 2 → ℝ} {x : Vec 2}
    (hrep : LocalFiniteMax F f x) (h0 : DifferentiableAt ℝ (f 0) x)
    (h1 : DifferentiableAt ℝ (f 1) x) (hne : f 0 x ≠ f 1 x) :
    DifferentiableAt ℝ F x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply h1.congr_of_eventuallyEq
    filter_upwards [local_pair_eq_max hrep,h0.continuousAt.eventually_lt h1.continuousAt hlt] with z he hz
    exact he.trans (max_eq_right hz.le)
  · apply h0.congr_of_eventuallyEq
    filter_upwards [local_pair_eq_max hrep,h1.continuousAt.eventually_lt h0.continuousAt hgt] with z he hz
    exact he.trans (max_eq_left hz.le)

/-- A regular two-branch corner is the only nonsmooth point of its objective
level in a sufficiently small neighborhood. -/
theorem nonsmooth_level_isolated {F : Vec 2 → ℝ} {x : Vec 2}
    (hx : TwoBranchRegularAt F x) :
    ∀ᶠ z in 𝓝 x, F z=F x → ¬DifferentiableAt ℝ F z → z=x := by
  obtain ⟨f,a,b,hrep,hC,h0,h1,hd,hf0,hf1⟩ := hx
  obtain ⟨p,hp,hpC,hplevel,hunique⟩ := exists_corner_curve hC h0 h1 hd hf0 hf1
  filter_upwards [hrep.eventually,local_pair_eq_max hrep,hunique,
    (hC 0).eventually (by norm_num),(hC 1).eventually (by norm_num)] with z hzrep hzmax hzuni hz0 hz1
  intro hlevel hn
  have heq : f 0 z=f 1 z := by
    by_contra he
    exact hn (two_branch_smooth_of_ne hzrep (hz0.differentiableAt (by norm_num))
      (hz1.differentiableAt (by norm_num)) he)
  apply hzuni
  have hvalue : f 1 z=F x := by simpa only [heq,max_self] using hzmax.symm.trans hlevel
  intro i
  fin_cases i
  · exact heq.trans hvalue
  · exact hvalue

/-- A compact set whose relevant points are locally isolated has only finitely
many such points; neighborhoods at irrelevant limit points are also required. -/
theorem finite_of_compact_local_singletons {K S : Set (Vec 2)} (hK : IsCompact K)
    (hSK : S ⊆ K) (hlocal : ∀ p ∈ K, ∀ᶠ z in 𝓝 p, z ∈ S → z=p) : S.Finite := by
  classical
  have hex (p : K) : ∃ U : Set (Vec 2), IsOpen U ∧ (p : Vec 2) ∈ U ∧
      ∀ z ∈ U, z ∈ S → z=(p : Vec 2) := by
    obtain ⟨U,hsub,hU,hp⟩ := mem_nhds_iff.mp (hlocal p p.property)
    exact ⟨U,hU,hp,fun z hz => hsub hz⟩
  choose U hU hp hsingle using hex
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (by
    intro p hpK
    exact mem_iUnion.mpr ⟨⟨p,hpK⟩,hp ⟨p,hpK⟩⟩)
  apply (s.finite_toSet.image (fun p : K => (p : Vec 2))).subset
  intro z hz
  obtain ⟨p,hps,hzp⟩ := mem_iUnion₂.mp (hs (hSK hz))
  exact ⟨p,hps,(hsingle p z hzp hz).symm⟩

/-- Finitely many actual nonsmooth corners occur in a compact regular subset of
one level. Smooth charts and two-branch inverse charts are the only premises. -/
theorem finite_nonsmooth_on_compact_level {F : Vec 2 → ℝ} {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀ p ∈ K, F p=ℓ)
    (hregular : ∀ p ∈ K, ContDiffAt ℝ 2 F p ∨ TwoBranchRegularAt F p) :
    {p ∈ K | ¬DifferentiableAt ℝ F p}.Finite := by
  apply finite_of_compact_local_singletons hK (fun _ hp => hp.1)
  intro p hp
  rcases hregular p hp with hs | hc
  · filter_upwards [hs.eventually (by norm_num)] with z hz hmem
    exact False.elim (hmem.2 (hz.differentiableAt (by norm_num)))
  · filter_upwards [nonsmooth_level_isolated hc] with z hz hmem
    exact hz ((hlevel z hmem.1).trans (hlevel p hp).symm) hmem.2

end PlanarCornerCharts
end BfgsVerification
