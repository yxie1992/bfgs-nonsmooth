import BfgsVerification.PlanarFieldConstruction

/-! Uniform positive comparison against every actual support on an open
neighborhood of the whole compact level. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification
namespace PlanarObjectiveField
open ConvexSubdifferential PlanarNormalGeometry PlanarCornerCharts AffineCriticalObjective

/-- Positivity against the compact actual subdifferential persists uniformly
near a point where the comparison field is locally Lipschitz. -/
theorem supports_pairing_positive_near {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {W : Vec n → Vec n} {x : Vec n}
    (hW : ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U)
    (hpos : ∀ g ∈ subdifferential F x, 0 < dot g (W x)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ z in 𝓝 x, ∀ g ∈ subdifferential F z, η ≤ dot g (W z) := by
  classical
  obtain ⟨g0,hg0,hmin⟩ := (isCompact_subdifferential hF x).exists_isMinOn
    (subdifferential_nonempty hF x) (show ContinuousOn (fun g : Vec n => dot g (W x)) (subdifferential F x) from by unfold dot; fun_prop)
  let η : ℝ := dot g0 (W x)/2
  have hη : 0 < η := half_pos (hpos g0 hg0)
  obtain ⟨L,U,hU,hWU⟩ := hW
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  let Q := closedBall x (r/2)
  have hQ : IsCompact Q := isCompact_closedBall _ _
  have hQU : Q ⊆ U := (closedBall_subset_ball (by linarith : r/2<r)).trans hrU
  obtain ⟨G,hG,hbound⟩ := convex_supporting_bound_on_compact hF hQ
  let C : Set (Vec n × Vec n) := Q ×ˢ closedBall (0 : Vec n) G
  have hC : IsCompact C := hQ.prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun zg : Vec n × Vec n => dot zg.2 (W zg.1)) C := by
    have hp : ContinuousOn (fun zg : Vec n × Vec n => (zg.2,W zg.1)) C :=
      continuousOn_snd.prodMk (hWU.continuousOn.comp continuousOn_fst (fun z hz => hQU hz.1))
    exact continuous_dot.comp_continuousOn hp
  let B : Set (Vec n × Vec n) :=
    (C ∩ {zg | dot zg.2 (W zg.1) ≤ η}) ∩ {zg | zg.2 ∈ subdifferential F zg.1}
  have hB : IsCompact B := by
    apply (hC.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hC.isClosed isClosed_Iic) inter_subset_left).inter_right
    exact isClosed_graph (convex_continuous hF)
  have hproj : IsClosed (Prod.fst '' B) := (hB.image continuous_fst).isClosed
  have hx : x ∉ Prod.fst '' B := by
    rintro ⟨⟨z,g⟩,hz,hzx⟩
    have he : z=x := hzx
    have hg : g ∈ subdifferential F x := by simpa only [← he] using hz.2
    have hb : dot g (W x) ≤ η := by simpa only [← he] using hz.1.2
    have hm : dot g0 (W x) ≤ dot g (W x) := hmin hg
    dsimp only [η] at hb
    linarith [hpos g0 hg0]
  refine ⟨η,hη,?_⟩
  filter_upwards [closedBall_mem_nhds x (by linarith : 0<r/2),hproj.isOpen_compl.mem_nhds hx] with z hz hnot
  intro g hg
  by_contra hneg
  apply hnot
  refine ⟨(z,g),⟨⟨⟨hz,?_⟩,le_of_lt (lt_of_not_ge hneg)⟩,hg⟩,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact norm_le_of_sqNorm_le hG.le (hbound z hz g hg)

/-- The positive constant and neighborhood cover the whole compact set; no
single presumed limit point is selected. -/
theorem exists_uniform_supports_visibility {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {W : Vec n → Vec n} {K : Set (Vec n)} (hK : IsCompact K)
    (hW : ∀ x ∈ K,
      (∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U) ∧
      (∀ g ∈ subdifferential F x, 0 < dot g (W x))) :
    ∃ η : ℝ, 0 < η ∧ ∃ N : Set (Vec n), IsOpen N ∧ K ⊆ N ∧
      ∀ x ∈ N, ∀ g ∈ subdifferential F x, η ≤ dot g (W x) := by
  classical
  by_cases hKn : K.Nonempty
  · have hex (x : K) : ∃ η : ℝ, 0<η ∧ ∃ N : Set (Vec n), IsOpen N ∧ (x : Vec n) ∈ N ∧
        ∀ z ∈ N, ∀ g ∈ subdifferential F z, η ≤ dot g (W z) := by
      obtain ⟨η,hη,hnear⟩ := supports_pairing_positive_near hF (hW x x.property).1 (hW x x.property).2
      obtain ⟨N,hsub,hN,hx⟩ := _root_.mem_nhds_iff.mp hnear
      exact ⟨η,hη,N,hN,hx,fun z hz => hsub hz⟩
    choose η hη N hN hxN hbound using hex
    obtain ⟨s,hs⟩ := hK.elim_finite_subcover N hN (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxN ⟨x,hx⟩⟩)
    let p : K := ⟨hKn.choose,hKn.choose_spec⟩
    let t := insert p s
    have htn : t.Nonempty := ⟨p,Finset.mem_insert_self p s⟩
    let η0 := t.inf' htn η
    have hη0 : 0<η0 := (Finset.lt_inf'_iff htn).mpr (fun x _ => hη x)
    refine ⟨η0,hη0,⋃ x ∈ t, N x,isOpen_iUnion (fun x => isOpen_iUnion (fun _ => hN x)),?_,?_⟩
    · intro x hx
      obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion₂.mpr ⟨p,Finset.mem_insert_of_mem hp,hxp⟩
    · intro x hx g hg
      obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hx
      exact (Finset.inf'_le η hp).trans (hbound p x hxp g hg)
  · refine ⟨1,by norm_num,∅,isOpen_empty,?_,by simp⟩
    exact subset_empty_iff.mpr (Set.not_nonempty_iff_eq_empty.mp hKn)

/-- Pointwise local Lipschitz neighborhoods extend to an open neighborhood
of the entire set. This step is independent of any support selection. -/
theorem exists_open_local_lipschitz_extension {n : ℕ} {W : Vec n → Vec n} {K : Set (Vec n)}
    (hW : ∀ x ∈ K, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U) :
    ∃ N : Set (Vec n), IsOpen N ∧ K ⊆ N ∧
      ∀ x ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U := by
  classical
  have hex (x : K) : ∃ L : ℝ≥0, ∃ U : Set (Vec n), IsOpen U ∧ (x : Vec n) ∈ U ∧ LipschitzOnWith L W U := by
    obtain ⟨L,U,hU,hLU⟩ := hW x x.property
    obtain ⟨V,hVU,hV,hx⟩ := _root_.mem_nhds_iff.mp hU
    exact ⟨L,V,hV,hx,hLU.mono hVU⟩
  choose L U hU hxU hLU using hex
  refine ⟨⋃ x : K, U x,isOpen_iUnion hU,?_,?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  · intro x hx
    obtain ⟨p,hp⟩ := mem_iUnion.mp hx
    exact ⟨L p,U p,(hU p).mem_nhds hp,hLU p⟩

/-- The actual source geometry yields positive comparison uniformly near the
whole compact regular level. No support-selection continuity or field budget is
assumed. The exact equal pairing on the base level is retained for endpoint
transversality. -/
theorem exists_visible_comparison_field_on_compact_level {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ TwoBranchRegularAt F x)
    (hnoncritical : ∀ x ∈ K, ¬IsAffineCritical F x) :
    ∃ W : Vec 2 → Vec 2,
      (∀ x ∈ K, ∀ g ∈ subdifferential F x, ∀ h ∈ subdifferential F x, dot g (W x)=dot h (W x)) ∧
      ∃ η : ℝ, 0<η ∧ ∃ N : Set (Vec 2), IsOpen N ∧ K ⊆ N ∧
        (∀ x ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U) ∧
        (∀ x ∈ N, ∀ g ∈ subdifferential F x, η ≤ dot g (W x)) := by
  obtain ⟨W,hW⟩ := exists_comparison_field_on_compact_level hF hK hlevel hstrict hregular hnoncritical
  obtain ⟨η,hη,N,hN,hKN,hbound⟩ := exists_uniform_supports_visibility hF hK
    (fun x hx => ⟨(hW x hx).1,(hW x hx).2.1⟩)
  obtain ⟨V,hV,hKV,hLip⟩ := exists_open_local_lipschitz_extension (fun x hx => (hW x hx).1)
  exact ⟨W,fun x hx => (hW x hx).2.2,η,hη,N∩V,hN.inter hV,
    fun x hx => ⟨hKN hx,hKV hx⟩,fun x hx => hLip x hx.2,fun x hx => hbound x hx.1⟩

end PlanarObjectiveField
end BfgsVerification
