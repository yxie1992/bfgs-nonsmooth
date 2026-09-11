import BfgsVerification.PlanarConvexCorner

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification.PlanarAllPairs
open PlanarCornerCharts PlanarObjectiveField ConvexSubdifferential AffineCriticalObjective

theorem common_pairing_neighborhood {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec 2)} {m : ℕ} (points : Fin m → Vec 2)
    (charts : ∀i,ConvexCornerChart F (points i)) {W : Vec 2 → Vec 2}
    (hcorner : ∀i,∀ᶠ z in 𝓝 (points i),W z=deriv (charts i).curve (F z))
    (hcover : ∀x∈K,ContDiffAt ℝ 2 F x ∨ ∃i,x=points i) :
    ∃N : Set (Vec 2),IsOpen N ∧ K⊆N ∧
      ∀x∈N,∀g∈subdifferential F x,∀h∈subdifferential F x,dot g (W x)=dot h (W x) := by
  let P (x : Vec 2) : Prop := ∀g∈subdifferential F x,∀h∈subdifferential F x,dot g (W x)=dot h (W x)
  refine ⟨interior {x | P x},isOpen_interior,?_,fun x hx => interior_subset hx⟩
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  rcases hcover x hx with hs | ⟨i,rfl⟩
  · filter_upwards [hs.eventually (by norm_num)] with z hz
    intro g hg h hh
    have hd := hasFDerivAt_coordinateGradient (hz.differentiableAt (by norm_num))
    rw [supporting_vector_eq_gradient hg hd,supporting_vector_eq_gradient hh hd]
  · exact (charts i).common_pairing_near hF (hcorner i)

/-- The original convex two-branch charts produce one actual comparison field
with common support pairing throughout an open neighborhood, rather than only
on the reference compact level. -/
theorem exists_pairwise_structured_field {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀x∈K,F x=ℓ)
    (hstrict : ∀x y : Vec 2,segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x=y)
    (hregular : ∀x∈K,ContDiffAt ℝ 2 F x ∨ ConvexTwoBranchRegularAt F x)
    (hnoncritical : ∀x∈K,¬IsAffineCritical F x) :
    ∃m : ℕ,∃χ : Fin m → Vec 2 → ℝ,∃v : Fin m → ℝ → Vec 2,
      (∀i,ContDiff ℝ ∞ (χ i)) ∧ ∃N : Set (Vec 2),∃η : ℝ,
      0 < η ∧ IsOpen N ∧ K⊆N ∧
      (∀x∈N,∃L : ℝ≥0,∃U∈𝓝 x,LipschitzOnWith L (field hF χ v) U) ∧
      (∀x∈N,∀g∈subdifferential F x,η ≤ dot g (field hF χ v x)) ∧
      (∀x∈N,∀i,ContDiffAt ℝ 1 (v i) (F x)) ∧
      (∀x∈N,ContDiffAt ℝ 2 F x ∨ ∃i,∀ᶠ z in 𝓝 x,field hF χ v z=v i (F z)) ∧
      (∀x∈N,∀g∈subdifferential F x,∀h∈subdifferential F x,
        dot g (field hF χ v x)=dot h (field hF χ v x)) := by
  obtain ⟨m,points,charts,hinj,hpoints,hcover⟩ := exists_finite_convexCornerCharts hF hK hlevel hregular
  have hne : ∀x∈K,DifferentiableAt ℝ F x → coordinateGradient F x≠0 := by
    intro x hx hd hz
    obtain ⟨v,hv⟩ := (equal_rate_exists_iff_not_affineCritical hF x).mpr (hnoncritical x hx)
    have hs := convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hd)
    have he := hv _ hs
    rw [hz] at he
    norm_num [dot] at he
  obtain ⟨χ,hχ,_,_,hfield,hW⟩ := field_from_actual_cornerCharts hF hlevel hstrict hne
    points (fun i => (charts i).toCornerChart) hinj (fun i => (hpoints i).1) hcover
  let v (i : Fin m) : ℝ → Vec 2 := deriv (charts i).curve
  have hv : ∀i,ContDiffAt ℝ 1 (v i) ℓ := by
    intro i
    simpa only [hlevel _ (hpoints i).1] using (charts i).toCornerChart.velocityC1
  obtain ⟨Ns,hNs,hKNs,hstruct⟩ := field_structural_neighborhood hF hlevel hv hfield hcover
  obtain ⟨η,hη,Nv,hNv,hKNv,hvis⟩ := exists_uniform_supports_visibility hF hK hW
  obtain ⟨Nl,hNl,hKNl,hLip⟩ := exists_open_local_lipschitz_extension (fun x hx => (hW x hx).1)
  obtain ⟨Nc,hNc,hKNc,hcommon⟩ := common_pairing_neighborhood hF points charts hfield hcover
  refine ⟨m,χ,v,hχ,(Ns∩Nv∩Nl)∩Nc,η,hη,((hNs.inter hNv).inter hNl).inter hNc,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact ⟨⟨⟨hKNs hx,hKNv hx⟩,hKNl hx⟩,hKNc hx⟩
  · intro x hx
    exact hLip x hx.1.2
  · intro x hx
    exact hvis x hx.1.1.2
  · intro x hx
    exact (hstruct x hx.1.1.1).1
  · intro x hx
    exact (hstruct x hx.1.1.1).2
  · intro x hx
    exact hcommon x hx.2

end BfgsVerification.PlanarAllPairs
