import BfgsVerification.PlanarFieldVisibility
import BfgsVerification.CenteredLocalUniform

/-! Compact buffers and uniform actual field bounds in Module C. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Metric
namespace BfgsVerification
namespace PlanarObjectiveField
open ConvexSubdifferential PlanarCornerCharts AffineCriticalObjective

/-- A smaller open neighborhood has compact closure in the field's regularity
region, and one Lipschitz radius/constant works on full balls around that compact
buffer. This supplies actual derivative bounds wherever a derivative is used. -/
theorem exists_compact_uniform_field_buffer {n : ℕ} {W : Vec n → Vec n}
    {K N : Set (Vec n)} (hK : IsCompact K) (hN : IsOpen N) (hKN : K ⊆ N)
    (hLip : ∀ p ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith L W U) :
    ∃ V Q : Set (Vec n), IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Q ∧ IsCompact Q ∧ Q ⊆ N ∧
      ∃ M : ℝ≥0, ∃ ρ : ℝ, 0<ρ ∧ ∃ G : ℝ, 0<G ∧
        (∀ p ∈ Q, ball p ρ ⊆ N ∧ LipschitzOnWith M W (ball p ρ)) ∧
        (∀ p ∈ Q, sqNorm (W p)≤G^2) ∧ (∀ p ∈ Q, ‖fderiv ℝ W p‖≤M) := by
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hN hKN
  let Q := cthickening δ K
  let V := thickening (δ/2) K
  have hQ : IsCompact Q := hK.cthickening
  have hVQ : closure V ⊆ Q := (closure_thickening_subset_cthickening (δ/2) K).trans
    (cthickening_mono (by linarith : δ/2≤δ) K)
  have hLoc : LocallyLipschitzOn N W := by
    intro p hp
    obtain ⟨L,U,hU,hLU⟩ := hLip p hp
    exact ⟨L,U,mem_nhdsWithin_of_mem_nhds hU,hLU⟩
  obtain ⟨M,ρ,hρ,hballs⟩ := CenteredSmoothSublinear.compact_uniform_local_lipschitz hN hQ hsub hLoc
  have hc : ContinuousOn (fun p => sqNorm (W p)) Q :=
    continuous_sqNorm.comp_continuousOn (hLoc.continuousOn.mono hsub)
  obtain ⟨B,hB⟩ := hQ.bddAbove_image hc
  let G := Real.sqrt (|B|+1)
  have hG : 0<G := Real.sqrt_pos.mpr (by positivity)
  refine ⟨V,Q,isOpen_thickening,self_subset_thickening (by linarith) K,hVQ,hQ,hsub,M,ρ,hρ,G,hG,hballs,?_,?_⟩
  · intro p hp
    rw [Real.sq_sqrt (by positivity : 0≤|B|+1)]
    exact (hB ⟨p,hp,rfl⟩).trans (by linarith [le_abs_self B])
  · intro p hp
    exact norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds p hρ) (hballs p hp).2

/-- Source-level field construction with a compact buffered neighborhood and
actual uniform field, close-pair Lipschitz and derivative bounds. -/
theorem exists_buffered_visible_comparison_field {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ TwoBranchRegularAt F x)
    (hnoncritical : ∀ x ∈ K, ¬IsAffineCritical F x) :
    ∃ W : Vec 2 → Vec 2, ∃ V Q N : Set (Vec 2), IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Q ∧
      IsCompact Q ∧ Q ⊆ N ∧ IsOpen N ∧
      ∃ η : ℝ, 0<η ∧ ∃ M : ℝ≥0, ∃ ρ : ℝ, 0<ρ ∧ ∃ G : ℝ, 0<G ∧
        (∀ p ∈ Q, ball p ρ ⊆ N ∧ LipschitzOnWith M W (ball p ρ)) ∧
        (∀ p ∈ Q, sqNorm (W p)≤G^2) ∧ (∀ p ∈ Q, ‖fderiv ℝ W p‖≤M) ∧
        (∀ p ∈ N, ∀ g ∈ subdifferential F p, η≤dot g (W p)) ∧
        (∀ p ∈ K, ∀ g ∈ subdifferential F p, ∀ h ∈ subdifferential F p, dot g (W p)=dot h (W p)) := by
  obtain ⟨W,hcommon,η,hη,N,hN,hKN,hLip,hvis⟩ :=
    exists_visible_comparison_field_on_compact_level hF hK hlevel hstrict hregular hnoncritical
  obtain ⟨V,Q,hV,hKV,hVQ,hQ,hQN,M,ρ,hρ,G,hG,hballs,hbound,hderiv⟩ :=
    exists_compact_uniform_field_buffer hK hN hKN hLip
  exact ⟨W,V,Q,N,hV,hKV,hVQ,hQ,hQN,hN,η,hη,M,ρ,hρ,G,hG,hballs,hbound,hderiv,hvis,hcommon⟩

end PlanarObjectiveField
end BfgsVerification
