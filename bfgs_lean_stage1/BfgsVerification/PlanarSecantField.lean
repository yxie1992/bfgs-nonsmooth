import BfgsVerification.PlanarCompactSecant
import BfgsVerification.PlanarRunTransport

/-! The same actual field simultaneously carries all transport geometry and
uniform local secant correction estimates from the source convex C² charts. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification
namespace PlanarObjectiveField
open PlanarCornerCharts ConvexSubdifferential AffineCriticalObjective

theorem exists_secant_structured_visible_field {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ConvexTwoBranchRegularAt F x)
    (hnoncritical : ∀ x ∈ K, ¬IsAffineCritical F x) {σ : ℝ} (hσ : 0<σ) :
    ∃ m : ℕ, ∃ χ : Fin m → Vec 2 → ℝ, ∃ v : Fin m → ℝ → Vec 2,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      ∃ N : Set (Vec 2), ∃ η : ℝ, 0<η ∧ IsOpen N ∧ K ⊆ N ∧
        (∀ x ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (field hF χ v) U) ∧
        (∀ x ∈ N, ∀ g ∈ subdifferential F x, η ≤ dot g (field hF χ v x)) ∧
        (∀ x ∈ N, ∀ i, ContDiffAt ℝ 1 (v i) (F x)) ∧
        (∀ x ∈ N, ContDiffAt ℝ 2 F x ∨ ∃ i,
          ∀ᶠ z in 𝓝 x, field hF χ v z=v i (F z)) ∧
        (∀ x ∈ K, ∀ g ∈ subdifferential F x, ∀ h ∈ subdifferential F x,
          dot g (field hF χ v x)=dot h (field hF χ v x)) ∧
        (∀ p∈K, PlanarCrossing.LocalSecantControl F (field hF χ v) σ p) := by
  obtain ⟨m,points,charts,hinj,hpoints,hcover⟩ := exists_finite_convexCornerCharts hF hK hlevel hregular
  have hne : ∀ x ∈ K, DifferentiableAt ℝ F x → coordinateGradient F x ≠ 0 := by
    intro x hx hd hz
    obtain ⟨v,hv⟩ := (equal_rate_exists_iff_not_affineCritical hF x).mpr (hnoncritical x hx)
    have hs := convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hd)
    have he := hv _ hs
    rw [hz] at he
    norm_num [dot] at he
  obtain ⟨χ,hχ,_,_,hfield,hW⟩ := field_from_actual_cornerCharts hF hlevel hstrict hne
    points (fun i => (charts i).toCornerChart) hinj (fun i => (hpoints i).1) hcover
  let v (i : Fin m) : ℝ → Vec 2 := deriv (charts i).curve
  have hv : ∀ i, ContDiffAt ℝ 1 (v i) ℓ := by
    intro i
    simpa only [hlevel _ (hpoints i).1] using (charts i).toCornerChart.velocityC1
  obtain ⟨Ns,hNs,hKNs,hstruct⟩ := field_structural_neighborhood hF hlevel hv hfield hcover
  obtain ⟨η,hη,Nv,hNv,hKNv,hvis⟩ := exists_uniform_supports_visibility hF hK hW
  obtain ⟨Nl,hNl,hKNl,hLip⟩ := exists_open_local_lipschitz_extension (fun x hx => (hW x hx).1)
  refine ⟨m,χ,v,hχ,Ns∩Nv∩Nl,η,hη,(hNs.inter hNv).inter hNl,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact ⟨⟨hKNs hx,hKNv hx⟩,hKNl hx⟩
  · intro x hx
    exact hLip x hx.2
  · intro x hx
    exact hvis x hx.1.2
  · intro x hx
    exact (hstruct x hx.1.1).1
  · intro x hx
    exact (hstruct x hx.1.1).2
  · exact common_pairing_from_actual_cornerCharts hF points (fun i => (charts i).toCornerChart)
      (fun i => (hfield i).self_of_nhds) hcover

  · intro p hp
    rcases hcover p hp with hs | ⟨i,rfl⟩
    · exact PlanarCrossing.localSecantControl_of_smooth hF hs (hW p hp).1 σ
    · exact PlanarCrossing.localSecantControl_of_corner hF (charts i) (hfield i)
        (hW _ hp).1 hσ

end PlanarObjectiveField
end BfgsVerification
