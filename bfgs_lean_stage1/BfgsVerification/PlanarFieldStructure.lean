import BfgsVerification.PlanarFieldVisibility

/-! A structural neighborhood for the very same field and velocity family
used in C's comparison construction. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification
namespace PlanarObjectiveField
open PlanarCornerCharts ConvexSubdifferential AffineCriticalObjective

/-- The actual field is smooth where the objective is smooth, and locally a
single level-velocity function in corner neighborhoods. This neighborhood
retains the chosen family rather than selecting another existential field. -/
theorem field_structural_neighborhood {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec 2)} {ℓ : ℝ} (hlevel : ∀ x ∈ K, F x=ℓ)
    {m : ℕ} {points : Fin m → Vec 2} {v : Fin m → ℝ → Vec 2} {W : Vec 2 → Vec 2}
    (hv : ∀ i, ContDiffAt ℝ 1 (v i) ℓ)
    (hcorner : ∀ i, ∀ᶠ z in 𝓝 (points i), W z=v i (F z))
    (hcover : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ∃ i, x=points i) :
    ∃ N : Set (Vec 2), IsOpen N ∧ K ⊆ N ∧
      ∀ x ∈ N, (∀ i, ContDiffAt ℝ 1 (v i) (F x)) ∧
        (ContDiffAt ℝ 2 F x ∨ ∃ i, ∀ᶠ z in 𝓝 x, W z=v i (F z)) := by
  let P (x : Vec 2) : Prop := (∀ i, ContDiffAt ℝ 1 (v i) (F x)) ∧
    (ContDiffAt ℝ 2 F x ∨ ∃ i, ∀ᶠ z in 𝓝 x, W z=v i (F z))
  refine ⟨interior {x | P x},isOpen_interior,?_,?_⟩
  swap
  · intro x hx
    exact (interior_subset : interior {x | P x} ⊆ {x | P x}) hx
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  have hvnear : ∀ᶠ z in 𝓝 x, ∀ i, ContDiffAt ℝ 1 (v i) (F z) := by
    apply eventually_all.mpr
    intro i
    have hc : Tendsto F (𝓝 x) (𝓝 ℓ) := by
      simpa only [hlevel x hx] using (convex_continuous hF).continuousAt.tendsto (x := x)
    exact hc.eventually ((hv i).eventually (by norm_num))
  rcases hcover x hx with hs | ⟨i,rfl⟩
  · filter_upwards [hvnear,hs.eventually (by norm_num)] with z hz hzs
    exact ⟨hz,Or.inl hzs⟩
  · filter_upwards [hvnear,(hcorner i).eventually_nhds] with z hz hzc
    exact ⟨hz,Or.inr ⟨i,hzc⟩⟩

/-- One actual cutoff and velocity family simultaneously has visibility,
local Lipschitz regularity, the smooth/corner structural formula, and common
support pairing on the compact level. All data are derived from the objective. -/
theorem exists_structured_visible_comparison_field {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ TwoBranchRegularAt F x)
    (hnoncritical : ∀ x ∈ K, ¬IsAffineCritical F x) :
    ∃ m : ℕ, ∃ χ : Fin m → Vec 2 → ℝ, ∃ v : Fin m → ℝ → Vec 2,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      ∃ N : Set (Vec 2), ∃ η : ℝ, 0<η ∧ IsOpen N ∧ K ⊆ N ∧
        (∀ x ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (field hF χ v) U) ∧
        (∀ x ∈ N, ∀ g ∈ subdifferential F x, η ≤ dot g (field hF χ v x)) ∧
        (∀ x ∈ N, ∀ i, ContDiffAt ℝ 1 (v i) (F x)) ∧
        (∀ x ∈ N, ContDiffAt ℝ 2 F x ∨ ∃ i,
          ∀ᶠ z in 𝓝 x, field hF χ v z=v i (F z)) ∧
        (∀ x ∈ K, ∀ g ∈ subdifferential F x, ∀ h ∈ subdifferential F x,
          dot g (field hF χ v x)=dot h (field hF χ v x)) := by
  obtain ⟨m,points,charts,hinj,hpoints,hcover⟩ := exists_finite_cornerCharts hF hK hlevel hregular
  have hne : ∀ x ∈ K, DifferentiableAt ℝ F x → coordinateGradient F x ≠ 0 := by
    intro x hx hd hz
    obtain ⟨v,hv⟩ := (equal_rate_exists_iff_not_affineCritical hF x).mpr (hnoncritical x hx)
    have hs := convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hd)
    have he := hv _ hs
    rw [hz] at he
    norm_num [dot] at he
  obtain ⟨χ,hχ,_,_,hfield,hW⟩ := field_from_actual_cornerCharts hF hlevel hstrict hne
    points charts hinj (fun i => (hpoints i).1) hcover
  let v (i : Fin m) : ℝ → Vec 2 := deriv (charts i).curve
  have hv : ∀ i, ContDiffAt ℝ 1 (v i) ℓ := by
    intro i
    simpa only [hlevel _ (hpoints i).1] using (charts i).velocityC1
  obtain ⟨Ns,hNs,hKNs,hstruct⟩ := field_structural_neighborhood hF hlevel hv hfield hcover
  obtain ⟨η,hη,Nv,hNv,hKNv,hvis⟩ := exists_uniform_supports_visibility hF hK hW
  obtain ⟨Nl,hNl,hKNl,hLip⟩ := exists_open_local_lipschitz_extension (fun x hx => (hW x hx).1)
  refine ⟨m,χ,v,hχ,Ns∩Nv∩Nl,η,hη,(hNs.inter hNv).inter hNl,?_,?_,?_,?_,?_,?_⟩
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
  · exact common_pairing_from_actual_cornerCharts hF points charts
      (fun i => (hfield i).self_of_nhds) hcover

/-- The finitely many actual level-velocity derivatives have one Euclidean
bound on a compact structural buffer, derived from their actual C1 regularity. -/
theorem compact_velocity_derivative_bound {F : Vec 2 → ℝ} (hF : Continuous F)
    {m : ℕ} {v : Fin m → ℝ → Vec 2} {Q : Set (Vec 2)} (hQ : IsCompact Q)
    (hv : ∀ x ∈ Q, ∀ i, ContDiffAt ℝ 1 (v i) (F x)) :
    ∃ A : ℝ, 0<A ∧ ∀ x ∈ Q, ∀ i, ‖euclideanVector (deriv (v i) (F x))‖ ≤ A := by
  have hc (i : Fin m) : ContinuousOn (fun x => ‖euclideanVector (deriv (v i) (F x))‖) Q := by
    intro x hx
    have hd : ContinuousAt (deriv (v i)) (F x) := by
      change ContinuousAt (fun t => (fderiv ℝ (v i) t) 1) (F x)
      have hf := ((hv x hx i).fderiv_right (m := 0) (by norm_num)).continuousAt
      exact (show Continuous (fun L : ℝ →L[ℝ] Vec 2 => L 1) from
        continuous_id.clm_apply continuous_const).continuousAt.comp hf
    have he : Continuous (euclideanVector : Vec 2 → EuclideanSpace ℝ (Fin 2)) :=
      PiLp.continuous_equiv_symm _ _
    have hcom : ContinuousAt (fun q => deriv (v i) (F q)) x :=
      hd.comp (f := F) hF.continuousAt
    exact (he.continuousAt.comp (f := fun q => deriv (v i) (F q)) hcom).norm.continuousWithinAt
  have hsum : ContinuousOn (fun x => ∑ i : Fin m, ‖euclideanVector (deriv (v i) (F x))‖) Q :=
    continuousOn_finset_sum _ (fun i _ => hc i)
  obtain ⟨B,hB⟩ := hQ.bddAbove_image hsum
  refine ⟨|B|+1,by positivity,?_⟩
  intro x hx i
  calc
    ‖euclideanVector (deriv (v i) (F x))‖ ≤ ∑ j : Fin m, ‖euclideanVector (deriv (v j) (F x))‖ :=
      Finset.single_le_sum (f := fun j => ‖euclideanVector (deriv (v j) (F x))‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ B := hB ⟨x,hx,rfl⟩
    _ ≤ |B|+1 := by linarith [le_abs_self B]

end PlanarObjectiveField
end BfgsVerification
