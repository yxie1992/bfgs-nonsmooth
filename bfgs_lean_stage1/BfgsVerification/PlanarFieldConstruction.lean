import BfgsVerification.PlanarActualCorners

/-! Construction of the actual locally Lipschitz comparison field around a
compact regular planar level. Its finite cutoffs and corner velocities are
obtained from the original objective data. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Function
namespace BfgsVerification
namespace PlanarObjectiveField
open ConvexSubdifferential PlanarNormalGeometry PlanarCornerCharts AffineCriticalObjective

/-- A finite actual corner family supplies a single joined field, positive
against every actual support on the whole compact level. -/
theorem field_from_actual_cornerCharts {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec 2)} {ℓ : ℝ} (hlevel : ∀ x ∈ K, F x=ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hne : ∀ x ∈ K, DifferentiableAt ℝ F x → coordinateGradient F x ≠ 0)
    {m : ℕ} (points : Fin m → Vec 2) (charts : ∀ i, CornerChart F (points i))
    (hinj : Function.Injective points) (hpoint : ∀ i, points i ∈ K)
    (hcover : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ∃ i, x=points i) :
    ∃ χ : Fin m → Vec 2 → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i w, χ i w ∈ Icc (0 : ℝ) 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ i, ∀ᶠ z in 𝓝 (points i),
        field hF χ (fun j => deriv (charts j).curve) z = deriv (charts i).curve (F z)) ∧
      ∀ x ∈ K,
        (∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (field hF χ (fun j => deriv (charts j).curve)) U) ∧
        (∀ g ∈ subdifferential F x, 0 < dot g (field hF χ (fun j => deriv (charts j).curve) x)) := by
  let a (i : Fin m) : Vec 2 := coordinateGradient ((charts i).branches 0) (points i)
  let b (i : Fin m) : Vec 2 := coordinateGradient ((charts i).branches 1) (points i)
  let v (i : Fin m) : ℝ → Vec 2 := deriv (charts i).curve
  have hv (i : Fin m) : ContDiffAt ℝ 1 (v i) ℓ := by
    simpa only [hlevel _ (hpoint i)] using (charts i).velocityC1
  have hva (i : Fin m) : dot (a i) (v i ℓ)=1 := by
    simpa only [hlevel _ (hpoint i)] using (charts i).commonRate 0
  have hvb (i : Fin m) : dot (b i) (v i ℓ)=1 := by
    simpa only [hlevel _ (hpoint i)] using (charts i).commonRate 1
  have hdis : Pairwise (fun i j => Disjoint (normalSector (a i) (b i)) (normalSector (a j) (b j))) := by
    intro i j hij
    apply normalSectors_disjoint hF (fun he => hij (hinj he))
      ((hlevel _ (hpoint i)).trans (hlevel _ (hpoint j)).symm)
      (by simpa only [hlevel _ (hpoint i)] using hstrict)
      ((charts i).supports hF 0) ((charts i).supports hF 1)
      ((charts j).supports hF 0) ((charts j).supports hF 1)
      (hva i) (hvb i) (hva j) (hvb j)
  obtain ⟨χ,η,hχ,hη,hrange,hd,hnear⟩ := exists_moving_normalSector_cutoffs
    (fun i _ => a i) (fun i _ => b i) v ℓ
    (fun _ => continuousAt_const) (fun _ => continuousAt_const)
    (fun i => (hv i).continuousAt) hva hvb hdis
  have hsupp : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))) :=
    fun i j hij => (hd hij).mono subset_closure subset_closure
  have hplateau (i : Fin m) : ∀ᶠ w in 𝓝ˢ (normalSector (a i) (b i)), χ i w=1 :=
    mem_nhdsSet_iff_forall.mpr ((hnear.self_of_nhds i).1)
  have hfield (i : Fin m) : ∀ᶠ z in 𝓝 (points i), field hF χ v z=v i (F z) := by
    apply field_eventually_eq_corner_velocity hF (charts i).localMax (charts i).hasGradient
      (charts i).active (charts i).commonRate v hsupp (hplateau i)
  refine ⟨χ,hχ,hrange,hd,hfield,?_⟩
  intro x hx
  rcases hcover x hx with hs | ⟨i,rfl⟩
  · have hg := hasFDerivAt_coordinateGradient (hs.differentiableAt (by norm_num))
    have hg0 := hne x hx (hs.differentiableAt (by norm_num))
    have hvc (j : Fin m) : ContDiffAt ℝ 1 (v j) (F x) := by rw [hlevel x hx]; exact hv j
    refine ⟨(field_contDiffAt_smooth hF hχ hvc hs hg0).exists_lipschitzOnWith,?_⟩
    intro g hgmem
    have he := supporting_vector_eq_gradient hgmem hg
    subst g
    rw [field_gradient_pairing hF χ v hg hg0]
    apply mul_pos
    · apply norm_pos_iff.mpr
      intro he
      exact hg0 (congrArg (fun w : EuclideanSpace ℝ (Fin 2) => fun i => w i) he)
    · apply PlanarAmbientFrame.height_pos _ hrange hsupp
      intro j hj
      have hh := (hnear.self_of_nhds j).2 (normalized (coordinateGradient F x))
        (normalized_sqNorm hg0).le hj
      rw [hlevel x hx]
      exact (hη j).trans_le hh
  · refine ⟨lipschitz_near_of_eq_level_velocity hF (charts i).velocityC1 (hfield i),?_⟩
    intro g hg
    have he := field_supports_pairing_corner hF (charts i).localMax (charts i).hasGradient
      (charts i).active (charts i).commonRate v hsupp (hplateau i) rfl g hg
    rw [he]
    norm_num

/-- On the base level, all actual supports have the same pairing with the
constructed field. This identity, stronger than positivity, is needed for C's
endpoint transversality contradiction. -/
theorem common_pairing_from_actual_cornerCharts {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec 2)} {m : ℕ} (points : Fin m → Vec 2)
    (charts : ∀ i, CornerChart F (points i)) {W : Vec 2 → Vec 2}
    (hfield : ∀ i, W (points i)=deriv (charts i).curve (F (points i)))
    (hcover : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ∃ i, x=points i) :
    ∀ x ∈ K, ∀ g ∈ subdifferential F x, ∀ h ∈ subdifferential F x,
      dot g (W x)=dot h (W x) := by
  intro x hx g hg h hh
  rcases hcover x hx with hs | ⟨i,rfl⟩
  · have hd := hasFDerivAt_coordinateGradient (hs.differentiableAt (by norm_num))
    rw [supporting_vector_eq_gradient hg hd,supporting_vector_eq_gradient hh hd]
  · rw [hfield i]
    rw [two_branch_support_pairing hF (charts i).localMax (charts i).hasGradient
      (charts i).active (charts i).commonRate g hg,
      two_branch_support_pairing hF (charts i).localMax (charts i).hasGradient
      (charts i).active (charts i).commonRate h hh]

/-- The compact-level field is derived entirely from the actual objective's
regularity and strict contour hypotheses. No field, cutoff, finite corner list,
angle selection or velocity regularity is supplied as a premise. -/
theorem exists_comparison_field_on_compact_level {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ TwoBranchRegularAt F x)
    (hnoncritical : ∀ x ∈ K, ¬IsAffineCritical F x) :
    ∃ W : Vec 2 → Vec 2, ∀ x ∈ K,
      (∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U) ∧
      (∀ g ∈ subdifferential F x, 0 < dot g (W x)) ∧
      (∀ g ∈ subdifferential F x, ∀ h ∈ subdifferential F x, dot g (W x)=dot h (W x)) := by
  obtain ⟨m,points,charts,hinj,hpoints,hcover⟩ := exists_finite_cornerCharts hF hK hlevel hregular
  have hne : ∀ x ∈ K, DifferentiableAt ℝ F x → coordinateGradient F x ≠ 0 := by
    intro x hx hd hz
    obtain ⟨v,hv⟩ := (equal_rate_exists_iff_not_affineCritical hF x).mpr (hnoncritical x hx)
    have hs := convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hd)
    have he := hv _ hs
    rw [hz] at he
    norm_num [dot] at he
  obtain ⟨χ,_,_,_,hfield,hW⟩ := field_from_actual_cornerCharts hF hlevel hstrict hne
    points charts hinj (fun i => (hpoints i).1) hcover
  refine ⟨field hF χ (fun j => deriv (charts j).curve),?_⟩
  intro x hx
  exact ⟨(hW x hx).1,(hW x hx).2,
    common_pairing_from_actual_cornerCharts hF points charts
      (fun i => (hfield i).self_of_nhds) hcover x hx⟩

end PlanarObjectiveField
end BfgsVerification
