import BfgsVerification.PlanarConvergence

/-! The actual regular-switching premise for nondegenerate planar finite maxima. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Metric
namespace BfgsVerification
namespace PlanarMaxRegular
open ConvexSubdifferential PlanarCornerCharts PlanarCrossing PlanarActiveGeometry
open AffineCriticalObjective HomogeneousPlanar

theorem regular_of_all_active_independent {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {m : ℕ} {f : Fin m → Vec 2 → ℝ} {p : Vec 2} {U : Set (Vec 2)}
    (hU : IsOpen U) (hpU : p∈U) (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hrep : LocalFiniteMax F f p) (hact : ∀ i, f i p=F p)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f i) p))
    (hn : ¬IsAffineCritical F p) : ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p := by
  have hc (i : Fin m) := (hf i).2.contDiffAt (hU.mem_nhds hpU)
  have hs (i : Fin m) : coordinateGradient (f i) p∈subdifferential F p :=
    active_gradient_supports hF hrep (fun i => hasFDerivAt_coordinateGradient ((hc i).differentiableAt (by norm_num)))
      (mem_activeIndices.mpr (hact i))
  have hn' : (0 : Vec 2)∉affineSpan ℝ (range (fun i => coordinateGradient (f i) p)) := by
    intro hz
    apply hn
    apply (isAffineCritical_iff_coordinate_affineSpan F p).mpr
    exact (affineSpan_mono ℝ (by rintro _ ⟨i,rfl⟩; exact hs i)) hz
  have hm := cardinal_le_two_of_affineIndependent_not_critical _ hind hn'
  have hmpos : 0 < m := by
    obtain ⟨i,_⟩ := (hrep.self_of_nhds).1
    exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hcases : m=1 ∨ m=2 := by omega
  rcases hcases with rfl | rfl
  · left
    have he : F =ᶠ[𝓝 p] f 0 := by
      filter_upwards [hrep] with z hz
      obtain ⟨i,hi⟩ := hz.1
      have hi0 : i=0 := Subsingleton.elim _ _
      simpa only [hi0] using hi.symm
    exact (hc 0).congr_of_eventuallyEq he
  · right
    have hd : pairDet (coordinateGradient (f 0) p) (coordinateGradient (f 1) p)≠0 := by
      have hneq : coordinateGradient (f 0) p ≠ coordinateGradient (f 1) p := by
        intro he
        have hi : (0 : Fin 2)=1 := hind.injective he
        norm_num at hi
      have hspan : (![coordinateGradient (f 0) p,coordinateGradient (f 1) p] : Fin 2 → Vec 2) =
          (fun i => coordinateGradient (f i) p) := by
        ext i
        fin_cases i <;> rfl
      exact pairDet_ne_zero_of_not_critical _ _ hneq (by rwa [hspan])
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hrep.and (hU.mem_nhds hpU))
    refine ⟨f,Metric.ball p r,isOpen_ball,Metric.mem_ball_self hr,?_,?_,hact,hd⟩
    · intro i
      exact ⟨(hf i).1.subset (fun z hz => (hball hz).2) (convex_ball p r),
        (hf i).2.mono (fun z hz => (hball hz).2)⟩
    · exact fun z hz => (hball hz).1

/-- No alphabet or switching structure is assumed: active restriction of the
actual finite maximum derives the one- or two-branch alternative at the point. -/
theorem regular_of_finite_max_independent {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {m : ℕ} {f : Fin m → Vec 2 → ℝ} {p : Vec 2} {U : Set (Vec 2)}
    (hU : IsOpen U) (hpU : p∈U) (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hrep : LocalFiniteMax F f p)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f i) p))
    (hn : ¬IsAffineCritical F p) : ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p := by
  let a := activeIndexMap F f p
  have ha : Function.Injective a := ((activeIndices F f p).orderEmbOfFin rfl).injective
  have hc (i : Fin m) := (hf i).2.contDiffAt (hU.mem_nhds hpU)
  apply regular_of_all_active_independent hF hU hpU (fun i => hf (a i))
    (localFiniteMax_restrict_active (convex_continuous hF).continuousAt (fun i => (hc i).continuousAt) hrep) ?_ ?_ hn
  · intro i
    apply mem_activeIndices.mp
    have hi : a i∈range a := mem_range_self i
    rwa [range_activeIndexMap] at hi
  · exact hind.comp_embedding ⟨a,ha⟩

end PlanarMaxRegular
end BfgsVerification
