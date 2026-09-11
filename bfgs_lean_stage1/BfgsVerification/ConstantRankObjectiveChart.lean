import BfgsVerification.ConstantRankLocalField
import BfgsVerification.PlanarActiveGeometry

noncomputable section
open scoped BigOperators Topology ContDiff InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification.ConstantRankFields
open AffineCriticalGeometry AffineCriticalObjective ConvexSubdifferential

def commonRateVector {n m : ℕ} (g : Fin m → Vec n) (i : Fin m) : Vec n :=
  fun j => commonRate g i j

theorem coordinateGradient_contDiffAt {n : ℕ} {f : Vec n → ℝ} {p : Vec n}
    (hf : ContDiffAt ℝ 2 f p) : ContDiffAt ℝ 1 (coordinateGradient f) p := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) p := hf.fderiv_right (by norm_num)
  apply contDiffAt_pi.mpr
  intro i
  exact hd.clm_apply contDiffAt_const

theorem commonRateVector_chart {d n m : ℕ} (g : Vec d → Fin m → Vec n)
    (p : Vec d) (i : Fin m)
    (hc : ∀j,ContDiffAt ℝ 1 (fun x => g x j) p)
    (hrank : ∀ᶠx in 𝓝 p,(differenceMatrix (g x) i).rank=(differenceMatrix (g p) i).rank)
    (hzero : (0 : EuclideanSpace ℝ (Fin n))∉affineSpan ℝ (range (fun j => euclideanVector (g p j)))) :
    ∃U : Set (Vec d),IsOpen U ∧ p∈U ∧
      ContDiffOn ℝ 1 (fun x => commonRateVector (g x) i) U ∧
      ∀x∈U,∀j,dot (g x j) (commonRateVector (g x) i)=1 := by
  obtain ⟨U,hU,hp,hc,hpair⟩ := commonRate_chart g p i hc hrank hzero
  have heuc : ContDiff ℝ 1 (fun v : EuclideanSpace ℝ (Fin n) => fun j => v j) :=
    (WithLp.linearEquiv 2 ℝ (Vec n)).toContinuousLinearEquiv.contDiff
  refine ⟨U,hU,hp,heuc.comp_contDiffOn hc,?_⟩
  intro x hx j
  have h := hpair x hx j
  change ⟪euclideanVector (g x j),euclideanVector (commonRateVector (g x) i)⟫_ℝ=1 at h
  rwa [euclidean_pairing_eq_dot] at h

/-- A locally represented family active at the base supplies the actual
non-affine-criticality premise of the canonical common-rate construction. -/
theorem affine_zero_excluded_of_active_family {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) (p : Vec n)
    (hrep : LocalFiniteMax F f p) (hall : ∀i,f i p=F p)
    (hd : ∀i,DifferentiableAt ℝ (f i) p) (hnc : ¬IsAffineCritical F p) :
    (0 : EuclideanSpace ℝ (Fin n))∉affineSpan ℝ
      (range (fun i => euclideanVector (coordinateGradient (f i) p))) := by
  have ha : activeIndices F f p=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact mem_activeIndices.mpr (hall i)
  have hs := subdifferential_eq_active_convexHull hF hrep
    (fun i => hasFDerivAt_coordinateGradient (hd i))
  rw [ha,Finset.coe_univ,Set.image_univ] at hs
  have he := affineSpan_subgradientFamily_of_convexHull p
    (range (fun i => coordinateGradient (f i) p)) hs
  intro hz
  apply hnc
  change (0 : EuclideanSpace ℝ (Fin n))∈affineSpan ℝ (range (subgradientFamily F p))
  rw [he,← Set.range_comp]
  exact hz

/-- The literal local C construction for an actual finite C2 maximum with
all represented branches active at the base. C2 gives C1 regularity of v. -/
theorem active_family_objective_chart {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) (p : Vec n)
    (i : Fin m) (hrep : LocalFiniteMax F f p) (hall : ∀j,f j p=F p)
    (hf : ∀j,ContDiffAt ℝ 2 (f j) p) (hnc : ¬IsAffineCritical F p)
    (hrank : ∀ᶠx in 𝓝 p,
      (differenceMatrix (fun j => coordinateGradient (f j) x) i).rank=
        (differenceMatrix (fun j => coordinateGradient (f j) p) i).rank) :
    ∃U : Set (Vec n),∃v : Vec n → Vec n,IsOpen U ∧ p∈U ∧
      ContDiffOn ℝ 1 v U ∧
      (∀x∈U,∀j,dot (coordinateGradient (f j) x) (v x)=1) ∧
      (∀x∈U,LocalFiniteMax F f x ∧ ∀j,DifferentiableAt ℝ (f j) x) := by
  have hz := affine_zero_excluded_of_active_family hF f p hrep hall
    (fun j => (hf j).differentiableAt (by norm_num)) hnc
  obtain ⟨U,hU,hp,hc,hpair⟩ := commonRateVector_chart
    (fun x j => coordinateGradient (f j) x) p i
    (fun j => coordinateGradient_contDiffAt (hf j)) hrank hz
  have hd : ∀ᶠx in 𝓝 p,∀j,DifferentiableAt ℝ (f j) x := by
    apply eventually_all.mpr
    intro j
    exact ((hf j).eventually (by norm_num)).mono fun x hx => hx.differentiableAt (by norm_num)
  obtain ⟨V,hVsub,hV,hpV⟩ := mem_nhds_iff.mp (hrep.eventually.and hd)
  exact ⟨U∩V,fun x => commonRateVector (fun j => coordinateGradient (f j) x) i,
    hU.inter hV,⟨hp,hpV⟩,hc.mono inter_subset_left,
    fun x hx => hpair x hx.1,fun x hx => hVsub hx.2⟩

end BfgsVerification.ConstantRankFields
