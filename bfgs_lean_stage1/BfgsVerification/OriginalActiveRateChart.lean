import BfgsVerification.ConstantRankObjectiveChart

noncomputable section
open scoped BigOperators Topology ContDiff InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification.ConstantRankFields
open AffineCriticalGeometry AffineCriticalObjective ConvexSubdifferential

theorem dot_constant_on_affineSpan {n m : ℕ} (g : Fin m → Vec n) (v : Vec n) (c : ℝ)
    (hp : ∀i,dot (g i) v=c) {a : Vec n} (ha : a∈affineSpan ℝ (range g)) : dot a v=c := by
  let e : Vec n →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Vec n)).symm.toLinearMap.toAffineMap
  have hm : euclideanVector a∈(affineSpan ℝ (range g)).map e := ⟨a,ha,rfl⟩
  rw [AffineSubspace.map_span,← Set.range_comp] at hm
  have hh := affine_pairing_of_constant (fun i => euclideanVector (g i)) (euclideanVector v) c
    (fun i => (euclidean_pairing_eq_dot _ _).trans (hp i)) (euclideanVector a) hm
  exact (euclidean_pairing_eq_dot _ _).symm.trans hh

theorem support_pairing_of_branch_pairings {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {p v : Vec n}
    (hrep : LocalFiniteMax F f p) (hd : ∀i,DifferentiableAt ℝ (f i) p)
    (hp : ∀i,dot (coordinateGradient (f i) p) v=1) :
    ∀a∈subdifferential F p,dot a v=1 := by
  intro a ha
  have hs := subdifferential_eq_active_convexHull hF hrep
    (fun i => hasFDerivAt_coordinateGradient (hd i))
  rw [hs] at ha
  apply dot_constant_on_affineSpan _ v 1 hp
  apply convexHull_subset_affineSpan _
  apply convexHull_mono (image_subset_range _ _) ha

/-- Source C's fixed family is precisely the original active set I(p).
Nearby active indices are proved to belong to it; no original inactive branch
or locally varying index family is silently substituted. -/
theorem original_active_commonRate_chart {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) (p : Vec n)
    (hrep : LocalFiniteMax F f p) (hf : ∀j,ContDiffAt ℝ 2 (f j) p)
    (hnc : ¬IsAffineCritical F p) (i : Fin (activeIndices F f p).card)
    (hrank : ∀ᶠx in 𝓝 p,
      (differenceMatrix (fun j => coordinateGradient (f (activeIndexMap F f p j)) x) i).rank=
      (differenceMatrix (fun j => coordinateGradient (f (activeIndexMap F f p j)) p) i).rank) :
    ∃U : Set (Vec n),∃v : Vec n → Vec n,IsOpen U ∧ p∈U ∧
      ContDiffOn ℝ 1 v U ∧
      (∀x∈U,∀j∈activeIndices F f p,dot (coordinateGradient (f j) x) (v x)=1) ∧
      (∀x∈U,∀a∈subdifferential F x,dot a (v x)=1) ∧
      (∀x∈U,activeIndices F f x⊆activeIndices F f p ∧ LocalFiniteMax F f x ∧
        ∀j,ContDiffAt ℝ 2 (f j) x) := by
  let b := activeIndexMap F f p
  have hfc : ∀j,ContinuousAt (f j) p := fun j => (hf j).continuousAt
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt hfc hrep
  have hall : ∀j,f (b j) p=F p := by
    intro j
    apply mem_activeIndices.mp
    have hh : b j∈range (activeIndexMap F f p) := mem_range_self j
    rwa [range_activeIndexMap] at hh
  obtain ⟨U,v,hU,hp,hv,hpair,hdata⟩ := active_family_objective_chart hF
    (fun j => f (b j)) p i hr hall (fun j => hf (b j)) hnc hrank
  have hs := activeIndices_eventually_subset (convex_continuous hF).continuousAt hfc hrep
  have hC : ∀ᶠx in 𝓝 p,∀j,ContDiffAt ℝ 2 (f j) x :=
    eventually_all.mpr (fun j => (hf j).eventually (by norm_num))
  obtain ⟨V,hVsub,hV,hpV⟩ := mem_nhds_iff.mp (hs.and (hrep.eventually.and hC))
  refine ⟨U∩V,v,hU.inter hV,⟨hp,hpV⟩,hv.mono inter_subset_left,?_,?_,fun x hx => hVsub hx.2⟩
  · intro x hx j hj
    have hmem : j∈range (activeIndexMap F f p) := by rwa [range_activeIndexMap]
    obtain ⟨q,hq⟩ := hmem
    simpa only [b,hq] using hpair x hx.1 q
  · intro x hx
    exact support_pairing_of_branch_pairings hF (hdata x hx.1).1
      (hdata x hx.1).2 (hpair x hx.1)

end BfgsVerification.ConstantRankFields
