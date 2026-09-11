import BfgsVerification.AffineDistanceContinuity
import BfgsVerification.FiniteMaxLocalCorrectness
import Mathlib.Topology.Semicontinuous

/-! Local lower semicontinuity of the actual affine-subdifferential distance.
Active sets can shrink nearby; the proved fixed-subfamily continuity controls
all of their finitely many possibilities. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification
namespace AffineDistance
open AffineBarycentric AffineCriticalObjective ConvexSubdifferential

def subfamilyDistance {n m : ℕ} (g : Fin m → Vec n) (J : Finset (Fin m)) : ℝ :=
  Metric.infDist (0 : EuclideanSpace ℝ (Fin n))
    (affineSpan ℝ (euclideanVector '' (g '' (J : Set (Fin m)))) : Set _)

def objectiveDistance {n : ℕ} (F : Vec n → ℝ) (p : Vec n) : ℝ :=
  Metric.infDist (0 : EuclideanSpace ℝ (Fin n))
    (affineSpan ℝ (range (subgradientFamily F p)) : Set _)

theorem subfamilyDistance_continuousAt {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (x : X) (J : Finset (Fin m)) (hJ : J.Nonempty)
    (hc : ∀ j, ContinuousAt (fun p => g p j) x) (hg : AffineIndependent ℝ (g x)) :
    ContinuousAt (fun p => subfamilyDistance (g p) J) x := by
  let e : Fin J.card → Fin m := J.orderEmbOfFin rfl
  have hi : Function.Injective e := (J.orderEmbOfFin rfl).injective
  have hr : range e = (J : Set (Fin m)) := Finset.range_orderEmbOfFin J rfl
  have he (p : X) : range (fun j => euclideanVector (g p (e j))) =
      euclideanVector '' (g p '' (J : Set (Fin m))) := by
    rw [← hr]
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨g p (e j),⟨e j,⟨j,rfl⟩,rfl⟩,rfl⟩
    · rintro ⟨u,⟨k,⟨j,rfl⟩,rfl⟩,rfl⟩
      exact ⟨j,rfl⟩
  have ht := affine_distance_continuousAt (fun p j => g p (e j)) x
    (⟨0, Finset.card_pos.mpr hJ⟩ : Fin J.card) (fun j => hc (e j)) (hg.comp_embedding ⟨e,hi⟩)
  simp_rw [he] at ht
  exact ht

theorem subfamilyDistance_antitone {n m : ℕ} (g : Fin m → Vec n)
    {J K : Finset (Fin m)} (hJ : J.Nonempty) (hJK : J ⊆ K) :
    subfamilyDistance g K ≤ subfamilyDistance g J := by
  apply Metric.infDist_le_infDist_of_subset
  · exact affineSpan_mono ℝ (image_mono (image_mono hJK))
  · obtain ⟨i,hi⟩ := hJ
    exact ⟨euclideanVector (g i), subset_affineSpan ℝ _ ⟨g i,⟨i,hi,rfl⟩,rfl⟩⟩

theorem active_subfamily_lowerSemicontinuousAt {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (J : X → Finset (Fin m)) (x : X)
    (hc : ∀ j, ContinuousAt (fun p => g p j) x) (hg : AffineIndependent ℝ (g x))
    (hJ : ∀ᶠ p in 𝓝 x, (J p).Nonempty ∧ J p ⊆ J x) :
    LowerSemicontinuousAt (fun p => subfamilyDistance (g p) (J p)) x := by
  intro a ha
  have he (K : Finset (Fin m)) : ∀ᶠ p in 𝓝 x,
      K.Nonempty → K ⊆ J x → a < subfamilyDistance (g p) K := by
    by_cases hK : K.Nonempty ∧ K ⊆ J x
    · have hlt := ha.trans_le (subfamilyDistance_antitone (g x) hK.1 hK.2)
      exact ((subfamilyDistance_continuousAt g x K hK.1 hc hg).eventually
        (lt_mem_nhds hlt)).mono (fun _ hp _ _ => hp)
    · exact Eventually.of_forall (fun _ h1 h2 => (hK ⟨h1,h2⟩).elim)
  filter_upwards [eventually_all.mpr he, hJ] with p hp hJp
  exact hp (J p) hJp.1 hJp.2

theorem objectiveDistance_eq_active {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {p : Vec n} {g : Fin m → Vec n}
    (hrep : LocalFiniteMax F f p)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) p) :
    objectiveDistance F p = subfamilyDistance g (activeIndices F f p) := by
  unfold objectiveDistance subfamilyDistance
  rw [affineSpan_subgradientFamily_of_convexHull p _ (subdifferential_eq_active_convexHull hF hrep hg)]

theorem objectiveDistance_lowerSemicontinuousAt {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ}
    (g : Vec n → Fin m → Vec n) (x : Vec n)
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ᶠ p in 𝓝 x, ∀ i, HasFDerivAt (f i) (gradientFunctional (g p i)) p)
    (hc : ∀ i, ContinuousAt (fun p => g p i) x)
    (hind : AffineIndependent ℝ (g x)) : LowerSemicontinuousAt (objectiveDistance F) x := by
  have hsub := activeIndices_eventually_subset (convex_continuous hF).continuousAt
    (fun i => (hg.self_of_nhds i).continuousAt) hrep
  have hJ : ∀ᶠ p in 𝓝 x, (activeIndices F f p).Nonempty ∧ activeIndices F f p ⊆ activeIndices F f x := by
    filter_upwards [hrep.eventually, hsub] with p hp hs
    exact ⟨activeIndices_nonempty hp,hs⟩
  have hl := active_subfamily_lowerSemicontinuousAt g (activeIndices F f) x hc hind hJ
  have he : ∀ᶠ p in 𝓝 x, objectiveDistance F p=subfamilyDistance (g p) (activeIndices F f p) := by
    filter_upwards [hrep.eventually,hg] with p hp hgp
    exact objectiveDistance_eq_active hF hp hgp
  intro a ha
  rw [he.self_of_nhds] at ha
  filter_upwards [hl a ha,he] with p hp hep
  rwa [hep]

end AffineDistance
end BfgsVerification
