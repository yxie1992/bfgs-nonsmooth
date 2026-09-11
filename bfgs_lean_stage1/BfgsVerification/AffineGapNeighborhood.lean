import BfgsVerification.AffineGapCompact
import BfgsVerification.PlanarActiveGeometry

/-! The source's nondegenerate finite C¹ maximum supplies the neighborhood in
which the actual affine gap is lower semicontinuous and positive on compact
positive bands. Originally inactive branches are discarded by proof. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Metric
namespace BfgsVerification
namespace AffineDistance
open AffineBarycentric AffineCriticalObjective ConvexSubdifferential

theorem coordinateGradient_continuousAt_of_contDiffAt {n : ℕ} {f : Vec n → ℝ} {x : Vec n}
    (hf : ContDiffAt ℝ 1 f x) : ContinuousAt (coordinateGradient f) x := by
  have hd : ContDiffAt ℝ 0 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  apply continuousAt_pi.mpr
  intro i
  exact (hd.clm_apply contDiffAt_const).continuousAt

/-- Abstract actual-derivative bridge, with continuity required locally as
provided by C¹ branches. The rank and correctness conclusions are derived. -/
theorem neighborhood_gap_of_positive_barycentric {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ}
    (g : Vec n → Fin m → Vec n) (star : Vec n)
    (hrep : LocalFiniteMax F f star)
    (hg : ∀ᶠ p in 𝓝 star, ∀ i, HasFDerivAt (f i) (gradientFunctional (g p i)) p)
    (hc : ∀ᶠ p in 𝓝 star, ∀ i, ContinuousAt (fun q => g q i) p)
    (hind : AffineIndependent ℝ (g star)) (w : Vec m)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1) (hzero : ∑ i, w i • g star i=0) :
    ∃ V : Set (Vec n), IsOpen V ∧ star∈V ∧
      (∀ p∈V, LowerSemicontinuousAt (objectiveDistance F) p ∧
        (IsAffineCritical F p ↔ ∀ z, F p≤F z)) ∧
      (∀ K : Set (Vec n), IsCompact K → K.Nonempty → K⊆V →
        (∀ p∈K, F star<F p) →
        ∃ p∈K, 0<objectiveDistance F p ∧ ∀ q∈K, objectiveDistance F p≤objectiveDistance F q) := by
  have hb := local_affine_critical_correctness hF g star hrep hg hc.self_of_nhds hind w hw hsum hzero
  have he : ∀ᶠ p in 𝓝 star, LowerSemicontinuousAt (objectiveDistance F) p ∧
      (IsAffineCritical F p ↔ ∀ z, F p≤F z) := by
    filter_upwards [hrep.eventually,hg.eventually_nhds,hc,hb] with p hp hgp hcp hbp
    refine ⟨objectiveDistance_lowerSemicontinuousAt hF g p hp hgp hcp hbp.1,?_⟩
    rw [isAffineCritical_iff_coordinate_affineSpan]
    exact hbp.2.1
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ball star r,isOpen_ball,mem_ball_self hr,(fun p hp => hball hp),?_⟩
  intro K hK hne hKV hpositive
  apply compact_positive_objectiveDistance_minimum hF hK hne
  · exact fun p hp => (hball (hKV hp)).1
  · intro p hp hcrit
    exact (hpositive p hp).not_le (((hball (hKV hp)).2.mp hcrit) star)

/-- Module A for an actual locally represented finite C¹ maximum. Only the
originally active actual gradients need independence and positive weights.
Branch convexity is unnecessary for this stronger local statement. -/
theorem finite_C1_max_neighborhood_gap {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (star : Vec n) (hstar : star∈U)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) U) (hrep : LocalFiniteMax F f star)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f star i)) star))
    (w : Vec (activeIndices F f star).card) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, w i=1)
    (hzero : ∑ i, w i • coordinateGradient (f (activeIndexMap F f star i)) star=0) :
    ∃ V : Set (Vec n), IsOpen V ∧ star∈V ∧
      (∀ p∈V, LowerSemicontinuousAt (objectiveDistance F) p ∧
        (IsAffineCritical F p ↔ ∀ z, F p≤F z)) ∧
      (∀ K : Set (Vec n), IsCompact K → K.Nonempty → K⊆V →
        (∀ p∈K, F star<F p) →
        ∃ p∈K, 0<objectiveDistance F p ∧ ∀ q∈K, objectiveDistance F p≤objectiveDistance F q) := by
  let a := activeIndexMap F f star
  let g : Vec n → Fin (activeIndices F f star).card → Vec n :=
    fun p i => coordinateGradient (f (a i)) p
  have hfcont (i : Fin m) : ContinuousAt (f i) star :=
    (hf i).continuousOn.continuousAt (hU.mem_nhds hstar)
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt hfcont hrep
  have hd : ∀ᶠ p in 𝓝 star, ∀ i, HasFDerivAt (f (a i)) (gradientFunctional (g p i)) p := by
    filter_upwards [hU.mem_nhds hstar] with p hp i
    exact hasFDerivAt_coordinateGradient (((hf (a i)).contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
  have hc : ∀ᶠ p in 𝓝 star, ∀ i, ContinuousAt (fun q => g q i) p := by
    filter_upwards [hU.mem_nhds hstar] with p hp i
    exact coordinateGradient_continuousAt_of_contDiffAt ((hf (a i)).contDiffAt (hU.mem_nhds hp))
  exact neighborhood_gap_of_positive_barycentric hF g star hr hd hc hind w hw hsum hzero

end AffineDistance
end BfgsVerification
