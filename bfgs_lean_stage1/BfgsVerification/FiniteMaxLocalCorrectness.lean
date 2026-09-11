import BfgsVerification.FiniteMaxSubdifferential
import BfgsVerification.AffineBarycentricLocal

/-! Module A's local affine-critical correctness for an actual locally represented
finite maximum. Inactive branches are removed by a proved neighborhood argument. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace ConvexSubdifferential

/-- A local representation holds locally at every sufficiently nearby point. -/
theorem LocalFiniteMax.eventually {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n} (hrep : LocalFiniteMax F f x) :
    ∀ᶠ p in 𝓝 x, LocalFiniteMax F f p :=
  hrep.eventually_nhds

/-- Positive gaps of inactive branches persist near the base point. -/
theorem activeIndices_eventually_subset {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n} (hF : ContinuousAt F x)
    (hf : ∀ i, ContinuousAt (f i) x) (hrep : LocalFiniteMax F f x) :
    ∀ᶠ p in 𝓝 x, activeIndices F f p ⊆ activeIndices F f x := by
  have hbase := mem_of_mem_nhds hrep
  have hev (i : Fin m) : ∀ᶠ p in 𝓝 x,
      i ∈ activeIndices F f p → i ∈ activeIndices F f x := by
    by_cases hi : i ∈ activeIndices F f x
    · exact Eventually.of_forall (fun _ _ => hi)
    · have hlt : f i x < F x := lt_of_le_of_ne (hbase.2 (mem_range_self i))
        (fun heq => hi (mem_activeIndices.mpr heq))
      filter_upwards [(hf i).eventually_lt hF hlt] with p hp hip
      exact (hp.ne (mem_activeIndices.mp hip)).elim
  exact (eventually_all.mpr hev).mono fun _ hp _ hi => hp _ hi

/-- A fixed enumeration of precisely the original branches active at the base. -/
def activeIndexMap {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (x : Vec n) : Fin (activeIndices F f x).card → Fin m :=
  (activeIndices F f x).orderEmbOfFin rfl

theorem range_activeIndexMap {n m : ℕ} (F : Vec n → ℝ)
    (f : Fin m → Vec n → ℝ) (x : Vec n) :
    Set.range (activeIndexMap F f x) = (activeIndices F f x : Set (Fin m)) :=
  Finset.range_orderEmbOfFin _ rfl

/-- Removing the originally inactive branches preserves the actual objective in
a neighborhood; no restricted-model representation is assumed. -/
theorem localFiniteMax_restrict_active {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n} (hF : ContinuousAt F x)
    (hf : ∀ i, ContinuousAt (f i) x) (hrep : LocalFiniteMax F f x) :
    LocalFiniteMax F (fun i => f (activeIndexMap F f x i)) x := by
  filter_upwards [hrep, activeIndices_eventually_subset hF hf hrep] with p hp hsub
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hp.1
    have himem := hsub (mem_activeIndices.mpr hi)
    have hirange : i ∈ Set.range (activeIndexMap F f x) := by
      rw [range_activeIndexMap]
      exact himem
    obtain ⟨j, hj⟩ := hirange
    exact ⟨j, by simpa only [hj] using hi⟩
  · rintro v ⟨j, rfl⟩
    exact hp.2 (mem_range_self _)

/-- Barycentric stability applied to the exact active-gradient subdifferential.
This version starts with a family already restricted to the relevant branches. -/
theorem local_affine_critical_correctness {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ}
    (g : Vec n → Fin m → Vec n) (xstar : Vec n)
    (hrep : LocalFiniteMax F f xstar)
    (hg : ∀ᶠ p in 𝓝 xstar, ∀ i,
      HasFDerivAt (f i) (gradientFunctional (g p i)) p)
    (hc : ∀ i, ContinuousAt (fun p => g p i) xstar)
    (hind : AffineIndependent ℝ (g xstar)) (wstar : Vec m)
    (hpos : ∀ i, 0 < wstar i) (hsum : (∑ i, wstar i) = 1)
    (hzero : (∑ i, wstar i • g xstar i) = 0) :
    ∀ᶠ p in 𝓝 xstar, AffineIndependent ℝ (g p) ∧
      ((0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) ↔ ∀ z, F p ≤ F z) ∧
      ((0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) →
        activeIndices F f p = Finset.univ) := by
  filter_upwards [hrep.eventually, hg,
    AffineBarycentric.affine_critical_subfamily_eventually_full g xstar hc hind
      wstar hpos hsum hzero] with p hp hgp hb
  have heq := subdifferential_eq_active_convexHull hF hp hgp
  have hspan : affineSpan ℝ (subdifferential F p) =
      affineSpan ℝ (g p '' (activeIndices F f p : Set (Fin m))) := by
    rw [heq, affineSpan_convexHull]
  refine ⟨hb.1, ⟨?_, ?_⟩, ?_⟩
  · intro hcrit
    have hzero := (hb.2 _ (hspan ▸ hcrit)).2
    apply zero_mem_iff_global_minimum.mp
    rwa [heq]
  · intro hmin
    exact subset_affineSpan ℝ _ (zero_mem_iff_global_minimum.mpr hmin)
  · intro hcrit
    exact (hb.2 _ (hspan ▸ hcrit)).1

/-- The source's original-family theorem: inactive branches are discarded by
continuity, and only the originally active gradients need nondegenerate positive
barycentric weights. Branches themselves may be nonconvex. -/
theorem local_affine_critical_correctness_original_family {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ}
    (g : Vec n → Fin m → Vec n) (xstar : Vec n)
    (hrep : LocalFiniteMax F f xstar)
    (hg : ∀ᶠ p in 𝓝 xstar, ∀ i,
      HasFDerivAt (f i) (gradientFunctional (g p i)) p)
    (hc : ∀ i, ContinuousAt (fun p => g p i) xstar)
    (hind : AffineIndependent ℝ (fun i => g xstar (activeIndexMap F f xstar i)))
    (wstar : Vec (activeIndices F f xstar).card)
    (hpos : ∀ i, 0 < wstar i) (hsum : (∑ i, wstar i) = 1)
    (hzero : (∑ i, wstar i • g xstar (activeIndexMap F f xstar i)) = 0) :
    ∀ᶠ p in 𝓝 xstar,
      ((0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) ↔ ∀ z, F p ≤ F z) := by
  have hf (i : Fin m) : ContinuousAt (f i) xstar :=
    (mem_of_mem_nhds hg i).continuousAt
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt hf hrep
  have hd : ∀ᶠ p in 𝓝 xstar, ∀ i : Fin (activeIndices F f xstar).card,
      HasFDerivAt (f (activeIndexMap F f xstar i))
        (gradientFunctional (g p (activeIndexMap F f xstar i))) p := by
    filter_upwards [hg] with p hp i
    exact hp _
  exact (local_affine_critical_correctness hF
    (fun p i => g p (activeIndexMap F f xstar i)) xstar hr hd
    (fun i => hc _) hind wstar hpos hsum hzero).mono fun _ hp => hp.2.1

end ConvexSubdifferential
end BfgsVerification
