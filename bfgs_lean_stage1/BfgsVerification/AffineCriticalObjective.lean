import BfgsVerification.AffineCriticalGeometry
import BfgsVerification.ConvexSubdifferential

/-! Module A's actual finite-convex affine-critical geometry and compact-run
reduction. Subgradients and their nonemptiness are derived from the objective. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Set Filter Matrix
namespace BfgsVerification
namespace AffineCriticalObjective
open ConvexSubdifferential AffineCriticalGeometry

def subgradientFamily {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    subdifferential F x → EuclideanSpace ℝ (Fin n) := fun g => euclideanVector g

def IsAffineCritical {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Prop :=
  (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (range (subgradientFamily F x))

def AffineCorrectAt {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Prop :=
  IsAffineCritical F x → (0 : Vec n) ∈ subdifferential F x

def canonicalVector {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (x : Vec n) :
    EuclideanSpace ℝ (Fin n) := closestAffinePoint (subgradientFamily F x)
      ⟨(subdifferential_nonempty hF x).choose, (subdifferential_nonempty hF x).choose_spec⟩

theorem range_subgradientFamily {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    range (subgradientFamily F x) = euclideanVector '' subdifferential F x := by
  ext a
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g,g.property,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨⟨g,hg⟩,rfl⟩

theorem affineSpan_subgradientFamily_of_convexHull {n : ℕ} {F : Vec n → ℝ}
    (x : Vec n) (S : Set (Vec n)) (he : subdifferential F x = convexHull ℝ S) :
    affineSpan ℝ (range (subgradientFamily F x)) = affineSpan ℝ (euclideanVector '' S) := by
  rw [range_subgradientFamily,he]
  have hm := (WithLp.linearEquiv 2 ℝ (Vec n)).symm.toLinearMap.image_convexHull S
  change euclideanVector '' convexHull ℝ S = convexHull ℝ (euclideanVector '' S) at hm
  rw [hm,affineSpan_convexHull]

theorem canonicalVector_eq {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x : Vec n) (g : subdifferential F x) :
    canonicalVector hF x = closestAffinePoint (subgradientFamily F x) g :=
  closestAffinePoint_independent _ _ _

theorem canonicalVector_pairing {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x : Vec n) (g : Vec n) (hg : g ∈ subdifferential F x) :
    ⟪euclideanVector g, canonicalVector hF x⟫_ℝ = ‖canonicalVector hF x‖^2 := by
  rw [canonicalVector_eq hF x ⟨g,hg⟩]
  exact affine_pairing_closest (subgradientFamily F x) ⟨g,hg⟩ _
    (mem_affineSpan ℝ (mem_range_self (f := subgradientFamily F x) ⟨g,hg⟩))

theorem canonicalVector_zero_iff {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x : Vec n) : canonicalVector hF x = 0 ↔ IsAffineCritical F x :=
  closestAffinePoint_zero_iff _ _

theorem affine_distance_eq_norm {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x : Vec n) : Metric.infDist (0 : EuclideanSpace ℝ (Fin n))
      (affineSpan ℝ (range (subgradientFamily F x)) : Set _) = ‖canonicalVector hF x‖ :=
  infDist_affineSpan_eq_norm_closest _ _

theorem euclidean_pairing_eq_dot {n : ℕ} (g v : Vec n) :
    ⟪euclideanVector g, euclideanVector v⟫_ℝ = dot g v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _

/-- Source equal-rate direction for every actual subgradient, with no finite
alphabet or regular subgradient selection assumed. -/
theorem equal_rate_exists_iff_not_affineCritical {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (x : Vec n) :
    (∃ v : Vec n, ∀ g ∈ subdifferential F x, dot g v = -1) ↔ ¬ IsAffineCritical F x := by
  obtain ⟨g,hg⟩ := subdifferential_nonempty hF x
  constructor
  · rintro ⟨v,hv⟩
    apply affine_zero_excluded_of_equal_rate (subgradientFamily F x) (euclideanVector v)
    intro a
    exact (euclidean_pairing_eq_dot a v).trans (hv a a.property)
  · intro hx
    obtain ⟨v,hv⟩ := (equal_rate_exists_iff (subgradientFamily F x) ⟨g,hg⟩).mpr hx
    refine ⟨fun i => v i, ?_⟩
    intro a ha
    have he : euclideanVector (fun i => v i) = v := rfl
    rw [← euclidean_pairing_eq_dot, he]
    exact hv ⟨a,ha⟩

/-- Pointwise affine correctness is exactly equal-rate separation at a
nonoptimal point. The actual supporting-set minimum criterion discharges
stationarity versus optimality. -/
theorem affineCorrectAt_iff_nonoptimal_equal_rate {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (x : Vec n) :
    AffineCorrectAt F x ↔
      (x ∉ argmin F → ∃ v : Vec n, ∀ g ∈ subdifferential F x, dot g v = -1) := by
  constructor
  · intro hc hn
    apply (equal_rate_exists_iff_not_affineCritical hF x).mpr
    intro ha
    exact hn (zero_mem_iff_global_minimum.mp (hc ha))
  · intro hv ha
    apply zero_mem_iff_global_minimum.mpr
    by_contra hn
    exact ((equal_rate_exists_iff_not_affineCritical hF x).mp (hv hn)) ha

theorem affineCorrectAt_of_hasFDerivAt {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) : AffineCorrectAt F x := by
  intro hc
  have hs := subdifferential_eq_singleton_of_hasFDerivAt hF hg
  have he : (0 : EuclideanSpace ℝ (Fin n)) = euclideanVector g := by
    simpa [IsAffineCritical,range_subgradientFamily,hs] using hc
  have hz : g = 0 := by
    ext i
    exact (congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) he).symm
  rw [hs,hz]
  exact mem_singleton 0

end AffineCriticalObjective
namespace AdmissibleBFGSRun
open AffineCriticalObjective ConvexSubdifferential
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Every actual cluster point has the common finite value limit. -/
theorem value_of_cluster {ℓ : ℝ} (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ))
    {p : Vec n} (hp : MapClusterPt p atTop R.x) : F p = ℓ := by
  have hc : MapClusterPt (F p) atTop (fun k => F (R.x k)) :=
    hp.continuousAt_comp (convex_continuous R.convex).continuousAt
  exact eq_of_nhds_neBot (hc.clusterPt.mono hℓ)

/-- Module A's compact-run reduction uses an actual affine-critical cluster
point; neither a full iterate limit nor vanishing accepted gradients is assumed. -/
theorem convergence_of_affineCritical_cluster {K : Set (Vec n)} (hK : IsCompact K)
    (hxK : ∀ k, R.x k ∈ K) (hcorrect : ∀ p ∈ K, AffineCorrectAt F p)
    (p : Vec n) (hp : MapClusterPt p atTop R.x) (ha : IsAffineCritical F p) :
    p ∈ argmin F ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F p)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ z, F z = F p → z = p) → Tendsto R.x atTop (𝓝 p)) := by
  have hpK : p ∈ K := by
    have hc := hp.clusterPt.mem_closure_of_mem K (mem_map.mpr (Eventually.of_forall hxK))
    rwa [hK.isClosed.closure_eq] at hc
  obtain ⟨L,hL⟩ := convex_boundedBelow_on_compact R.convex hK
  obtain ⟨ℓ,hℓ⟩ := R.objective_value_limit_of_lower_bound L (fun k => hL _ (hxK k))
  have he := R.value_of_cluster hℓ hp
  have hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F p)) := by rwa [he]
  have hmin : p ∈ argmin F := zero_mem_iff_global_minimum.mp (hcorrect p hpK ha)
  refine ⟨hmin,hv,R.distance_to_argmin_of_values p hmin hK hxK hv,
    euclidean_distance_to_argmin_of_values (convex_continuous R.convex) p hmin hK hxK hv,
    fun hu => R.iterates_tendsto_unique_min_of_values p hmin hu hv⟩

end AdmissibleBFGSRun
end BfgsVerification
