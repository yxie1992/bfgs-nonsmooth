import BfgsVerification.AffineCriticalObjective

/-! Actual compact cluster sets and eventual trapping near the whole set.
These are shared by C and U, with no assumed iterate limit or connectedness. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace ClusterSetGeometry

def clusterSet {E : Type*} [TopologicalSpace E] (x : ℕ → E) : Set E :=
  {p | MapClusterPt p atTop x}

theorem isClosed_clusterSet {E : Type*} [TopologicalSpace E] (x : ℕ → E) :
    IsClosed (clusterSet x) := isClosed_setOf_clusterPt

theorem clusterSet_subset_of_closed {E : Type*} [TopologicalSpace E]
    (x : ℕ → E) {K : Set E} (hK : IsClosed K) (hxK : ∀ k, x k ∈ K) :
    clusterSet x ⊆ K := by
  intro p hp
  have hc := hp.clusterPt.mem_closure_of_mem K (mem_map.mpr (Eventually.of_forall hxK))
  rwa [hK.closure_eq] at hc

theorem isCompact_clusterSet {E : Type*} [TopologicalSpace E] [T2Space E]
    (x : ℕ → E) {K : Set E} (hK : IsCompact K) (hxK : ∀ k, x k ∈ K) :
    IsCompact (clusterSet x) :=
  hK.of_isClosed_subset (isClosed_clusterSet x) (clusterSet_subset_of_closed x hK.isClosed hxK)

theorem clusterSet_nonempty {E : Type*} [TopologicalSpace E]
    (x : ℕ → E) {K : Set E} (hK : IsCompact K) (hxK : ∀ k, x k ∈ K) :
    (clusterSet x).Nonempty := by
  have hf : ∃ᶠ k in atTop, x k ∈ K := Frequently.of_forall hxK
  obtain ⟨p,_,hp⟩ := hK.exists_mapClusterPt_of_frequently hf
  exact ⟨p,hp⟩

/-- Every open neighborhood of the whole actual cluster set contains the full
sufficiently late trajectory. A chart around one selected point is insufficient. -/
theorem eventually_mem_of_open_superset {E : Type*} [TopologicalSpace E] [T2Space E]
    (x : ℕ → E) {K U : Set E} (hK : IsCompact K) (hxK : ∀ k, x k ∈ K)
    (hU : IsOpen U) (hsub : clusterSet x ⊆ U) : ∀ᶠ k in atTop, x k ∈ U := by
  by_contra hn
  have hf : ∃ᶠ k in atTop, x k ∈ K ∩ Uᶜ := by
    have hu : ∃ᶠ k in atTop, x k ∉ U := not_eventually.mp hn
    exact hu.and_eventually (Eventually.of_forall hxK) |>.mono (fun k hk => ⟨hk.2,hk.1⟩)
  obtain ⟨p,hp,hcp⟩ := (hK.inter_right hU.isClosed_compl).exists_mapClusterPt_of_frequently hf
  exact hp.2 (hsub hcp)

/-- The usual distance-to-cluster-set fact is derived from compactness. -/
theorem distance_tendsto_zero {E : Type*} [MetricSpace E]
    (x : ℕ → E) {K : Set E} (hK : IsCompact K) (hxK : ∀ k, x k ∈ K) :
    Tendsto (fun k => Metric.infDist (x k) (clusterSet x)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hU : IsOpen {p | Metric.infDist p (clusterSet x) < ε} :=
    isOpen_lt (Metric.continuous_infDist_pt _) continuous_const
  have hsub : clusterSet x ⊆ {p | Metric.infDist p (clusterSet x) < ε} := by
    intro p hp
    change Metric.infDist p (clusterSet x) < ε
    simpa only [Metric.infDist_zero_of_mem hp] using hε
  have he := eventually_mem_of_open_superset x hK hxK hU hsub
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun k hk => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg Metric.infDist_nonneg]
  exact hN k hk

end ClusterSetGeometry
namespace AdmissibleBFGSRun
open ClusterSetGeometry AffineCriticalObjective ConvexSubdifferential
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Source C/U positive limiting level under the hypothetical absence of
an affine-critical cluster. The objective value limit is constructed. -/
theorem positive_limit_of_no_affineCritical_cluster
    {K : Set (Vec n)} (hK : IsCompact K) (hxK : ∀ k, R.x k ∈ K)
    (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hno : ∀ p ∈ clusterSet R.x, ¬ IsAffineCritical F p) :
    ∃ ℓ : ℝ, F star < ℓ ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) ∧
      clusterSet R.x ⊆ {p | F p = ℓ} := by
  obtain ⟨ℓ,hℓ⟩ := R.objective_value_limit_of_lower_bound (F star) (fun k => hmin _)
  have hle : F star ≤ ℓ := ge_of_tendsto hℓ (Eventually.of_forall (fun k => hmin _))
  have hlevel : clusterSet R.x ⊆ {p | F p = ℓ} := fun p hp => R.value_of_cluster hℓ hp
  refine ⟨ℓ,lt_of_le_of_ne hle ?_,hℓ,hlevel⟩
  intro he
  obtain ⟨p,hp⟩ := clusterSet_nonempty R.x hK hxK
  have hstat : (0 : Vec n) ∈ subdifferential F p := zero_mem_iff_global_minimum.mpr (fun z => by
    rw [hlevel hp,← he]
    exact hmin z)
  apply hno p hp
  apply mem_affineSpan ℝ
  refine ⟨⟨0,hstat⟩,?_⟩
  rfl

end AdmissibleBFGSRun
end BfgsVerification
