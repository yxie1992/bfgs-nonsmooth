import BfgsVerification.PlanarSecantRun

/-! Literal Module C sublevel and local-basin conclusions. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification
namespace AdmissibleBFGSRun
open ClusterSetGeometry ConvexSubdifferential PlanarCornerCharts AffineCriticalObjective
variable {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)

/-- C's principal theorem on the stated compact source sublevel. The smooth
or convex two-branch structure is required only outside affine criticality. -/
theorem planar_affineCritical_cluster_on_sublevel
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {x : Vec 2 | F x≤b}) (hstart : F (R.x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) :
    ∃ p∈clusterSet R.x, F p≤b ∧ IsAffineCritical F p := by
  have hclosed : IsClosed R.initialSublevel := isClosed_le (convex_continuous R.convex) continuous_const
  have hsub : R.initialSublevel⊆{x : Vec 2 | F x≤b} := fun x hx => hx.trans hstart
  have hinit := hK.of_isClosed_subset hclosed hsub
  have hΓ : clusterSet R.x⊆{x : Vec 2 | F x≤b} :=
    (clusterSet_subset_of_closed R.x hclosed R.iterate_mem_initialSublevel).trans hsub
  obtain ⟨p,hp,ha⟩ := R.planar_affineCritical_cluster hinit star hmin
    (fun ℓ hℓ hl0 => hstrict ℓ hℓ (hl0.trans hstart))
    (fun p hp => hregular p (hΓ hp))
  exact ⟨p,hp,hΓ hp,ha⟩

/-- C's affine-correctness corollary includes both stated Euclidean distance
and the finite-Pi distance; uniqueness gives the actual whole iterate limit. -/
theorem planar_convergence_on_sublevel
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {x : Vec 2 | F x≤b}) (hstart : F (R.x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p)
    (hcorrect : ∀ p : Vec 2, F p≤b → AffineCorrectAt F p) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ z, F z=F star → z=star) → Tendsto R.x atTop (𝓝 star)) := by
  obtain ⟨p,hp,hpb,ha⟩ := R.planar_affineCritical_cluster_on_sublevel star hmin b hK hstart hstrict hregular
  have hxK : ∀ k, R.x k∈{x : Vec 2 | F x≤b} := fun k => (R.objective_le_initial k).trans hstart
  obtain ⟨hpm,hv,hd,hed,_⟩ := R.convergence_of_affineCritical_cluster hK hxK hcorrect p hp ha
  have he : F p=F star := le_antisymm (hpm star) (hmin p)
  rw [he] at hv
  exact ⟨hv,hd,hed,fun hu => R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

end AdmissibleBFGSRun
namespace PlanarConvergence
open PlanarCornerCharts AffineCriticalObjective

/-- The basin is chosen before the run, independently of its SPD initial
metric and fixed valid Armijo–weak-Wolfe constants. -/
theorem local_convergence_basin {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (hunique : ∀ z, F z=F star → z=star)
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) (hstar : star∈Ω)
    (hregular : ∀ p∈Ω, ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p)
    (hcorrect : ∀ p∈Ω, AffineCorrectAt F p) {b : ℝ} (hb : F star<b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y) :
    ∃ ε : ℝ, 0<ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0)<F star+ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨η,hη,hsub⟩ := Localization.neighborhood_basin hF star hmin hunique (hΩ.mem_nhds hstar)
  let ε : ℝ := min η (b-F star)
  have hε : 0<ε := lt_min hη (sub_pos.mpr hb)
  refine ⟨ε,hε,?_⟩
  intro R hstart
  have hstartb : F (R.x 0)≤b := by
    have he : ε≤b-F star := min_le_right _ _
    linarith
  have hKΩ : ∀ p, F p≤F (R.x 0) → p∈Ω := by
    intro p hp
    apply hsub
    have he : ε≤η := min_le_left _ _
    change F p≤F star+η
    linarith
  have hK := R.initialSublevel_compact_of_unique_minimizer star hmin hunique
  obtain ⟨hv,_,_,hx⟩ := R.planar_convergence_on_sublevel star hmin (F (R.x 0)) hK le_rfl
    (fun ℓ hℓ hl0 => hstrict ℓ hℓ (hl0.trans hstartb))
    (fun p hp => hregular p (hKΩ p hp)) (fun p hp => hcorrect p (hKΩ p hp))
  exact ⟨hv,hx hunique⟩

end PlanarConvergence
end BfgsVerification
