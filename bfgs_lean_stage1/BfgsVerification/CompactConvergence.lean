import BfgsVerification.LocalizationCorollaries
import BfgsVerification.StrictContours
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Compact solution sets and actual objective limits

Optimal values imply distance to the full solution set tends to zero on a
compact containing set. Uniqueness is not assumed. Compact initial sublevels
supply attained global minima and real limits of actual accepted objective values.
-/

noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification

/-- Global minimizers of an actual real-valued objective. -/
def argmin {E : Type*} (F : E → ℝ) : Set E := {x | ∀ y, F x ≤ F y}

/-- On a compact containing set, convergence of values to an attained minimum
forces convergence of distance to the entire solution set, without uniqueness. -/
theorem distance_to_argmin_of_values
    {E : Type*} [MetricSpace E] {F : E → ℝ} (hF : Continuous F)
    (xStar : E) (hmin : ∀ y, F xStar ≤ F y)
    {K : Set E} (hK : IsCompact K) {x : ℕ → E} (hxK : ∀ k, x k ∈ K)
    (hvalues : Tendsto (fun k => F (x k)) atTop (𝓝 (F xStar))) :
    Tendsto (fun k => Metric.infDist (x k) (argmin F)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push_neg at hn
  let S := K ∩ {p | ε ≤ Metric.infDist p (argmin F)}
  have hS : IsCompact S := hK.inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt (argmin F)))
  have hfreq : ∃ᶠ k in atTop, x k ∈ S := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk, hdist⟩ := hn N
    refine ⟨k, hk, hxK k, ?_⟩
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg Metric.infDist_nonneg] using hdist
  obtain ⟨p, hp, φ, hφ, hpconv⟩ := hS.tendsto_subseq' hfreq
  have hFp : F p = F xStar := tendsto_nhds_unique
    ((hF.tendsto p).comp hpconv) (hvalues.comp hφ.tendsto_atTop)
  have hpmin : p ∈ argmin F := by
    intro y
    rw [hFp]
    exact hmin y
  have hzero := Metric.infDist_zero_of_mem hpmin
  have hdist : ε ≤ Metric.infDist p (argmin F) := hp.2
  rw [hzero] at hdist
  linarith

/-- Distance to minimizers after a continuous coordinate map, including the
Euclidean realization of finite coordinate vectors. -/
theorem mapped_distance_to_argmin_of_values
    {E Y : Type*} [MetricSpace E] [MetricSpace Y] {F : E → ℝ} (hF : Continuous F)
    (ψ : E → Y) (hψ : Continuous ψ) (xStar : E) (hmin : ∀ y, F xStar ≤ F y)
    {K : Set E} (hK : IsCompact K) {x : ℕ → E} (hxK : ∀ k, x k ∈ K)
    (hvalues : Tendsto (fun k => F (x k)) atTop (𝓝 (F xStar))) :
    Tendsto (fun k => Metric.infDist (ψ (x k)) (ψ '' argmin F)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push_neg at hn
  let S := K ∩ {p | ε ≤ Metric.infDist (ψ p) (ψ '' argmin F)}
  have hS : IsCompact S := hK.inter_right
    (isClosed_le continuous_const ((Metric.continuous_infDist_pt (ψ '' argmin F)).comp hψ))
  have hfreq : ∃ᶠ k in atTop, x k ∈ S := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk, hdist⟩ := hn N
    refine ⟨k, hk, hxK k, ?_⟩
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg Metric.infDist_nonneg] using hdist
  obtain ⟨p, hp, φ, hφ, hpconv⟩ := hS.tendsto_subseq' hfreq
  have hFp : F p = F xStar := tendsto_nhds_unique
    ((hF.tendsto p).comp hpconv) (hvalues.comp hφ.tendsto_atTop)
  have hpmin : p ∈ argmin F := by
    intro y
    rw [hFp]
    exact hmin y
  have hzero := Metric.infDist_zero_of_mem (mem_image_of_mem ψ hpmin)
  have hdist : ε ≤ Metric.infDist (ψ p) (ψ '' argmin F) := hp.2
  rw [hzero] at hdist
  linarith

/-- Actual Euclidean coordinate realization, with its L² norm. -/
def euclideanVector {n : ℕ} : Vec n → EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Vec n)).symm

/-- Distance to the actual Euclidean set of minimizers, independent of the
finite-Pi norm used internally for the coordinate model. -/
def euclideanSolutionDistance {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : ℝ :=
  Metric.infDist (euclideanVector x) (euclideanVector '' argmin F)

theorem euclidean_distance_to_argmin_of_values
    {n : ℕ} {F : Vec n → ℝ} (hF : Continuous F)
    (xStar : Vec n) (hmin : ∀ y, F xStar ≤ F y)
    {K : Set (Vec n)} (hK : IsCompact K) {x : ℕ → Vec n} (hxK : ∀ k, x k ∈ K)
    (hvalues : Tendsto (fun k => F (x k)) atTop (𝓝 (F xStar))) :
    Tendsto (fun k => euclideanSolutionDistance F (x k)) atTop (𝓝 0) :=
  mapped_distance_to_argmin_of_values hF euclideanVector
    (PiLp.continuous_equiv_symm _ _) xStar hmin hK hxK hvalues

/-- A zero gradient of a finite convex objective certifies a global minimum;
this justifies successful termination outside the infinite nonzero-gradient model. -/
theorem global_minimum_of_zero_gradient {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x : Vec n}
    (hg : HasFDerivAt F (gradientFunctional 0) x) : x ∈ argmin F := by
  intro y
  have h := convex_supporting_inequality hF hg y
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  linarith

namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The compact initial sublevel contains a global minimizer. -/
theorem exists_global_minimum_of_compact_sublevel
    (hK : IsCompact R.initialSublevel) :
    ∃ xStar ∈ R.initialSublevel, ∀ y, F xStar ≤ F y := by
  obtain ⟨xStar, hxStar, hmin⟩ := hK.exists_isMinOn
    ⟨R.x 0, R.iterate_mem_initialSublevel 0⟩ (convex_continuous R.convex).continuousOn
  refine ⟨xStar, hxStar, fun y => ?_⟩
  by_cases hy : y ∈ R.initialSublevel
  · exact hmin hy
  · have hy' : F (R.x 0) < F y := lt_of_not_ge hy
    exact hxStar.trans hy'.le

/-- Lower-bounded accepted values have an actual finite limit by Armijo
monotonicity. The limit is not assumed to be optimal. -/
theorem objective_value_limit_of_lower_bound (L : ℝ)
    (hL : ∀ k, L ≤ F (R.x k)) :
    ∃ ℓ : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) := by
  refine ⟨⨅ k, F (R.x k), tendsto_atTop_ciInf R.objective_antitone ?_⟩
  exact ⟨L, by rintro z ⟨k, rfl⟩; exact hL k⟩

/-- Compact initial sublevels supply a real limit of accepted objective values. -/
theorem objective_value_limit_of_compact_sublevel (hK : IsCompact R.initialSublevel) :
    ∃ ℓ : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) := by
  obtain ⟨L, hL⟩ := R.lower_bound_of_compact_sublevel hK
  exact R.objective_value_limit_of_lower_bound L hL

/-- The common nonunique-minimizer conclusion for the actual accepted run. -/
theorem distance_to_argmin_of_values (xStar : Vec n)
    (hmin : ∀ y, F xStar ≤ F y) {K : Set (Vec n)}
    (hK : IsCompact K) (hxK : ∀ k, R.x k ∈ K)
    (hvalues : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xStar))) :
    Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) :=
  BfgsVerification.distance_to_argmin_of_values (convex_continuous R.convex)
    xStar hmin hK hxK hvalues

end AdmissibleBFGSRun
end BfgsVerification
