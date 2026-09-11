import BfgsVerification.SemialgebraicCurveGraphs
import BfgsVerification.SemialgebraicScalarSmooth
import BfgsVerification.ConvexAnalysis

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification.RealAlgebraicGeometry

/-- The graph of the actual objective along an actual semialgebraic curve is
semialgebraic on the given parameter domain. The eliminated coordinates are the
actual point on the curve, not independently chosen witnesses for each atom. -/
theorem semialgebraic_objective_curve_scalar_graph {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraicObjective F) {p : ℝ → Vec n} {J : Set ℝ}
    (hp : IsSemialgebraicCurveOn p J) :
    IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ J ∧ v none = F (p (v (some 0)))} := by
  let G : Vec n → Vec 1 := fun x _ => F x
  have hG : IsSemialgebraicMapOn G univ := by
    apply IsSemialgebraicMapOn.coordinatewise isSemialgebraic_univ
    intro i
    simpa only [mem_univ,true_and] using hF
  have hg := hp.map hG (fun _ _ => mem_univ _)
  let flip : Option (Fin 1) → Option (Fin 1) := fun i =>
    match i with | none => some 0 | some _ => none
  have h := hg.reindex flip
  convert h using 1
  ext v
  change (_ ∈ J ∧ _ = _) ↔
    (v (some 0) ∈ J ∧ (fun _ : Fin 1 => v none) = (fun _ : Fin 1 => F (p (v (some 0)))))
  exact and_congr_right (fun _ => ⟨fun he => funext (fun _ => he),fun he => congrFun he 0⟩)

/-- Literal A composition regularity, derived from finite convexity and the
actual two semialgebraic graphs. The continuous path need not be differentiable.
Continuity at both endpoints and smoothness outside one finite interior set are
proved for the actual scalar composition. -/
theorem convex_semialgebraic_objective_curve_piecewise_smooth {n : ℕ} {F : Vec n → ℝ}
    (hconv : ConvexOn ℝ univ F) (hF : IsSemialgebraicObjective F)
    {p : ℝ → Vec n} (hc : ContinuousOn p (Icc 0 1))
    (hp : IsSemialgebraicCurveOn p (Icc 0 1)) :
    IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ Icc (0 : ℝ) 1 ∧ v none = (F ∘ p) (v (some 0))} ∧
    ContinuousOn (F ∘ p) (Icc 0 1) ∧
    ∃ E : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ E → ContDiffAt ℝ ∞ (F ∘ p) t := by
  have hgraph := semialgebraic_objective_curve_scalar_graph hF hp
  have hcont : ContinuousOn (F ∘ p) (Icc 0 1) := (convex_continuous hconv).comp_continuousOn hc
  obtain ⟨E,_,hE⟩ := continuous_semialgebraic_interval_piecewise_smooth hcont hgraph
  exact ⟨hgraph,hcont,E,hE⟩

end BfgsVerification.RealAlgebraicGeometry
