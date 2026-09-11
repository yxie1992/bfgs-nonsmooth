import BfgsVerification.ObjectiveSemialgebraicComposition

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification.RealAlgebraicGeometry

/-- Actual coordinate graphs of an arbitrary finite-dimensional semialgebraic
curve follow by projecting the full graph, with its original parameter domain. -/
theorem semialgebraic_curve_coordinate_scalar_graph {σ : Type*} [Fintype σ]
    {p : ℝ → σ → ℝ} {J : Set ℝ} (hp : IsSemialgebraicCurveOn p J) (i : σ) :
    IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ J ∧ v none = p (v (some 0)) i} := by
  have hG := IsSemialgebraicMapOn.polynomial (fun _ : Fin 1 => MvPolynomial.X i)
    isSemialgebraic_univ
  have hg : IsSemialgebraicCurveOn (fun t (_ : Fin 1) => p t i) J := by
    simpa only [MvPolynomial.eval_X,Function.comp_def] using
      hp.map hG (fun _ _ => mem_univ _)
  let flip : Option (Fin 1) → Option (Fin 1) := fun j =>
    match j with | none => some 0 | some _ => none
  have h := hg.reindex flip
  convert h using 1
  ext v
  change (_ ∈ J ∧ _ = _) ↔
    (v (some 0) ∈ J ∧ (fun _ : Fin 1 => v none) = (fun _ : Fin 1 => p (v (some 0)) i))
  exact and_congr_right (fun _ => ⟨fun he => funext (fun _ => he),fun he => congrFun he 0⟩)

/-- Every actual finite-dimensional semialgebraic curve is infinitely smooth
outside a derived finite set of its actual parameter domain. No continuity or
piecewise smoothness premise is imposed, and empty coordinate types are allowed. -/
theorem semialgebraic_curve_smooth_except_finite {σ : Type*} [Fintype σ]
    {p : ℝ → σ → ℝ} {J : Set ℝ} (hp : IsSemialgebraicCurveOn p J) :
    ∃ E : Finset ℝ, ∀ t ∈ J, t ∉ E → ContDiffAt ℝ ∞ p t := by
  classical
  choose E hE using fun i : σ =>
    semialgebraic_scalar_smooth_except_finite (f := fun t => p t i) (D := J)
      (semialgebraic_curve_coordinate_scalar_graph hp i)
  refine ⟨Finset.univ.biUnion E,?_⟩
  intro t ht hnot
  apply contDiffAt_pi.mpr
  intro i
  exact hE i t ht (fun hi => hnot (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩))

end BfgsVerification.RealAlgebraicGeometry
