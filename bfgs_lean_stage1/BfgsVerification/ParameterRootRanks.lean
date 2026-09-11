import BfgsVerification.ParameterRootCounts
import BfgsVerification.OrderedRootRanks
import Mathlib.Data.Fintype.Option

noncomputable section
open Set Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

variable {σ τ : Type*} [Finite σ] [Finite τ]

theorem FiniteSemialgebraicFunction.reindex {α : Type*} {f : (σ → ℝ) → α}
    (hf : FiniteSemialgebraicFunction f) (r : σ → τ) :
    FiniteSemialgebraicFunction (fun x : τ → ℝ => f (fun i => x (r i))) := by
  refine ⟨hf.finite_range.subset ?_,fun a => ?_⟩
  · rintro _ ⟨x,rfl⟩
    exact Set.mem_range_self _
  · simpa only [MvPolynomial.eval_X, Set.preimage_setOf_eq] using
      (hf.fiber a).polynomial_preimage (fun i => MvPolynomial.X (r i))

theorem rootBelowCount_eq_sign_count (p : Polynomial ℝ) (t : ℝ) :
    rootBelowCount p t = rootSignCount p
      (fun _ : Fin 1 => Polynomial.X - Polynomial.C t) (fun _ => -1) := by
  classical
  unfold rootBelowCount rootSignCount finiteSignCount
  congr 1
  apply Finset.filter_congr
  intro a _
  simp only [funext_iff, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sign_eq_neg_one_iff, sub_neg]
  simp

/-- Add a distinguished real coordinate, retaining the actual parameter
polynomial coefficients by their variable renaming. -/
def liftRootParameterPolynomial (p : Polynomial (MvPolynomial σ ℝ)) :
    Polynomial (MvPolynomial (Option σ) ℝ) :=
  p.map (MvPolynomial.rename some).toRingHom

omit [Finite σ] in
theorem liftRootParameterPolynomial_specialize
    (p : Polynomial (MvPolynomial σ ℝ)) (v : Option σ → ℝ) :
    (liftRootParameterPolynomial p).map (MvPolynomial.eval v) =
      p.map (MvPolynomial.eval (fun i => v (some i))) := by
  ext k
  simp [liftRootParameterPolynomial, MvPolynomial.eval_rename, Function.comp_def]

omit [Finite σ] in
theorem finiteSemialgebraic_rootBelowCount [Fintype σ]
    (p : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun v : Option σ → ℝ =>
      rootBelowCount (p.map (MvPolynomial.eval (fun i => v (some i)))) (v none)) := by
  have h := finiteSemialgebraic_actualRootSignCount (liftRootParameterPolynomial p)
    (fun _ : Fin 1 => Polynomial.X - Polynomial.C (MvPolynomial.X none)) (fun _ => -1)
  simpa only [liftRootParameterPolynomial_specialize, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, MvPolynomial.eval_X,
    ← rootBelowCount_eq_sign_count] using h

end BfgsVerification.RealAlgebraicGeometry
