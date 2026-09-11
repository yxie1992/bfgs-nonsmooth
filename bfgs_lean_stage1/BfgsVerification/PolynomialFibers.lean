import BfgsVerification.SemialgebraicGraphs
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Actual multivariate polynomial fibers and their actual vertical derivatives.
The parameters are arbitrary finite real coordinates; no degree restriction or
root regularity assumption is built into the definitions. -/
noncomputable section
open scoped Topology
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

def parameterPoint (x : Vec n) (t : ℝ) : Option (Fin n) → ℝ := fun i => match i with
  | none => t
  | some j => x j

def parameterEval (p : MvPolynomial (Option (Fin n)) ℝ) (z : Vec n × ℝ) : ℝ :=
  MvPolynomial.eval (parameterPoint z.1 z.2) p

def fiberPolynomial (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | none => Polynomial.X
    | some j => Polynomial.C (x j)) p

theorem fiberPolynomial_eval (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) (t : ℝ) :
    (fiberPolynomial p x).eval t = parameterEval p (x,t) := by
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    simp
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂Hom Polynomial.C _ p) =
    MvPolynomial.eval₂Hom (RingHom.id ℝ) (parameterPoint x t) p
  rw [MvPolynomial.map_eval₂Hom,hc]
  have hg : (fun i : Option (Fin n) => (Polynomial.evalRingHom t)
      (match i with | none => Polynomial.X | some j => Polynomial.C (x j))) = parameterPoint x t := by
    funext i
    cases i with
    | none => exact Polynomial.eval_X
    | some j => exact Polynomial.eval_C
  rw [hg]

def parameterCoordinate : Option (Fin n) → (Vec n × ℝ) →L[ℝ] ℝ
  | none => ContinuousLinearMap.snd ℝ (Vec n) ℝ
  | some i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Vec n) ℝ)

theorem analytic_parameterEval (p : MvPolynomial (Option (Fin n)) ℝ) (z : Vec n × ℝ) :
    AnalyticAt ℝ (parameterEval p) z := by
  have h := AnalyticOnNhd.eval_continuousLinearMap' (parameterCoordinate (n := n)) p z (mem_univ _)
  have he : (fun w : Vec n × ℝ => MvPolynomial.eval (fun i => parameterCoordinate i w) p) =
      parameterEval p := by
    funext w
    apply congrArg (fun v : Option (Fin n) → ℝ => MvPolynomial.eval v p)
    funext i
    cases i <;> rfl
  exact he ▸ h

/-- The derivative test used for a simple root is the derivative of the actual
univariate fiber polynomial, and equals the actual vertical Frechet derivative. -/
theorem parameterEval_vertical_derivative (p : MvPolynomial (Option (Fin n)) ℝ)
    (x : Vec n) (t : ℝ) :
    fderiv ℝ (parameterEval p) (x,t) (0,1) = (fiberPolynomial p x).derivative.eval t := by
  have hF := (analytic_parameterEval p (x,t)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun u : ℝ => (x,u)) (0,1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hcomp := hF.comp_hasDerivAt t hcurve
  have hp := (fiberPolynomial p x).hasDerivAt t
  have he : (fun u : ℝ => (fiberPolynomial p x).eval u) = (fun u => parameterEval p (x,u)) :=
    funext (fiberPolynomial_eval p x)
  rw [he] at hp
  exact hcomp.unique hp

end RealAlgebraicGeometry
end BfgsVerification
