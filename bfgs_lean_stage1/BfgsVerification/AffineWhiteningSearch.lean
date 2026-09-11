import BfgsVerification.AffineWhiteningRun
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection DeterministicLineSearch
variable {n : ℕ}

def linearEquiv (A : Mat n) (hA : A.det≠0) : Vec n ≃L[ℝ] Vec n :=
  (LinearEquiv.ofInjectiveEndo A.mulVecLin (by
    intro x y h
    change A.mulVec x=A.mulVec y at h
    have hh := congrArg (point A) h
    simpa only [point_map A hA] using hh)).toContinuousLinearEquiv

@[simp] theorem linearEquiv_apply (A : Mat n) (hA : A.det≠0) (x : Vec n) :
    linearEquiv A hA x=A.mulVec x := rfl

theorem differentiableAt_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x : Vec n) :
    DifferentiableAt ℝ (objective A F) (point A x) ↔ DifferentiableAt ℝ F x := by
  simpa only [Function.comp_def,linearEquiv_apply,map_point A hA] using
    (linearEquiv A hA).comp_right_differentiableAt_iff (f:=F) (x:=point A x)

/-- The actual total derivative convention is respected even at nonsmooth
points; this gives exact equality of every fuel-bounded search, without an
additional differentiability premise for unvisited trials. -/
theorem coordinateGradient_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x : Vec n) :
    coordinateGradient (objective A F) (point A x)=gradient A (coordinateGradient F x) := by
  apply gradientFunctional_injective
  change gradientFunctional (fun i => (fderiv ℝ (objective A F) (point A x)) (Pi.single i 1))=_
  rw [gradientFunctional_coordinates]
  have hd := (linearEquiv A hA).comp_right_fderiv (f:=F) (x:=point A x)
  change fderiv ℝ (objective A F) (point A x)=
    (fderiv ℝ F (A.mulVec (point A x))).comp (matrixCLM A) at hd
  rw [map_point A hA] at hd
  rw [hd,← gradientFunctional_coordinates (fderiv ℝ F x),gradientFunctional_comp]
  rfl

theorem armijo_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x p g : Vec n) (c a : ℝ) :
    Armijo (objective A F) (point A x) (point A p) (gradient A g) c a ↔
      Armijo F x p g c a := by
  have hq : point A x+a • point A p=point A (x+a • p) := by
    simp only [point,Matrix.mulVec_add,Matrix.mulVec_smul]
  simp only [Armijo,hq,objective,map_point A hA,dot_gradient_point A hA]

theorem wolfe_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x p g : Vec n) (c a : ℝ) :
    Wolfe (objective A F) (point A x) (point A p) (gradient A g) c a ↔
      Wolfe F x p g c a := by
  have hq : point A x+a • point A p=point A (x+a • p) := by
    simp only [point,Matrix.mulVec_add,Matrix.mulVec_smul]
  simp only [Wolfe,hq,coordinateGradient_equiv A hA,dot_gradient_point A hA]

theorem search_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x p g : Vec n) (c₁ c₂ : ℝ) (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a : ℝ) :
    search (objective A F) (point A x) (point A p) (gradient A g) c₁ c₂ fuel l h a=
      search F x p g c₁ c₂ fuel l h a := by
  induction fuel generalizing l h a with
  | zero => simp only [search]
  | succ fuel ih =>
    rw [search,search]
    rw [show Armijo (objective A F) (point A x) (point A p) (gradient A g) c₁ a=Armijo F x p g c₁ a from propext (armijo_equiv A hA F x p g c₁ a)]
    rw [show Wolfe (objective A F) (point A x) (point A p) (gradient A g) c₂ a=Wolfe F x p g c₂ a from propext (wolfe_equiv A hA F x p g c₂ a)]
    simp only [ih]

/-- Every decision and every rejected-trial length is unchanged for arbitrary
fuel. No finite trace, differentiable oracle, or successful search is assumed. -/
theorem fromMetric_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x : Vec n) (H : Mat n) (c₁ c₂ : ℝ) (fuel : ℕ) :
    fromMetric (objective A F) (point A x) (metric A H) c₁ c₂ fuel=
      fromMetric F x H c₁ c₂ fuel := by
  simp only [fromMetric,coordinateGradient_equiv A hA,step_equiv A hA,search_equiv A hA]

end BfgsVerification.AffineWhitening
