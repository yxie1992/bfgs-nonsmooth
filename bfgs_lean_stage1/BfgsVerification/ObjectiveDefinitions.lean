import BfgsVerification.Definitions

/-!
# Objective-level specification of an infinite admissible full-BFGS run

The objective is finite everywhere and convex. Differentiability is required
only at accepted iterates. Positive definiteness is assumed only at the initial
matrix; its preservation, positive energies, and positive curvatures must be
proved. No boundedness, summability, or convergence is built into the run.
-/

noncomputable section
open scoped BigOperators
open Matrix Filter

namespace BfgsVerification

/-- The derivative functional represented by the Euclidean gradient coordinates.
The finite-dimensional Pi norm gives the same differentiability/topology as the
Euclidean norm; the displayed functional is exactly the usual dot product. -/
def gradientFunctional {n : ℕ} (g : Vec n) : Vec n →L[ℝ] ℝ :=
  ∑ i, g i • ContinuousLinearMap.proj i

@[simp] theorem gradientFunctional_apply {n : ℕ} (g v : Vec n) :
    gradientFunctional g v = dot g v := by
  simp [gradientFunctional, dot]

/-- Infinite accepted, nonstationary full-BFGS run with ordinary Armijo and
weak Wolfe. This specification does not assert all-ray line-search existence. -/
structure AdmissibleBFGSRun (n : ℕ) (F : Vec n → ℝ) where
  convex : ConvexOn ℝ Set.univ F
  x : ℕ → Vec n
  H : ℕ → Mat n
  g : ℕ → Vec n
  α : ℕ → ℝ
  c₁ : ℝ
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  initial_posDef : (H 0).PosDef
  alpha_pos : ∀ k, 0 < α k
  gradient_nonzero : ∀ k, g k ≠ 0
  hasGradient : ∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k)
  step : ∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k)
  update : ∀ k,
    H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k))
      (g (k + 1) - g k)
  armijo : ∀ k,
    F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k))
  weak_wolfe : ∀ k,
    c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)) ≤
      dot (g (k + 1)) (bfgsStep (H k) (g k) (α k))

namespace AdmissibleBFGSRun

def q {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) : ℝ :=
  metricEnergy (R.H k) (R.g k)

def d {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) : ℝ :=
  R.α k * R.q k

def beta {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) : ℝ :=
  -dot (R.g (k + 1) - R.g k) ((R.H k).mulVec (R.g k)) / R.q k

def initialSublevel {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) : Set (Vec n) :=
  {z | F z ≤ F (R.x 0)}

end AdmissibleBFGSRun

end BfgsVerification
