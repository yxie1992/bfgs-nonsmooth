import Mathlib

/-!
# Exact mathematical targets for the BFGS formalization

STATUS: compiled definitions. These definitions do not prove the target propositions.
Source: BFGS_MASTER_REPORT.pdf, Module M, printed pp. 9--10 (PDF pp. 13--14).

`principalSum` uses sums of actual principal determinants. It is NOT an
uninterpreted collection of numbers. `EndToEnd.fullBFGS_normalizedHierarchy`
connects this definition to the hierarchy in `ScalarHierarchy.lean` (the export
is in the `BfgsVerification` namespace).
-/

noncomputable section
open scoped BigOperators
open Matrix Filter

namespace BfgsVerification

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def dot {n : ℕ} (x y : Vec n) : ℝ := ∑ i, x i * y i

def sqNorm {n : ℕ} (x : Vec n) : ℝ := ∑ i, (x i) ^ 2

def outer {n : ℕ} (x y : Vec n) : Mat n := fun i j => x i * y j

def metricEnergy {n : ℕ} (H : Mat n) (g : Vec n) : ℝ :=
  dot g (H.mulVec g)

def bfgsStep {n : ℕ} (H : Mat n) (g : Vec n) (α : ℝ) : Vec n :=
  -α • H.mulVec g

def inverseBFGS {n : ℕ} (H : Mat n) (s y : Vec n) : Mat n :=
  let t := dot y s
  (1 - t⁻¹ • outer s y) * H * (1 - t⁻¹ • outer y s) +
    t⁻¹ • outer s s

def principalSum {n : ℕ} (H : Mat n) (j : ℕ) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
    Matrix.det (H.submatrix (fun i : I => (i : Fin n))
      (fun i : I => (i : Fin n)))

/-- This is M.1's desired end-to-end theorem statement, NOT a theorem proof. -/
def PrincipalMinorHierarchyTarget : Prop :=
  ∀ (n : ℕ) (H : Mat n) (g y : Vec n) (α : ℝ),
    H.PosDef → 0 < α →
    let q := metricEnergy H g
    let β := -dot y (H.mulVec g) / q
    0 < q → 0 < β →
    ∀ j : ℕ, 1 ≤ j → j ≤ n →
      principalSum (inverseBFGS H (bfgsStep H g α) y) j ≤
        sqNorm y / (β ^ 2 * q) * principalSum H (j + 1) +
        α / β * principalSum H j

/-- Pure matrix sequence specification: no objective or spectral limit is assumed. -/
structure FullBFGSRun (n : ℕ) where
  H : ℕ → Mat n
  g : ℕ → Vec n
  α : ℕ → ℝ
  positive_definite : ∀ k, (H k).PosDef
  alpha_pos : ∀ k, 0 < α k
  energy_pos : ∀ k, 0 < metricEnergy (H k) (g k)
  curvature_pos : ∀ k,
    0 < dot (g (k + 1) - g k) (bfgsStep (H k) (g k) (α k))
  update : ∀ k,
    H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k))
      (g (k + 1) - g k)

namespace FullBFGSRun

def q {n : ℕ} (R : FullBFGSRun n) (k : ℕ) : ℝ :=
  metricEnergy (R.H k) (R.g k)

def d {n : ℕ} (R : FullBFGSRun n) (k : ℕ) : ℝ := R.α k * R.q k

def beta {n : ℕ} (R : FullBFGSRun n) (k : ℕ) : ℝ :=
  -dot (R.g (k + 1) - R.g k) ((R.H k).mulVec (R.g k)) / R.q k

end FullBFGSRun

def reciprocalMean (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, (q k)⁻¹) / (N : ℝ)

def reciprocalGeometricMean (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∏ k ∈ Finset.range N, (q k)⁻¹) ^ ((N : ℝ)⁻¹)

/-- M.2's target, inhabited by `reciprocalGrowth`, with boundedness and the
weak-Wolfe lower bound spelled out. -/
def ReciprocalGrowthTarget : Prop :=
  ∀ (n : ℕ) (R : FullBFGSRun n) (G c : ℝ),
    0 < G → 0 < c →
    (∀ k, sqNorm (R.g k) ≤ G ^ 2) →
    (∀ k, c ≤ R.beta k) →
    Tendsto R.d atTop (nhds 0) →
    Tendsto (reciprocalGeometricMean R.q) atTop atTop ∧
    Tendsto (reciprocalMean R.q) atTop atTop

/-- M.3's target, inhabited by `superquadraticReciprocalGrowth`. -/
def SuperquadraticReciprocalTarget : Prop :=
  ∀ (n : ℕ) (R : FullBFGSRun n) (G c : ℝ),
    0 < G → 0 < c →
    (∀ k, sqNorm (R.g k) ≤ G ^ 2) →
    (∀ k, c ≤ R.beta k) → Summable R.d →
    Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2)
      atTop atTop

end BfgsVerification
