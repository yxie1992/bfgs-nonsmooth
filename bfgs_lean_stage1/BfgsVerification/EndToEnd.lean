import BfgsVerification.PrincipalHierarchy
import BfgsVerification.Normalization

/-!
# Module M: exported results for actual full-BFGS matrix runs

These declarations discharge the matrix-hierarchy premise using the theorem
about actual inverse-BFGS updates and actual principal determinants. They do not
assume a normalized scalar hierarchy, matrix convergence, or iterate convergence.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace BfgsVerification

/-- The normalized scalar hierarchy is derived from the actual full-BFGS update. -/
theorem fullBFGS_normalizedHierarchy {n : ℕ} (R : FullBFGSRun n) (G c : ℝ)
    (hG : 0 < G) (hc : 0 < c)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (hβ : ∀ k, c ≤ R.beta k) :
    ScalarHierarchy.NormalizedHierarchy n (fun k => principalSum (R.H k))
      R.q (fun k => R.d k / c) (4 * G ^ 2 / c ^ 2) (G ^ 2) :=
  normalizedHierarchy_of_principalMinorHierarchy principalMinorHierarchy R G c hG hc hg hβ

/-- Both reciprocal means diverge for the actual full-BFGS run when predicted
decreases tend to zero and gradients and weak-Wolfe constants satisfy M.2. -/
theorem reciprocalGrowth : ReciprocalGrowthTarget :=
  reciprocalGrowth_of_principalMinorHierarchy principalMinorHierarchy

/-- Summable predicted decreases force superquadratic reciprocal-sum growth
for the actual unmodified full-BFGS run, in arbitrary finite dimension. -/
theorem superquadraticReciprocalGrowth : SuperquadraticReciprocalTarget :=
  superquadraticGrowth_of_principalMinorHierarchy principalMinorHierarchy

/-- Module M's finite-horizon bound with the actual tail budget and matrices.
The block length is `m+1` and the assumption `0<m` means length at least two. -/
theorem finiteHorizon {n : ℕ} (R : FullBFGSRun n) (G c : ℝ)
    (hG : 0 < G) (hc : 0 < c)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (hβ : ∀ k, c ≤ R.beta k)
    (hd : Summable R.d) (J m : ℕ) (hm : 0 < m) (η : ℝ) (hη : 0 < η) :
    let D := ∑' i : ℕ, R.d (J + i)
    let V := ScalarHierarchy.weightedPotential n ((4 * G ^ 2 / c ^ 2) / η)
      (principalSum (R.H J))
    ((m + 1 : ℕ) : ℝ) * (G ^ 2 * V) ^ (-1 / ((m + 1 : ℕ) : ℝ)) *
      (η + D / (c * (m : ℝ))) ^ (-(m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range (m + 1), (R.q (J + i))⁻¹ :=
  finiteHorizon_of_principalMinorHierarchy principalMinorHierarchy R G c hG hc hg hβ hd J m hm η hη

end BfgsVerification
