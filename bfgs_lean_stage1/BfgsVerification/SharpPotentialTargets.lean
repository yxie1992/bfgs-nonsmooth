import BfgsVerification.SharpPotentialDegree

noncomputable section
open scoped BigOperators Topology
open Filter
open BfgsVerification.ScalarHierarchy
namespace BfgsVerification

/-- Exact M149 polynomial, sharp power, and horizon root limit for actual full BFGS. -/
def SharpPrincipalPotentialTarget : Prop :=
  ∀ (n : ℕ) (R : FullBFGSRun n) (G c : ℝ), 0 < c → Summable R.d →
  ∀ J : ℕ,
    let D := ∑' i : ℕ, R.d (J + i)
    let K := 4 * G ^ 2 / c ^ 2
    ∃ p : Polynomial ℝ, p.natDegree ≤ n - 1 ∧
      (∀ m : ℕ, 2 ≤ m →
        weightedPotential n (K / (D / (c * ((m : ℝ) - 1)))) (principalSum (R.H J)) =
          p.eval ((m : ℝ) - 1) ∧
        weightedPotential n (K / (D / (c * ((m : ℝ) - 1)))) (principalSum (R.H J)) ≤
          weightedPotential n (K / (D / c)) (principalSum (R.H J)) *
            ((m : ℝ) - 1) ^ (n - 1)) ∧
      Tendsto (fun m : ℕ =>
        (weightedPotential n (K / (D / (c * ((m : ℝ) - 1))))
          (principalSum (R.H J))) ^ (1 / (m : ℝ))) atTop (𝓝 1)

theorem sharpPrincipalPotential : SharpPrincipalPotentialTarget := by
  intro n R G c hc hd J
  dsimp only
  refine ⟨SharpPotentialDegree.potentialPolynomial n
    ((4 * G ^ 2 / c ^ 2) / ((∑' i : ℕ, R.d (J + i)) / c)) (principalSum (R.H J)),
    SharpPotentialDegree.potentialPolynomial_natDegree _ _ _, ?_,
    SharpPotentialDegree.run_optimized_root_tendsto R G c hc hd J⟩
  intro m hm
  exact ⟨SharpPotentialDegree.principal_optimized_polynomial _ _ _ _ _,
    SharpPotentialDegree.run_optimized_bound R G c hc hd J m hm⟩

end BfgsVerification
