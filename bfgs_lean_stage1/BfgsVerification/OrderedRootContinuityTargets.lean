import BfgsVerification.OrderedRootBranches

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

def OrderedRootContinuityTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n),
    p.map (MvPolynomial.eval a) ≠ 0 → ∀ k : ℕ,
    k < (p.map (MvPolynomial.eval a)).roots.toFinset.card →
    ContinuousWithinAt (fun x => orderedRealRoot (p.map (MvPolynomial.eval x)) k)
      (rootSignatureStratum p a) a

theorem orderedRootContinuity : OrderedRootContinuityTarget := by
  intro n p a hp k hk
  exact parameter_ordered_root_continuousWithinAt p a hp hk Subset.rfl

def OrderedRootMultiplicityTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n),
    p.map (MvPolynomial.eval a) ≠ 0 → ∀ k : ℕ,
    k < (p.map (MvPolynomial.eval a)).roots.toFinset.card →
    ∀ᶠ x in 𝓝[rootSignatureStratum p a] a,
      (p.map (MvPolynomial.eval x)).rootMultiplicity (orderedRealRoot (p.map (MvPolynomial.eval x)) k) =
        (p.map (MvPolynomial.eval a)).rootMultiplicity (orderedRealRoot (p.map (MvPolynomial.eval a)) k)

theorem orderedRootMultiplicity : OrderedRootMultiplicityTarget := by
  intro n p a hp k hk
  exact parameter_ordered_root_multiplicity_locally_constant p a hp hk Subset.rfl

def OrderedRootSmoothBranchesTarget : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (k : ℕ),
    k < (fiberPolynomial p a).roots.toFinset.card →
    ContDiffOn ℝ ∞ (orderedFiberRoot p k)
      (rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a)

theorem orderedRootSmoothBranches : OrderedRootSmoothBranchesTarget := by
  intro n p a k hk
  exact orderedFiberRoot_contDiffOn_signature p a hk

end RealAlgebraicGeometry
end BfgsVerification
