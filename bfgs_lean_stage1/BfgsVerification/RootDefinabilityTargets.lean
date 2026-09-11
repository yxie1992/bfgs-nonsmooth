import BfgsVerification.SemialgebraicRootBands

noncomputable section
open Set Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

def ActualRootCountsTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)),
    FiniteSemialgebraicFunction (fun x : Vec n =>
      (p.map (MvPolynomial.eval x)).roots.toFinset.card) ∧
    FiniteSemialgebraicFunction (fun x : Vec n =>
      (p.map (MvPolynomial.eval x)).roots.card)

theorem actualRootCounts : ActualRootCountsTarget := by
  intro n p
  exact ⟨finiteSemialgebraic_distinctRealRootCount p,
    finiteSemialgebraic_totalRealRootMultiplicity p⟩

def ActualRootSignatureTarget : Prop :=
  ∀ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n),
    IsSemialgebraic (rootSignatureStratum p a)

theorem actualRootSignature : ActualRootSignatureTarget := by
  intro n p a
  exact rootSignatureStratum_semialgebraic p a

def ActualOrderedRootGraphTarget : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ),
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      k < (fiberPolynomial p (fun i => v (some i))).roots.toFinset.card ∧
        v none = orderedFiberRoot p k (fun i => v (some i))} ∧
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      v none = orderedFiberRoot p k (fun i => v (some i))}

theorem actualOrderedRootGraph : ActualOrderedRootGraphTarget := by
  intro n p k
  exact ⟨orderedFiberRoot_valid_graph_semialgebraic p k,
    orderedFiberRoot_graph_semialgebraic p k⟩

def ActualOrderedRootBandsTarget : Prop :=
  ∀ (n : ℕ) (p q : MvPolynomial (Option (Fin n)) ℝ) (j k : ℕ) (S : Set (Vec n)),
    IsSemialgebraic S →
    IsSemialgebraic {v : Option (Fin n) → ℝ | (fun i => v (some i)) ∈ S ∧
      orderedFiberRoot p j (fun i => v (some i)) < v none ∧
        v none < orderedFiberRoot q k (fun i => v (some i))}

theorem actualOrderedRootBands : ActualOrderedRootBandsTarget := by
  intro n p q j k S hS
  exact orderedFiberRoot_band_semialgebraic p q j k hS

end BfgsVerification.RealAlgebraicGeometry
