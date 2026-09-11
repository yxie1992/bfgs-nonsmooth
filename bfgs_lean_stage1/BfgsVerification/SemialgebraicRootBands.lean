import BfgsVerification.OrderedRootDefinability
import BfgsVerification.GeneralCoordinateProjection

noncomputable section
open Set MvPolynomial
namespace BfgsVerification.RealAlgebraicGeometry

variable {σ : Type*} [Fintype σ]

/-- A genuine semialgebraic scalar graph gives its strict subgraph by the
proved scalar projection theorem, with an actual graph-value witness. -/
theorem semialgebraic_below_of_graph {f : (σ → ℝ) → ℝ}
    (hf : IsSemialgebraic {v : Option σ → ℝ | v none = f (fun i => v (some i))}) :
    IsSemialgebraic {v : Option σ → ℝ | v none < f (fun i => v (some i))} := by
  let r : Option σ → Option (Option σ) := fun i =>
    match i with | none => none | some j => some (some j)
  have hg := hf.reindex r
  have hi : IsSemialgebraic {v : Option (Option σ) → ℝ | v (some none) < v none} := by
    refine ⟨.positive (MvPolynomial.X none - MvPolynomial.X (some none)), ?_⟩
    intro v
    simp [PolynomialFormula.Holds, sub_pos]
  have h := (hg.inter hi).scalar_projection
  convert h using 1
  ext v
  change v none < f (fun i => v (some i)) ↔
    ∃ t : ℝ, t = f (fun i => v (some i)) ∧ v none < t
  simp

theorem semialgebraic_above_of_graph {f : (σ → ℝ) → ℝ}
    (hf : IsSemialgebraic {v : Option σ → ℝ | v none = f (fun i => v (some i))}) :
    IsSemialgebraic {v : Option σ → ℝ | f (fun i => v (some i)) < v none} := by
  let r : Option σ → Option (Option σ) := fun i =>
    match i with | none => none | some j => some (some j)
  have hg := hf.reindex r
  have hi : IsSemialgebraic {v : Option (Option σ) → ℝ | v none < v (some none)} := by
    refine ⟨.positive (MvPolynomial.X (some none) - MvPolynomial.X none), ?_⟩
    intro v
    simp [PolynomialFormula.Holds, sub_pos]
  have h := (hg.inter hi).scalar_projection
  convert h using 1
  ext v
  change f (fun i => v (some i)) < v none ↔
    ∃ t : ℝ, t = f (fun i => v (some i)) ∧ t < v none
  simp

theorem orderedFiberRoot_below_semialgebraic {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      v none < orderedFiberRoot p k (fun i => v (some i))} :=
  semialgebraic_below_of_graph (orderedFiberRoot_graph_semialgebraic p k)

theorem orderedFiberRoot_above_semialgebraic {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      orderedFiberRoot p k (fun i => v (some i)) < v none} :=
  semialgebraic_above_of_graph (orderedFiberRoot_graph_semialgebraic p k)

theorem orderedFiberRoot_band_semialgebraic {n : ℕ}
    (p q : MvPolynomial (Option (Fin n)) ℝ) (j k : ℕ) {S : Set (Vec n)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : Option (Fin n) → ℝ | (fun i => v (some i)) ∈ S ∧
      orderedFiberRoot p j (fun i => v (some i)) < v none ∧
        v none < orderedFiberRoot q k (fun i => v (some i))} := by
  exact (hS.reindex some).inter ((orderedFiberRoot_above_semialgebraic p j).inter
    (orderedFiberRoot_below_semialgebraic q k))

end BfgsVerification.RealAlgebraicGeometry
