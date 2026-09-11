import BfgsVerification.ParameterRootRanks
import BfgsVerification.OrderedRootSmoothCharts

/-! Definability of the actual ordered roots used by the analytic chart
construction. No continuity, root enumeration, or root count is assumed. -/
noncomputable section
open Set Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

variable {n : ℕ}

theorem rootSignatureStratum_semialgebraic
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (a : Vec n) :
    IsSemialgebraic (rootSignatureStratum p a) := by
  exact (finiteSemialgebraic_polynomial_degree p).fiber _ |>.inter
    ((finiteSemialgebraic_distinctRealRootCount p).fiber _ |>.inter
      ((finiteSemialgebraic_totalRealRootMultiplicity p).fiber _))

theorem orderedFiberRoot_valid_graph_semialgebraic
    (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      k < (fiberPolynomial p (fun i => v (some i))).roots.toFinset.card ∧
        v none = orderedFiberRoot p k (fun i => v (some i))} := by
  have h := (zeroFiberCylinder_semialgebraic p).compl.inter
    ((isSemialgebraic_equal_zero p).inter
      ((finiteSemialgebraic_rootBelowCount
        (MvPolynomial.optionEquivLeft ℝ (Fin n) p)).fiber k))
  convert h using 1
  ext v
  simp only [mem_setOf_eq, orderedFiberRoot, orderedRealRoot_valid_iff_root,
    mem_inter_iff, mem_compl_iff, zeroFiberCylinder, ← fiberPolynomial_eq_map]
  have he := verticalDerivative_eval p v 0
  have he' : MvPolynomial.eval v p =
      (fiberPolynomial p (fun i => v (some i))).eval (v none) := by
    simpa only [verticalDerivative, Function.iterate_zero_apply] using he
  rw [he']

theorem orderedFiberRoot_graph_semialgebraic
    (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      v none = orderedFiberRoot p k (fun i => v (some i))} := by
  have hc := ((finiteSemialgebraic_distinctRealRootCount
    (MvPolynomial.optionEquivLeft ℝ (Fin n) p)).reindex (some : Fin n → Option (Fin n))).predicate
      (fun c => c ≤ k)
  have hzero : IsSemialgebraic {v : Option (Fin n) → ℝ | v none = 0} := by
    simpa only [MvPolynomial.eval_X] using
      isSemialgebraic_equal_zero (MvPolynomial.X (none : Option (Fin n)))
  have h := (orderedFiberRoot_valid_graph_semialgebraic p k).union (hc.inter hzero)
  convert h using 1
  ext v
  simp only [mem_setOf_eq, mem_union, mem_inter_iff, ← fiberPolynomial_eq_map,
    orderedFiberRoot]
  rw [orderedRealRoot_valid_iff_root, orderedRealRoot_total_iff]

/-- Any semialgebraic restriction of a parameter root signature has an actual
semialgebraic graph for each valid ordered root. -/
theorem orderedFiberRoot_graph_on_semialgebraic
    (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) {S : Set (Vec n)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = orderedFiberRoot p k (fun i => v (some i))} := by
  have hS' := hS.polynomial_preimage (fun i => MvPolynomial.X (some i))
  simpa only [MvPolynomial.eval_X, Set.preimage_setOf_eq] using
    hS'.inter (orderedFiberRoot_graph_semialgebraic p k)

end BfgsVerification.RealAlgebraicGeometry
