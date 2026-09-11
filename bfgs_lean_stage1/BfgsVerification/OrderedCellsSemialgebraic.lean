import BfgsVerification.OrderedGapConnectivity
import BfgsVerification.GeneralCoordinateProjection

/-! The actual graph/gap sets are semialgebraic when the base and the actual
boundary graphs are semialgebraic. Strict graph-side inequalities are derived
by proved scalar projection, not assumed graph regularity. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

def IsSemialgebraicCylinder {n : ℕ} (T : Set (Vec n × ℝ)) : Prop :=
  IsSemialgebraic {v : Option (Fin n) → ℝ | ((fun i => v (some i)), v none) ∈ T}

theorem restricted_graph_sides_semialgebraic {n : ℕ} {S : Set (Vec n)} {f : Vec n → ℝ}
    (hgraph : IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))}) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none < f (fun i => v (some i))} ∧
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ f (fun i => v (some i)) < v none} := by
  let r : Option (Fin n) → Option (Option (Fin n)) := fun j =>
    match j with
    | none => none
    | some i => some (some i)
  have hG := hgraph.reindex r
  have hL := (hG.inter (isSemialgebraic_positive
    (X none - X (some none) : MvPolynomial (Option (Option (Fin n))) ℝ))).scalar_projection
  have hU := (hG.inter (isSemialgebraic_positive
    (X (some none) - X none : MvPolynomial (Option (Option (Fin n))) ℝ))).scalar_projection
  constructor
  · convert hL using 1
    ext v
    simp only [mem_setOf_eq, mem_inter_iff, eval_sub, eval_X, r]
    constructor
    · rintro ⟨hx, ht⟩
      exact ⟨f (fun i => v (some i)), ⟨hx, rfl⟩, sub_pos.mpr ht⟩
    · rintro ⟨t, ⟨hx, he⟩, ht⟩
      exact ⟨hx, he ▸ sub_pos.mp ht⟩
  · convert hU using 1
    ext v
    simp only [mem_setOf_eq, mem_inter_iff, eval_sub, eval_X, r]
    constructor
    · rintro ⟨hx, ht⟩
      exact ⟨f (fun i => v (some i)), ⟨hx, rfl⟩, sub_pos.mpr ht⟩
    · rintro ⟨t, ⟨hx, he⟩, ht⟩
      exact ⟨hx, he ▸ sub_pos.mp ht⟩

theorem orderedGapCell_semialgebraic {n r : ℕ} (S : Set (Vec n))
    (f : Fin r → Vec n → ℝ) (hS : IsSemialgebraic S)
    (hf : ∀ i, IsSemialgebraicCylinder (orderedGraphCell S f i)) (j : Fin (r+1)) :
    IsSemialgebraicCylinder (orderedGapCell S f j) := by
  classical
  have hbase := hS.reindex some
  have hsides : ∀ i, IsSemialgebraic {v : Option (Fin n) → ℝ |
        (fun k => v (some k)) ∈ S ∧ v none < f i (fun k => v (some k))} ∧
      IsSemialgebraic {v : Option (Fin n) → ℝ |
        (fun k => v (some k)) ∈ S ∧ f i (fun k => v (some k)) < v none} :=
    fun i => restricted_graph_sides_semialgebraic (hf i)
  have hL := isSemialgebraic_forall_finite
    (fun i : Fin r => {v : Option (Fin n) → ℝ | i.val < j.val →
      (fun k => v (some k)) ∈ S ∧ f i (fun k => v (some k)) < v none})
    (fun i => by
      by_cases h : i.val < j.val
      · simpa only [h, true_implies] using (hsides i).2
      · simpa only [h, false_implies, setOf_true] using
          (isSemialgebraic_univ (σ := Option (Fin n))))
  have hU := isSemialgebraic_forall_finite
    (fun i : Fin r => {v : Option (Fin n) → ℝ | j.val ≤ i.val →
      (fun k => v (some k)) ∈ S ∧ v none < f i (fun k => v (some k))})
    (fun i => by
      by_cases h : j.val ≤ i.val
      · simpa only [h, true_implies] using (hsides i).1
      · simpa only [h, false_implies, setOf_true] using
          (isSemialgebraic_univ (σ := Option (Fin n))))
  have h := hbase.inter (hL.inter hU)
  unfold IsSemialgebraicCylinder
  convert h using 1
  ext v
  simp only [IsSemialgebraicCylinder, orderedGapCell, mem_setOf_eq, mem_inter_iff]
  constructor
  · rintro ⟨hx, hL, hU⟩
    exact ⟨hx, fun i hi => ⟨hx, hL i hi⟩, fun i hi => ⟨hx, hU i hi⟩⟩
  · rintro ⟨hx, hL, hU⟩
    exact ⟨hx, fun i hi => (hL i hi).2, fun i hi => (hU i hi).2⟩

theorem orderedCylindricalCell_semialgebraic {n r : ℕ} (S : Set (Vec n))
    (f : Fin r → Vec n → ℝ) (hS : IsSemialgebraic S)
    (hf : ∀ i, IsSemialgebraicCylinder (orderedGraphCell S f i))
    (i : Fin r ⊕ Fin (r+1)) : IsSemialgebraicCylinder (orderedCylindricalCell S f i) := by
  rcases i with i | j
  · exact hf i
  · exact orderedGapCell_semialgebraic S f hS hf j

end RealAlgebraicGeometry
end BfgsVerification
