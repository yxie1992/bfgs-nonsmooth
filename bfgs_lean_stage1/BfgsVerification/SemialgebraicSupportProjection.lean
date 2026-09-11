import BfgsVerification.SemialgebraicGraphs
import BfgsVerification.ConvexSubdifferential

/-! Exact reduction of the actual supporting graph to a coordinate projection
of a genuinely semialgebraic set. The projection theorem itself is not proved
or smuggled into the definition of semialgebraicity. -/
noncomputable section
open scoped BigOperators
open Set MvPolynomial

namespace BfgsVerification
namespace RealAlgebraicGeometry

abbrev SupportBase (n : ℕ) := Fin n ⊕ Fin n
abbrev SupportAux (n : ℕ) := Fin n ⊕ Bool
abbrev SupportAll (n : ℕ) := SupportBase n ⊕ SupportAux n

def supportGraph {n : ℕ} (F : Vec n → ℝ) : Set (SupportBase n → ℝ) :=
  {v | Homogeneous.Supports F (fun i => v (.inl i)) (fun i => v (.inr i))}

def oldGraphVars {n : ℕ} (v : SupportAll n → ℝ) : Option (Fin n) → ℝ
  | none => v (.inr (.inr false))
  | some i => v (.inl (.inl i))

def newGraphVars {n : ℕ} (v : SupportAll n → ℝ) : Option (Fin n) → ℝ
  | none => v (.inr (.inr true))
  | some i => v (.inr (.inl i))

def badSupportPolynomial (n : ℕ) : MvPolynomial (SupportAll n) ℝ :=
  (∑ i : Fin n, X (.inl (.inr i)) * (X (.inr (.inl i))-X (.inl (.inl i)))) -
    (X (.inr (.inr true))-X (.inr (.inr false)))

def badSupportSet {n : ℕ} (F : Vec n → ℝ) : Set (SupportAll n → ℝ) :=
  {v | oldGraphVars v ∈ objectiveGraph F ∧ newGraphVars v ∈ objectiveGraph F ∧
    v (.inr (.inr true))-v (.inr (.inr false)) <
      dot (fun i => v (.inl (.inr i)))
        ((fun i => v (.inr (.inl i)))-(fun i => v (.inl (.inl i))))}

theorem badSupportPolynomial_eval {n : ℕ} (v : SupportAll n → ℝ) :
    MvPolynomial.eval v (badSupportPolynomial n) =
      dot (fun i => v (.inl (.inr i)))
        ((fun i => v (.inr (.inl i)))-(fun i => v (.inl (.inl i)))) -
      (v (.inr (.inr true))-v (.inr (.inr false))) := by
  simp [badSupportPolynomial,dot]

/-- For a semialgebraic objective, the lifted violation set is an actual
semialgebraic set before projecting out z, F(x), and F(z). -/
theorem badSupportSet_semialgebraic {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraicObjective F) : IsSemialgebraic (badSupportSet F) := by
  have hold : IsSemialgebraic ((oldGraphVars (n := n)) ⁻¹' objectiveGraph F) := by
    have h := hF.polynomial_preimage (fun o : Option (Fin n) =>
      (X (match o with
        | none => Sum.inr (Sum.inr false)
        | some i => Sum.inl (Sum.inl i)) : MvPolynomial (SupportAll n) ℝ))
    convert h using 1
    ext v
    simp only [mem_preimage,objectiveGraph,mem_setOf_eq,oldGraphVars,MvPolynomial.eval_X]
  have hnew : IsSemialgebraic ((newGraphVars (n := n)) ⁻¹' objectiveGraph F) := by
    have h := hF.polynomial_preimage (fun o : Option (Fin n) =>
      (X (match o with
        | none => Sum.inr (Sum.inr true)
        | some i => Sum.inr (Sum.inl i)) : MvPolynomial (SupportAll n) ℝ))
    convert h using 1
    ext v
    simp only [mem_preimage,objectiveGraph,mem_setOf_eq,newGraphVars,MvPolynomial.eval_X]
  have h := hold.inter (hnew.inter (isSemialgebraic_positive (badSupportPolynomial n)))
  convert h using 1
  ext v
  simp only [badSupportSet,mem_setOf_eq,mem_inter_iff,mem_preimage,
    badSupportPolynomial_eval,sub_pos]

def coordinateProjection {σ τ : Type*} (S : Set ((σ ⊕ τ) → ℝ)) : Set (σ → ℝ) :=
  {x | ∃ y : τ → ℝ, Sum.elim x y ∈ S}

/-- This equality proves the exact quantified supporting-plane description;
there is no projection-closure premise in the equality itself. -/
theorem nonSupportGraph_eq_projection {n : ℕ} (F : Vec n → ℝ) :
    (supportGraph F)ᶜ = coordinateProjection (badSupportSet F) := by
  ext v
  change (¬Homogeneous.Supports F (fun i => v (.inl i)) (fun i => v (.inr i))) ↔ _
  constructor
  · intro h
    change ¬∀ z, dot (fun i => v (.inr i)) (z-(fun i => v (.inl i))) ≤
      F z-F (fun i => v (.inl i)) at h
    push_neg at h
    obtain ⟨z,hz⟩ := h
    refine ⟨Sum.elim z (fun b => if b then F z else F (fun i => v (.inl i))),?_⟩
    simpa only [badSupportSet,mem_setOf_eq,objectiveGraph,oldGraphVars,newGraphVars,
      Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true,true_and] using hz
  · rintro ⟨u,hu⟩ hs
    change oldGraphVars (Sum.elim v u) ∈ objectiveGraph F ∧
      newGraphVars (Sum.elim v u) ∈ objectiveGraph F ∧ _ at hu
    rcases hu with ⟨ha,hb,hbad⟩
    change u (.inr false) = F (fun i => v (.inl i)) at ha
    change u (.inr true) = F (fun i => u (.inl i)) at hb
    have hsupport := hs (fun i => u (.inl i))
    simp only [Sum.elim_inl,Sum.elim_inr] at hbad
    rw [ha,hb] at hbad
    exact (not_lt_of_ge hsupport) hbad

/-- Explicit conditional bridge: a separately proved coordinate projection
result would give semialgebraicity of the actual global supporting graph. -/
theorem supportGraph_semialgebraic_of_projection {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraicObjective F)
    (hprojection : ∀ S : Set (SupportAll n → ℝ), IsSemialgebraic S →
      IsSemialgebraic (coordinateProjection S)) : IsSemialgebraic (supportGraph F) := by
  have h := (hprojection _ (badSupportSet_semialgebraic hF)).compl
  rwa [← nonSupportGraph_eq_projection,compl_compl] at h

end RealAlgebraicGeometry
end BfgsVerification
