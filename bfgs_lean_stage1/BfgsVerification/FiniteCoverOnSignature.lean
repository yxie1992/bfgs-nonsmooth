import BfgsVerification.ActualCellFormulaCover
import BfgsVerification.FiniteRootSignatureCover
import BfgsVerification.BoundarySignTargets

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n m : ℕ}

def SmoothCoverDimension (n : ℕ) : Prop :=
  ∀ S : Set (Vec n), IsSemialgebraic S → HasFiniteSmoothSemialgebraicCover S

theorem restricted_formula_cover_iUnion {ι : Type*} [Fintype ι]
    (f : PolynomialFormula (Option (Fin n))) (S : ι → Set (Vec n))
    (h : ∀ i, HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun j => v (some j)) ∈ S i ∧ f.Holds v}) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun j => v (some j)) ∈ ⋃ i, S i ∧ f.Holds v} := by
  convert HasFiniteSmoothSemialgebraicCover.iUnion h using 1
  ext v
  simp only [mem_setOf_eq,mem_iUnion,exists_and_right]

theorem formula_cover_on_root_component
    (f : PolynomialFormula (Option (Fin n))) (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p)
    (Z : Finset (Fin m)) (a : Vec n) (S : Set (Vec n))
    (hsa : IsSemialgebraic S) (hpath : PiecewiseSmoothConnected S)
    (hzero : S ⊆ zeroFiberPattern P Z)
    (hS : S ⊆ rootSignatureStratum
      (MvPolynomial.optionEquivLeft ℝ (Fin n) (survivingPolynomialProduct P Z)) a)
    (signs : Fin m → Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card → SignType)
    (hboundary : ∀ x ∈ S, ∀ j i,
      SignType.sign (parameterEval (P j) (x,orderedFiberRoot (survivingPolynomialProduct P Z) i.val x)) = signs j i) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ f.Holds v} := by
  let p := survivingPolynomialProduct P Z
  let R : Fin (fiberPolynomial p a).roots.toFinset.card → Vec n → ℝ :=
    fun i => orderedFiberRoot p i.val
  have hsm := actual_ordered_root_family_smooth p a S hS
  have horder := actual_ordered_root_family_strictMono p a S hS
  have hgraph : ∀ i, IsSemialgebraicCylinder (orderedGraphCell S R i) :=
    fun i => orderedFiberRoot_graph_on_semialgebraic p i.val hsa
  apply formula_cover_from_signed_cylinders f P hP (orderedCylindricalCell S R) S
    (orderedCylindricalCell_semialgebraic S R hsa hgraph)
    (orderedCylindricalCell_piecewiseSmoothConnected S R hpath hsm horder)
    (orderedCylindricalCell_cover S R horder)
  intro c x hx y hy j
  exact input_sign_constant_on_actual_cell P Z a S hpath hzero hS signs hboundary c j hx hy

theorem formula_cover_on_boundary_refinement (ih : SmoothCoverDimension n)
    (f : PolynomialFormula (Option (Fin n))) (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p)
    (Z : Finset (Fin m)) (a : Vec n) (S : Set (Vec n))
    (hsa : IsSemialgebraic S)
    (hzero : S ⊆ zeroFiberPattern P Z)
    (hS : S ⊆ rootSignatureStratum
      (MvPolynomial.optionEquivLeft ℝ (Fin n) (survivingPolynomialProduct P Z)) a)
    (signs : Fin m → Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card → SignType)
    (hboundary : ∀ x ∈ S, ∀ j i,
      SignType.sign (parameterEval (P j) (x,orderedFiberRoot (survivingPolynomialProduct P Z) i.val x)) = signs j i) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ f.Holds v} := by
  classical
  obtain ⟨C,hC,hcover⟩ := ih S hsa
  have hsub : ∀ T : C, (T : Set (Vec n)) ⊆ S := by
    intro T x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨T,mem_iUnion.mpr ⟨T.2,hx⟩⟩
  have h := restricted_formula_cover_iUnion f (fun T : C => (T : Set (Vec n))) (fun T =>
    formula_cover_on_root_component f P hP Z a T (hC T T.2).1 (hC T T.2).2
      ((hsub T).trans hzero) ((hsub T).trans hS) signs
      (fun x hx => hboundary x (hsub T hx)))
  have he : (⋃ T : C, (T : Set (Vec n))) = S := by
    simpa only [Set.iUnion_subtype] using hcover
  simpa only [he] using h

theorem formula_cover_on_root_signature (ih : SmoothCoverDimension n)
    (f : PolynomialFormula (Option (Fin n))) (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p)
    (Z : Finset (Fin m)) (a : Vec n) (S : Set (Vec n))
    (hsa : IsSemialgebraic S)
    (hzero : S ⊆ zeroFiberPattern P Z)
    (hS : S ⊆ rootSignatureStratum
      (MvPolynomial.optionEquivLeft ℝ (Fin n) (survivingPolynomialProduct P Z)) a) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ f.Holds v} := by
  let p := survivingPolynomialProduct P Z
  let R : Fin (fiberPolynomial p a).roots.toFinset.card → Vec n → ℝ :=
    fun i => orderedFiberRoot p i.val
  have hgraph : ∀ i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = R i (fun k => v (some k))} :=
    fun i => orderedFiberRoot_graph_on_semialgebraic p i.val hsa
  have h := restricted_formula_cover_iUnion f (boundarySignStratum P R S) (fun signs =>
    formula_cover_on_boundary_refinement ih f P hP Z a _
      (boundarySignStratum_semialgebraic P R S hsa hgraph signs)
      (fun x hx => hzero hx.1) (fun x hx => hS hx.1) signs
      (fun x hx j i => hx.2 j i))
  simpa only [boundarySignStratum_cover] using h

end RealAlgebraicGeometry
end BfgsVerification
