import BfgsVerification.SemialgebraicMapGraphs

noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]

theorem semialgebraic_scalar_graph_polynomial (p : MvPolynomial σ ℝ)
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : Option σ → ℝ | (fun i => v (some i)) ∈ S ∧
      v none = MvPolynomial.eval (fun i => v (some i)) p} := by
  have he := isSemialgebraic_equal_zero
    (X none - rename some p : MvPolynomial (Option σ) ℝ)
  convert (hS.reindex some).inter he using 1
  ext v
  simp only [mem_inter_iff,mem_setOf_eq,MvPolynomial.eval_sub,MvPolynomial.eval_X,
    MvPolynomial.eval_rename,Function.comp_def,sub_eq_zero]

theorem semialgebraic_scalar_graph_const {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) (c : ℝ) :
    IsSemialgebraic {v : Option σ → ℝ | (fun i => v (some i)) ∈ S ∧ v none = c} := by
  simpa only [MvPolynomial.eval_C] using semialgebraic_scalar_graph_polynomial (C c) hS

/-- The literal Option-coordinate graph lift of an actual scalar function. -/
theorem IsSemialgebraicMapOn.graph_lift {S : Set (σ → ℝ)} (hS : IsSemialgebraic S)
    {f : (σ → ℝ) → ℝ} (hf : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))}) :
    IsSemialgebraicMapOn (fun x j => Option.elim j (f x) x) S := by
  apply IsSemialgebraicMapOn.coordinatewise hS
  intro j
  cases j with
  | none => exact hf
  | some i =>
    simpa only [MvPolynomial.eval_X] using semialgebraic_scalar_graph_polynomial (X i) hS

/-- Actual restricted scalar graphs are closed under real affine combinations.
The witnesses in the eliminated coordinates are exactly the two function values. -/
theorem semialgebraic_scalar_graph_affine {S : Set (σ → ℝ)} {f g : (σ → ℝ) → ℝ}
    (hf : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))})
    (hg : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = g (fun i => v (some i))}) (a b c : ℝ) :
    IsSemialgebraic {v : Option σ → ℝ | (fun i => v (some i)) ∈ S ∧
      v none = a * f (fun i => v (some i)) + b * g (fun i => v (some i)) + c} := by
  let r : Bool → Option σ → Option σ ⊕ Bool := fun flag j =>
    Option.elim j (.inr flag) (fun i => .inl (some i))
  let P : MvPolynomial (Option σ ⊕ Bool) ℝ :=
    X (.inl none) - (C a * X (.inr false) + C b * X (.inr true) + C c)
  have h := coordinate_projection_semialgebraic
    (((hf.reindex (r false)).inter (hg.reindex (r true))).inter (isSemialgebraic_equal_zero P))
  convert h using 1
  ext v
  change (_ ∈ S ∧ _ = _) ↔ ∃ y : Bool → ℝ, _
  simp only [mem_inter_iff,mem_setOf_eq,r,P,Option.elim_none,Option.elim_some,
    Sum.elim_inl,Sum.elim_inr,MvPolynomial.eval_sub,MvPolynomial.eval_add,
    MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,sub_eq_zero]
  constructor
  · rintro ⟨hx,he⟩
    refine ⟨fun flag => if flag then g (fun i => v (some i)) else f (fun i => v (some i)),?_⟩
    dsimp only [Bool.false_eq_true,ite_false,ite_true]
    exact ⟨⟨⟨hx,rfl⟩,hx,rfl⟩,he⟩
  · rintro ⟨y,⟨⟨hx,hf'⟩,_,hg'⟩,he⟩
    exact ⟨hx,by simpa only [hf',hg'] using he⟩

end RealAlgebraicGeometry
end BfgsVerification
