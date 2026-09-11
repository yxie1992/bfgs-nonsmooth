import BfgsVerification.ScalarGraphRoots

noncomputable section
open Set Filter Polynomial
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry

/-- A graph equality restricted to the actual function domain is obtained by
intersecting the two genuine graphs and projecting their common height. -/
theorem semialgebraic_function_root_equality {n : ℕ} {F : Vec n → ℝ} {D : Set (Vec n)}
    (hF : IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ D ∧ v none = F (fun i => v (some i))})
    (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    IsSemialgebraic {x : Vec n | x ∈ D ∧ F x = orderedFiberRoot p k x} := by
  have h := (hF.inter (orderedFiberRoot_graph_semialgebraic p k)).scalar_projection
  convert h using 1
  ext x
  change (x ∈ D ∧ F x = orderedFiberRoot p k x) ↔
    ∃ t, (x ∈ D ∧ t = F x) ∧ t = orderedFiberRoot p k x
  aesop

/-- Every actual semialgebraic scalar graph has a finite semialgebraic cover
of its domain on which the function is smooth. Smoothness on a lower-dimensional
piece means the actual ambient smooth extension notion of `ContDiffOn`. -/
theorem semialgebraic_function_finite_smooth_pieces {n : ℕ} {F : Vec n → ℝ}
    {D : Set (Vec n)}
    (hF : IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ D ∧ v none = F (fun i => v (some i))}) :
    ∃ C : Finset (Set (Vec n)),
      (∀ S ∈ C, IsSemialgebraic S ∧ ContDiffOn ℝ ∞ F S) ∧ ⋃ S ∈ C, S = D := by
  classical
  obtain ⟨f,hf⟩ := hF
  let e := Fintype.equivFin f.atomPolynomials
  let m := Fintype.card f.atomPolynomials
  let P : Fin m → MvPolynomial (Option (Fin n)) ℝ := fun i => (e.symm i).val
  have hP : ∀ p ∈ f.atomPolynomials, ∃ i, P i = p := by
    intro p hp
    refine ⟨e ⟨p,hp⟩,?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨p,hp⟩)
  let p := survivingPolynomialProduct P
  let q := fun Z => MvPolynomial.optionEquivLeft ℝ (Fin n) (p Z)
  choose C hC hcover using fun Z : Finset (Fin m) => finite_rootSignature_cover (q Z)
  let I := Σ Z : Finset (Fin m), Σ a : C Z, Fin (fiberPolynomial (p Z) a).roots.toFinset.card
  let S : I → Set (Vec n) := fun i => zeroFiberPattern P i.1 ∩
    rootSignatureStratum (q i.1) i.2.1 ∩
      {x | x ∈ D ∧ F x = orderedFiberRoot (p i.1) i.2.2.val x}
  have hS : ∀ i : I, IsSemialgebraic (S i) ∧ ContDiffOn ℝ ∞ F (S i) := by
    intro i
    have hroot := orderedFiberRoot_contDiffOn_signature (p i.1) i.2.1 i.2.2.isLt
    refine ⟨((zeroFiberPattern_semialgebraic P i.1).inter
      (hC i.1 i.2.1 i.2.1.2)).inter ?_,?_⟩
    · exact semialgebraic_function_root_equality ⟨f,hf⟩ _ _
    · exact (hroot.mono (fun x hx => hx.1.2)).congr (fun x hx => hx.2.2)
  have hScov : ⋃ i, S i = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hx⟩ := mem_iUnion.mp hx
      exact hx.2.1
    · intro hx
      let Z := Finset.univ.filter (fun i : Fin m => fiberPolynomial (P i) x = 0)
      have hxZ : x ∈ zeroFiberPattern P Z := by intro i; simp only [Z,Finset.mem_filter,Finset.mem_univ,true_and]
      have hxr : x ∈ ⋃ a ∈ C Z, rootSignatureStratum (q Z) a := by
        rw [hcover Z]
        exact mem_univ _
      obtain ⟨a,hax⟩ := mem_iUnion.mp hxr
      obtain ⟨ha,hxa⟩ := mem_iUnion.mp hax
      have ht : f.Holds (parameterPoint x (F x)) := (hf _).mp ⟨hx,rfl⟩
      have huniq : ∀ t, f.Holds (parameterPoint x t) → t = F x := by
        intro t ht
        exact ((hf _).mpr ht).2
      have hroot := singleton_formula_fiber_is_surviving_root f P hP Z x hxZ (F x) ht huniq
      obtain ⟨k,hk,hke⟩ := (isRoot_iff_exists_orderedRealRoot (fiberPolynomial (p Z) x)
        (survivingProduct_fiber_nonzero P Z hxZ) (F x)).mp hroot
      have hc : (fiberPolynomial (p Z) x).roots.toFinset.card =
          (fiberPolynomial (p Z) a).roots.toFinset.card := by
        simpa only [q,← fiberPolynomial_eq_map] using hxa.2.1
      let i : I := ⟨Z,⟨a,ha⟩,⟨k,hc ▸ hk⟩⟩
      exact mem_iUnion.mpr ⟨i,⟨hxZ,hxa⟩,hx,hke.symm⟩
  refine ⟨Finset.univ.image S,?_,?_⟩
  · intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    exact hS i
  · simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.iUnion_exists,
      Set.iUnion_iUnion_eq',Set.iUnion_true] using hScov

end BfgsVerification.RealAlgebraicGeometry
