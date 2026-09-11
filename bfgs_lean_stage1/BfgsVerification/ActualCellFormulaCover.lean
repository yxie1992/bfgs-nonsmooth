import BfgsVerification.ActualRootGapSigns
import BfgsVerification.OrderedRootDefinability

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n m : ℕ}

theorem input_sign_constant_on_actual_cell
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ) (Z : Finset (Fin m))
    (a : Vec n) (S : Set (Vec n)) (hpath : PiecewiseSmoothConnected S)
    (hzero : S ⊆ zeroFiberPattern P Z)
    (hS : S ⊆ rootSignatureStratum
      (MvPolynomial.optionEquivLeft ℝ (Fin n) (survivingPolynomialProduct P Z)) a)
    (signs : Fin m → Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card → SignType)
    (hboundary : ∀ x ∈ S, ∀ j i,
      SignType.sign (parameterEval (P j) (x,orderedFiberRoot (survivingPolynomialProduct P Z) i.val x)) = signs j i)
    (c : Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card ⊕
      Fin ((fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card+1))
    (j : Fin m) {x y : Vec n × ℝ}
    (hx : x ∈ orderedCylindricalCell S
      (fun i : Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card =>
        orderedFiberRoot (survivingPolynomialProduct P Z) i.val) c)
    (hy : y ∈ orderedCylindricalCell S
      (fun i : Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card =>
        orderedFiberRoot (survivingPolynomialProduct P Z) i.val) c) :
    SignType.sign (parameterEval (P j) x) = SignType.sign (parameterEval (P j) y) := by
  cases c with
  | inr k => exact input_sign_constant_on_actual_gap P Z a S hpath hzero hS k j hx hy
  | inl k =>
    have hx' : x = (x.1,orderedFiberRoot (survivingPolynomialProduct P Z) k.val x.1) :=
      Prod.ext rfl hx.2
    have hy' : y = (y.1,orderedFiberRoot (survivingPolynomialProduct P Z) k.val y.1) :=
      Prod.ext rfl hy.2
    calc
      _ = signs j k := by rw [hx']; exact hboundary x.1 hx.1 j k
      _ = _ := by rw [hy']; exact (hboundary y.1 hy.1 j k).symm

theorem formula_cover_from_signed_cylinders {ι : Type*} [Fintype ι]
    (f : PolynomialFormula (Option (Fin n))) (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p)
    (C : ι → Set (Vec n × ℝ)) (S : Set (Vec n))
    (hsa : ∀ i, IsSemialgebraicCylinder (C i))
    (hpath : ∀ i, PiecewiseSmoothConnected (C i))
    (hcover : (⋃ i, C i) = {z : Vec n × ℝ | z.1 ∈ S})
    (hsign : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, ∀ j,
      SignType.sign (parameterEval (P j) x) = SignType.sign (parameterEval (P j) y)) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ f.Holds v} := by
  classical
  let G : (Vec n × ℝ) → (Option (Fin n) → ℝ) := fun z => parameterPoint z.1 z.2
  let D : Finset (Set (Option (Fin n) → ℝ)) := Finset.univ.image (fun i => G '' C i)
  have hD : ∀ T ∈ D, IsSemialgebraic T ∧ PiecewiseSmoothConnected T := by
    intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    exact ⟨parameterPoint_image_semialgebraic (hsa i),(hpath i).image parameterPoint_contDiff.contDiffOn⟩
  have hbase : ∀ i, ∀ z ∈ C i, z.1 ∈ S := by
    intro i z hz
    have hm : z ∈ ⋃ i, C i := mem_iUnion.mpr ⟨i,hz⟩
    rwa [hcover] at hm
  apply finite_smooth_cover_select D hD
  · intro v hv
    have hm : ((fun i => v (some i)),v none) ∈ ⋃ i, C i := by rw [hcover]; exact hv.1
    obtain ⟨i,hi⟩ := mem_iUnion.mp hm
    exact mem_iUnion.mpr ⟨G '' C i,mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,
        ((fun j => v (some j)),v none),hi,parameterPoint_recover v⟩⟩
  · intro T hT x hx y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    change (u.1 ∈ S ∧ f.Holds (G u)) ↔ (v.1 ∈ S ∧ f.Holds (G v))
    simp only [hbase i u hu,hbase i v hv,true_and]
    rw [f.holds_iff_signHolds,f.holds_iff_signHolds]
    apply f.signHolds_congr
    intro p hp
    obtain ⟨j,rfl⟩ := hP p hp
    exact hsign i u hu v hv j

end RealAlgebraicGeometry
end BfgsVerification
