import BfgsVerification.PolynomialZeroPatterns
import BfgsVerification.OrderedRootDefinability

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem finite_range_representatives {E A : Type*} (f : E → A) (hf : (Set.range f).Finite) :
    ∃ C : Finset E, ∀ x : E, ∃ a ∈ C, f x = f a := by
  classical
  letI : Fintype (Set.range f) := hf.fintype
  choose g hg using (fun a : Set.range f => a.property)
  refine ⟨Finset.univ.image g,?_⟩
  intro x
  let a : Set.range f := ⟨f x,Set.mem_range_self x⟩
  exact ⟨g a,Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩,(hg a).symm⟩

theorem finiteSemialgebraic_rootSignature {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℝ)) :
    FiniteSemialgebraicFunction (fun x : Vec n =>
      ((p.map (MvPolynomial.eval x)).natDegree,
        (p.map (MvPolynomial.eval x)).roots.toFinset.card,
        (p.map (MvPolynomial.eval x)).roots.card)) :=
  (finiteSemialgebraic_polynomial_degree p).pair
    ((finiteSemialgebraic_distinctRealRootCount p).pair (finiteSemialgebraic_totalRealRootMultiplicity p))

/-- A finite family of actual attained root signatures covers parameter
space. Representatives are selected from the actual finite signature range. -/
theorem finite_rootSignature_cover {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ C : Finset (Vec n), (∀ a ∈ C, IsSemialgebraic (rootSignatureStratum p a)) ∧
      (⋃ a ∈ C, rootSignatureStratum p a) = univ := by
  obtain ⟨C,hC⟩ := finite_range_representatives _ (finiteSemialgebraic_rootSignature p).finite_range
  refine ⟨C,(fun a _ => rootSignatureStratum_semialgebraic p a),?_⟩
  ext x
  simp only [mem_univ,iff_true,mem_iUnion]
  obtain ⟨a,ha,he⟩ := hC x
  refine ⟨a,ha,?_⟩
  exact Prod.mk.inj he |>.imp_right (fun h => Prod.mk.inj h)

end RealAlgebraicGeometry
end BfgsVerification
