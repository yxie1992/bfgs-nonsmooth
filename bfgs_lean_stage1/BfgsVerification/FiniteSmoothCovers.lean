import BfgsVerification.SmoothPathTargets
import BfgsVerification.BooleanPolynomialProjection

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*} [Fintype σ]

/-- An actual finite cover, with semialgebraic pieces joined by actual smooth
paths except at finitely many interior parameters. This predicate itself does
not assert that every semialgebraic set has such a cover. -/
def HasFiniteSmoothSemialgebraicCover (S : Set (σ → ℝ)) : Prop :=
  ∃ C : Finset (Set (σ → ℝ)),
    (∀ T ∈ C, IsSemialgebraic T ∧ PiecewiseSmoothConnected T) ∧ ⋃ T ∈ C, T = S

theorem HasFiniteSmoothSemialgebraicCover.of_connected {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) (hc : PiecewiseSmoothConnected S) :
    HasFiniteSmoothSemialgebraicCover S := by
  classical
  refine ⟨{S},?_,by simp⟩
  intro T hT
  have he := Finset.mem_singleton.mp hT
  subst T
  exact ⟨hS,hc⟩

theorem HasFiniteSmoothSemialgebraicCover.empty :
    HasFiniteSmoothSemialgebraicCover (∅ : Set (σ → ℝ)) := by
  refine ⟨∅,by simp,by simp⟩

theorem HasFiniteSmoothSemialgebraicCover.iUnion {ι : Type*} [Fintype ι]
    {S : ι → Set (σ → ℝ)} (hS : ∀ i, HasFiniteSmoothSemialgebraicCover (S i)) :
    HasFiniteSmoothSemialgebraicCover (⋃ i, S i) := by
  classical
  choose C hC hcover using hS
  refine ⟨Finset.univ.biUnion C,?_,?_⟩
  · intro T hT
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hT
    exact hC i T hi
  · ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨T,hT,hx⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hT
      refine ⟨i,?_⟩
      rw [← hcover i]
      exact mem_iUnion.mpr ⟨T,mem_iUnion.mpr ⟨hi,hx⟩⟩
    · rintro ⟨i,hx⟩
      rw [← hcover i] at hx
      obtain ⟨T,hTx⟩ := mem_iUnion.mp hx
      obtain ⟨hT,hx⟩ := mem_iUnion.mp hTx
      exact ⟨T,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hT⟩,hx⟩

/-- Selecting whole compatible pieces of an existing finite cover preserves
that cover's geometry. No subset of a piece is assumed to retain paths. -/
theorem finite_smooth_cover_select (C : Finset (Set (σ → ℝ)))
    (hC : ∀ T ∈ C, IsSemialgebraic T ∧ PiecewiseSmoothConnected T)
    {S : Set (σ → ℝ)} (hsub : S ⊆ ⋃ T ∈ C, T)
    (hcompatible : ∀ T ∈ C, ∀ x ∈ T, ∀ y ∈ T, x ∈ S ↔ y ∈ S) :
    HasFiniteSmoothSemialgebraicCover S := by
  classical
  let D := C.filter (fun T => ∃ x ∈ T, x ∈ S)
  refine ⟨D,fun T hT => hC T (Finset.mem_filter.mp hT).1,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨T,hTx⟩ := mem_iUnion.mp hx
    obtain ⟨hT,hxT⟩ := mem_iUnion.mp hTx
    obtain ⟨hTC,y,hyT,hyS⟩ := Finset.mem_filter.mp hT
    exact (hcompatible T hTC y hyT x hxT).mp hyS
  · intro hx
    obtain ⟨T,hTx⟩ := mem_iUnion.mp (hsub hx)
    obtain ⟨hT,hxT⟩ := mem_iUnion.mp hTx
    exact mem_iUnion.mpr ⟨T,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hT,x,hxT,hx⟩,hxT⟩⟩

/-- A sign-invariant finite cover of the ambient space yields the desired
actual finite smooth cover of every supplied Boolean polynomial formula. -/
theorem PolynomialFormula.finite_smooth_cover_of_sign_cover (f : PolynomialFormula σ)
    (C : Finset (Set (σ → ℝ)))
    (hC : ∀ T ∈ C, IsSemialgebraic T ∧ PiecewiseSmoothConnected T)
    (hcover : ⋃ T ∈ C, T = univ)
    (hsign : ∀ T ∈ C, ∀ x ∈ T, ∀ y ∈ T, ∀ p ∈ f.atomPolynomials,
      SignType.sign (MvPolynomial.eval x p) = SignType.sign (MvPolynomial.eval y p)) :
    HasFiniteSmoothSemialgebraicCover {x | f.Holds x} := by
  apply finite_smooth_cover_select C hC (by rw [hcover]; exact subset_univ _)
  intro T hT x hx y hy
  change f.Holds x ↔ f.Holds y
  rw [f.holds_iff_signHolds,f.holds_iff_signHolds]
  exact f.signHolds_congr (hsign T hT x hx y hy)

theorem finite_smooth_cover_dimension_zero {S : Set (Fin 0 → ℝ)}
    (hS : IsSemialgebraic S) : HasFiniteSmoothSemialgebraicCover S := by
  apply HasFiniteSmoothSemialgebraicCover.of_connected hS
  intro x hx y hy
  have he : y = x := Subsingleton.elim _ _
  rw [he]
  exact PiecewiseSmoothPathIn.refl hx

end RealAlgebraicGeometry
end BfgsVerification
