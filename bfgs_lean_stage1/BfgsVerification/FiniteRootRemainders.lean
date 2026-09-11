import BfgsVerification.FiniteDegreePrefixes

/-! One finite family of actual lower-degree remainders covers every nonzero
real specialization of an arbitrary-degree divisor, including degree drops. -/
noncomputable section
open Polynomial Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Actual degree decrease and actual sign equivalences at every divisor root. -/
def RootRemainderSigns (p q r : Polynomial ℝ) : Prop :=
  (r=0 ∨ r.natDegree<q.natDegree) ∧
    ∀ t : ℝ, q.eval t=0 →
      (p.eval t=0 ↔ r.eval t=0) ∧
      (0<p.eval t ↔ 0<r.eval t) ∧
      (0≤p.eval t ↔ 0≤r.eval t)

variable {R : Type*} [CommRing R] [IsDomain R]

theorem exists_finite_root_remainders (p q : Polynomial R) :
    ∃ r : Fin (q.natDegree+1) → Polynomial R,
      ∀ f : R →+* ℝ, q.map f≠0 →
        ∃ i, RootRemainderSigns (p.map f) (q.map f) ((r i).map f) := by
  classical
  have hi : ∀ i : Fin (q.natDegree+1), ∃ r : Polynomial R,
      ∀ f : R →+* ℝ, f (degreePrefix q i.val).leadingCoeff≠0 →
        RootRemainderSigns (p.map f) ((degreePrefix q i.val).map f) (r.map f) := by
    intro i
    by_cases hq : degreePrefix q i.val=0
    · refine ⟨0,?_⟩
      intro f hf
      exact (hf (by rw [hq,leadingCoeff_zero,map_zero])).elim
    · obtain ⟨k,Q,r,he,hr,hu⟩ := exists_uniform_positive_pseudoDivision p (degreePrefix q i.val) hq
      exact ⟨r,hu⟩
  choose r hr using hi
  refine ⟨r,?_⟩
  intro f hq
  obtain ⟨N,hN,hmap,hlead⟩ := exists_degreePrefix_specialize q f hq
  let i : Fin (q.natDegree+1) := ⟨N,Finset.mem_range.mp hN⟩
  refine ⟨i,?_⟩
  have h := hr i f hlead
  change RootRemainderSigns (p.map f) ((degreePrefix q N).map f) ((r i).map f) at h
  rwa [hmap] at h

end RealAlgebraicGeometry
end BfgsVerification
