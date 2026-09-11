import BfgsVerification.ParameterRootPersistence
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- The actual distinct roots in a specified real set. -/
def rootsIn (p : Polynomial ℝ) (I : Set ℝ) : Finset ℝ := by
  classical
  exact p.roots.toFinset.filter (· ∈ I)

/-- Total actual real-root multiplicity in a specified set. -/
def rootWeightIn (p : Polynomial ℝ) (I : Set ℝ) : ℕ :=
  ∑ x ∈ rootsIn p I, p.rootMultiplicity x

theorem rootsIn_derivative_interleaving_bound (p : Polynomial ℝ) (I : Set ℝ)
    (hI : OrdConnected I) :
    (rootsIn p I).card ≤ ((rootsIn p.derivative I) \ (rootsIn p I)).card+1 := by
  classical
  by_cases hd : p.derivative=0
  · rw [Polynomial.eq_C_of_derivative_eq_zero hd]
    simp [rootsIn]
  have hp : p≠0 := by intro hz; exact hd (by simp [hz])
  apply Finset.card_le_diff_of_interleaved
  intro x hx y hy hxy _
  obtain ⟨hxroot,hxI⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyroot,hyI⟩ := Finset.mem_filter.mp hy
  have hpx := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hxroot)
  have hpy := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hyroot)
  obtain ⟨z,hz,hder⟩ := exists_deriv_eq_zero hxy p.continuousOn (hpx.trans hpy.symm)
  refine ⟨z, ?_, hz⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hI.out hxI hyI ⟨hz.1.le,hz.2.le⟩⟩
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hd).mpr
  simpa only [Polynomial.IsRoot, ← p.deriv] using hder

theorem rootWeightIn_le_derivative_add_one (p : Polynomial ℝ) (I : Set ℝ)
    (hI : OrdConnected I) : rootWeightIn p I ≤ rootWeightIn p.derivative I+1 := by
  classical
  let S := rootsIn p I
  let T := rootsIn p.derivative I
  have hpos : ∀ x ∈ S, 1 ≤ p.rootMultiplicity x := by
    intro x hx
    have hr := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1
    exact (Polynomial.rootMultiplicity_pos (Polynomial.ne_zero_of_mem_roots hr)).mpr
      (Polynomial.isRoot_of_mem_roots hr)
  have htpos : ∀ x ∈ T, 1 ≤ p.derivative.rootMultiplicity x := by
    intro x hx
    have hr := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1
    exact (Polynomial.rootMultiplicity_pos (Polynomial.ne_zero_of_mem_roots hr)).mpr
      (Polynomial.isRoot_of_mem_roots hr)
  have hzero : ∀ x ∈ S ∪ T, x ∉ T → p.derivative.rootMultiplicity x=0 := by
    intro x hx hxt
    have hxI : x ∈ I := by
      rcases Finset.mem_union.mp hx with hs | ht
      · exact (Finset.mem_filter.mp hs).2
      · exact (Finset.mem_filter.mp ht).2
    by_cases hd : p.derivative=0
    · simp [hd]
    · apply Polynomial.rootMultiplicity_eq_zero
      intro hr
      exact hxt (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr hr),hxI⟩)
  calc
    rootWeightIn p I = ∑ x ∈ S, (p.rootMultiplicity x-1+1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Nat.sub_add_cancel (hpos x hx)).symm
    _ = (∑ x ∈ S, (p.rootMultiplicity x-1))+S.card := by
      simp [Finset.sum_add_distrib]
    _ ≤ (∑ x ∈ S, p.derivative.rootMultiplicity x)+((T \ S).card+1) :=
      add_le_add (Finset.sum_le_sum (fun x _ =>
        Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity p x))
        (rootsIn_derivative_interleaving_bound p I hI)
    _ ≤ (∑ x ∈ S, p.derivative.rootMultiplicity x)+
        ((∑ x ∈ T \ S, p.derivative.rootMultiplicity x)+1) := by
      apply Nat.add_le_add_left
      apply Nat.add_le_add_right
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun x hx => htpos x (Finset.mem_sdiff.mp hx).1)
    _ = rootWeightIn p.derivative I+1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union]
      congr 1
      exact (Finset.sum_subset Finset.subset_union_right hzero).symm

end RealAlgebraicGeometry
end BfgsVerification
