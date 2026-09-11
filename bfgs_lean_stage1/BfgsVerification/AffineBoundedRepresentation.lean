import BfgsVerification.PlanarActiveGeometry
import Mathlib.LinearAlgebra.AffineSpace.Basis

/-! The finite affine representation used in Module A's quantified description.
Coefficients are signed real numbers; this is not convex Carathéodory. -/
noncomputable section
open scoped BigOperators
open Set

namespace BfgsVerification
namespace AffineSupportPath
open AffineCriticalObjective ConvexSubdifferential

/-- Every actual affine member in dimension n has an affine representation by
at most n+1 members of the original set, with no rank hypothesis on that set. -/
theorem affine_representation_bounded {n : ℕ} {S : Set (Vec n)} {z : Vec n}
    (hz : z ∈ affineSpan ℝ S) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n + 1 ∧ ∃ g : Fin m → Vec n, ∃ w : Fin m → ℝ,
      (∀ i, g i ∈ S) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • g i) = z := by
  classical
  obtain ⟨T,hTS,hspan,hind⟩ := exists_affineIndependent ℝ (Vec n) S
  have hfin : T.Finite := finite_set_of_fin_dim_affineIndependent ℝ hind
  letI : Fintype T := hfin.fintype
  let m := Fintype.card T
  let e : Fin m ≃ T := (Fintype.equivFin T).symm
  let g : Fin m → Vec n := fun i => e i
  have hgrange : range g = T := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hv
      exact ⟨e.symm ⟨v,hv⟩,by simp only [g,Equiv.apply_symm_apply]⟩
  have hzm : z ∈ affineSpan ℝ (range g) := by rwa [hgrange,hspan]
  obtain ⟨w,hw,he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hzm
  have hmn : m ≤ n+1 := by
    have hb := hind.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℝ (range ((↑) : T → Vec n)))
    have hn : Module.finrank ℝ (Vec n) = n := by simp [Vec]
    rw [hn] at hd
    exact hb.trans (Nat.add_le_add_right hd 1)
  have hmpos : 0 < m := by
    have hs : (Finset.univ : Finset (Fin m)).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      simp only [hempty,Finset.sum_empty] at hw
      norm_num at hw
    simpa using Finset.card_pos.mpr hs
  refine ⟨m,hmpos,hmn,g,w,fun i => hTS (e i).property,hw,?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at he
  exact he.symm

/-- The actual affine-critical predicate has a bounded existential description
using actual global supporting vectors and signed coefficients. -/
theorem isAffineCritical_iff_bounded_supports {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    IsAffineCritical F x ↔ ∃ m : ℕ, 0 < m ∧ m ≤ n + 1 ∧
      ∃ g : Fin m → Vec n, ∃ w : Fin m → ℝ,
        (∀ i, Homogeneous.Supports F x (g i)) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • g i) = 0 := by
  rw [isAffineCritical_iff_coordinate_affineSpan]
  constructor
  · exact affine_representation_bounded
  · rintro ⟨m,hm,hmb,g,w,hg,hw,he⟩
    rw [← he]
    have hmem := affineCombination_mem_affineSpan hw g
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hmem
    exact affineSpan_mono ℝ (by rintro v ⟨i,rfl⟩; exact hg i) hmem

end AffineSupportPath
end BfgsVerification
