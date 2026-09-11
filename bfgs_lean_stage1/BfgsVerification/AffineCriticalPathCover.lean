import BfgsVerification.FiniteAffineCriticalValues
import BfgsVerification.AffineBoundedRepresentation

/-! Conditional assembly of Module A's path argument. The path and finite-cover
predicates here are explicit geometric inputs, not definitions of semialgebraic
sets and not claimed to follow from semialgebraicity in this module. -/
noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification
namespace AffineSupportPath
open AffineCriticalObjective ConvexSubdifferential

/-- A supplied path and objective composition are differentiable except at
finitely many times. The endpoints require continuity only. -/
def PiecewiseDifferentiablePathIn {n : ℕ} (F : Vec n → ℝ) (S : Set (Vec n))
    (x y : Vec n) : Prop :=
  ∃ p : ℝ → Vec n, ContinuousOn p (Icc 0 1) ∧ p 0 = x ∧ p 1 = y ∧
    (∀ t ∈ Icc 0 1, p t ∈ S) ∧ ∃ s : Finset ℝ,
      ∀ t ∈ Ioo 0 1, t ∉ s →
        DifferentiableAt ℝ p t ∧ DifferentiableAt ℝ (F ∘ p) t

theorem value_eq_of_affineCritical_path {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {S : Set (Vec n)}
    (hS : ∀ x ∈ S, IsAffineCritical F x) {x y : Vec n}
    (hp : PiecewiseDifferentiablePathIn F S x y) : F x = F y := by
  obtain ⟨p,hpc,hp0,hp1,hpS,s,hd⟩ := hp
  have h := objective_constant_on_piecewise_differentiable_path hF s hpc
    (fun t ht => hS _ (hpS t ⟨ht.1.le,ht.2.le⟩))
    (fun t ht hs => (hd t ht hs).1) (fun t ht hs => (hd t ht hs).2)
    1 (by norm_num)
  rw [hp1,hp0] at h
  exact h.symm

/-- A supplied finite cover of the actual affine-critical set by pieces with
the required paths has finite actual objective image. Empty pieces are allowed. -/
theorem finite_values_of_finite_path_cover {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (C : Fin m → Set (Vec n))
    (hcover : {p | IsAffineCritical F p} = ⋃ i, C i)
    (hpaths : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, PiecewiseDifferentiablePathIn F (C i) x y) :
    (F '' {p | IsAffineCritical F p}).Finite := by
  have hsingle : ∀ i, (F '' C i).Subsingleton := by
    intro i a ha b hb
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    apply value_eq_of_affineCritical_path hF _ (hpaths i x hx y hy)
    intro p hp
    change p ∈ {p | IsAffineCritical F p}
    rw [hcover]
    exact mem_iUnion.mpr ⟨i,hp⟩
  rw [hcover,image_iUnion]
  exact Set.finite_iUnion (fun i => (hsingle i).finite)

/-- Final low-level consequence under an explicit finite path-cover premise.
The missing real-algebraic projection and path-decomposition theorems are not
hidden in this statement. -/
theorem low_level_affine_correct_of_finite_path_cover {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (C : Fin m → Set (Vec n))
    (hcover : {p | IsAffineCritical F p} = ⋃ i, C i)
    (hpaths : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, PiecewiseDifferentiablePathIn F (C i) x y)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p, F p < F star + ε →
      IsAffineCritical F p → (0 : Vec n) ∈ subdifferential F p :=
  low_level_affine_correct_of_finite_values
    (finite_values_of_finite_path_cover hF C hcover hpaths) star hmin

end AffineSupportPath
end BfgsVerification
