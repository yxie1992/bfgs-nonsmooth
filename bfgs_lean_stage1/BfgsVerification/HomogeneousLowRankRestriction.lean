import BfgsVerification.HomogeneousPlanarEscape
import BfgsVerification.AffineImageLifting
import BfgsVerification.HomogeneousCardinality

/-! Exact finite-subalphabet restriction at accepted differentiable iterates.
This is the actual-objective bridge needed after removing nonrecurrent slopes.
No global objective factorization is inferred from tail gradient membership. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- A differentiable finite maximum of actual distinct slope vectors is locally
its actual linear gradient. Duplicate original indices are already merged by
using a finite set of vectors, not by a genericity assumption. -/
theorem finiteMaxLinear_locally_eq_gradient {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    {x g : Vec n} (hg : HasFDerivAt (finiteMaxLinear A hA) (gradientFunctional g) x) :
    finiteMaxLinear A hA =ᶠ[𝓝 x] (fun z => dot g z) := by
  classical
  have hgm : g ∈ A := finiteMaxLinear_gradient_mem A hA hg
  have hex : dot g x = finiteMaxLinear A hA x :=
    supporting_euler (finiteMaxLinear_homogeneous A hA)
      (convex_supporting_inequality (finiteMaxLinear_convex A hA) hg)
  have hall : ∀ᶠ z in 𝓝 x, ∀ a ∈ A, dot a z ≤ dot g z := by
    apply A.finite_toSet.eventually_all.mpr
    intro a ha
    by_cases he : a = g
    · subst a
      exact Eventually.of_forall (fun _ => le_rfl)
    have hstrict : dot a x < dot g x := by
      have hle := slope_le_finiteMaxLinear A hA ha x
      rw [← hex] at hle
      apply lt_of_le_of_ne hle
      intro h
      exact he (finiteMaxLinear_active_eq_gradient A hA ha (by rw [← hex, h]) hg)
    have hev : ∀ᶠ z in 𝓝 x, (gradientFunctional a) z < (gradientFunctional g) z :=
      (isOpen_lt (gradientFunctional a).continuous (gradientFunctional g).continuous).mem_nhds
        (by simpa only [Set.mem_setOf_eq, gradientFunctional_apply] using hstrict)
    exact hev.mono (fun z hz => by simpa only [gradientFunctional_apply] using hz.le)
  filter_upwards [hall] with z hz
  apply le_antisymm _ (slope_le_finiteMaxLinear A hA hgm z)
  apply Finset.sup'_le
  intro a ha
  exact hz a ha

/-- A subset containing the actual gradient has the same local objective germ
at an accepted point, although the two objectives may differ globally. -/
theorem finiteMaxLinear_restriction_eventuallyEq {n : ℕ}
    (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A)
    {x g : Vec n} (hg : HasFDerivAt (finiteMaxLinear A hA) (gradientFunctional g) x)
    (hgm : g ∈ B) : finiteMaxLinear B hB =ᶠ[𝓝 x] finiteMaxLinear A hA := by
  filter_upwards [finiteMaxLinear_locally_eq_gradient A hA hg] with z hz
  apply le_antisymm
  · apply Finset.sup'_le
    intro b hb
    exact slope_le_finiteMaxLinear A hA (hBA hb) z
  · rw [hz]
    exact slope_le_finiteMaxLinear B hB hgm z

theorem finiteMaxLinear_restriction_hasGradient {n : ℕ}
    (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A)
    {x g : Vec n} (hg : HasFDerivAt (finiteMaxLinear A hA) (gradientFunctional g) x)
    (hgm : g ∈ B) : HasFDerivAt (finiteMaxLinear B hB) (gradientFunctional g) x :=
  hg.congr_of_eventuallyEq (finiteMaxLinear_restriction_eventuallyEq A B hA hB hBA hg hgm)

theorem finiteMaxLinear_restriction_value {n : ℕ}
    (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A)
    {x g : Vec n} (hg : HasFDerivAt (finiteMaxLinear A hA) (gradientFunctional g) x)
    (hgm : g ∈ B) : finiteMaxLinear B hB x = finiteMaxLinear A hA x :=
  (finiteMaxLinear_restriction_eventuallyEq A B hA hB hBA hg hgm).self_of_nhds

end Homogeneous
namespace AdmissibleBFGSRun
open Homogeneous

/-- The exact unchanged accepted run for a retained finite slope subset.
This construction is justified only when each actual gradient is retained. -/
def restrictMaxLinear {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B ⊆ A) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hg : ∀ k, R.g k ∈ B) : AdmissibleBFGSRun n (finiteMaxLinear B hB) where
  convex := finiteMaxLinear_convex B hB
  x := R.x
  H := R.H
  g := R.g
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := R.initial_posDef
  alpha_pos := R.alpha_pos
  gradient_nonzero := R.gradient_nonzero
  hasGradient := fun k => finiteMaxLinear_restriction_hasGradient A B hA hB hBA (R.hasGradient k) (hg k)
  step := R.step
  update := R.update
  armijo := by
    intro k
    rw [finiteMaxLinear_restriction_value A B hA hB hBA (R.hasGradient k) (hg k),
      finiteMaxLinear_restriction_value A B hA hB hBA (R.hasGradient (k + 1)) (hg (k + 1))]
    exact R.armijo k
  weak_wolfe := R.weak_wolfe

@[simp] theorem restrictMaxLinear_x {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty)
    (hB : B.Nonempty) (hBA : B ⊆ A) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hg : ∀ k, R.g k ∈ B) : (restrictMaxLinear A B hA hB hBA R hg).x = R.x := rfl

@[simp] theorem restrictMaxLinear_H {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty)
    (hB : B.Nonempty) (hBA : B ⊆ A) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hg : ∀ k, R.g k ∈ B) : (restrictMaxLinear A B hA hB hBA R hg).H = R.H := rfl

@[simp] theorem restrictMaxLinear_g {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty)
    (hB : B.Nonempty) (hBA : B ⊆ A) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hg : ∀ k, R.g k ∈ B) : (restrictMaxLinear A B hA hB hBA R hg).g = R.g := rfl

@[simp] theorem restrictMaxLinear_alpha {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty)
    (hB : B.Nonempty) (hBA : B ⊆ A) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hg : ∀ k, R.g k ∈ B) : (restrictMaxLinear A B hA hB hBA R hg).α = R.α := rfl

theorem restrictMaxLinear_value {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty)
    (hB : B.Nonempty) (hBA : B ⊆ A) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hg : ∀ k, R.g k ∈ B) (k : ℕ) :
    finiteMaxLinear B hB ((restrictMaxLinear A B hA hB hBA R hg).x k) =
      finiteMaxLinear A hA (R.x k) :=
  finiteMaxLinear_restriction_value A B hA hB hBA (R.hasGradient k) (hg k)

/-- Finitely many accepted slope values yield an actual recurrent finite subset
and a tail retaining exactly those values. No global objective equality follows. -/
theorem exists_recurrent_slope_subset {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA)) :
    ∃ (J : ℕ) (B : Finset (Vec n)), B.Nonempty ∧ (B : Set (Vec n)) = recurrentValues R.g ∧
      B ⊆ A ∧ ∀ k, R.g (J+k) ∈ B := by
  classical
  have hf := R.maxLinear_gradient_range_finite A hA
  have hrec := recurrentValues_finite R.g hf
  let B := hrec.toFinset
  have hB : B.Nonempty := by
    obtain ⟨b, hb⟩ := recurrentValues_nonempty R.g hf
    exact ⟨b, by simpa only [B, Set.Finite.mem_toFinset] using hb⟩
  have hBA : B ⊆ A := by
    intro b hb
    have hbr : b ∈ recurrentValues R.g := by simpa only [B, Set.Finite.mem_toFinset] using hb
    obtain ⟨k, rfl⟩ := recurrentValues_subset_range R.g hbr
    exact R.maxLinear_gradient_mem A hA k
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (eventually_mem_recurrentValues R.g hf)
  refine ⟨J, B, hB, by simp only [B, Set.Finite.coe_toFinset], hBA, ?_⟩
  intro k
  simpa only [B, Set.Finite.mem_toFinset] using hJ (J+k) (Nat.le_add_right J k)

/-- The genuine full-BFGS tail run on exactly the recurrent finite maximum,
with the same accepted coordinates, matrices, gradients and step lengths. -/
theorem exists_recurrent_maxLinear_run {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA)) :
    ∃ (J : ℕ) (B : Finset (Vec n)) (hB : B.Nonempty)
      (Q : AdmissibleBFGSRun n (finiteMaxLinear B hB)),
      (B : Set (Vec n)) = recurrentValues R.g ∧ B ⊆ A ∧
      Q.x = (fun k => R.x (J+k)) ∧ Q.H = (fun k => R.H (J+k)) ∧
      Q.g = (fun k => R.g (J+k)) ∧ Q.α = (fun k => R.α (J+k)) ∧
      Q.c₁ = R.c₁ ∧ Q.c₂ = R.c₂ ∧
      ∀ k, finiteMaxLinear B hB (Q.x k) = finiteMaxLinear A hA (R.x (J+k)) := by
  obtain ⟨J, B, hB, hrec, hBA, hg⟩ := R.exists_recurrent_slope_subset A hA
  let Q := restrictMaxLinear A B hA hB hBA (R.shift J) hg
  refine ⟨J, B, hB, Q, hrec, hBA, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro k
  exact (R.shift J).restrictMaxLinear_value A B hA hB hBA hg k

end AdmissibleBFGSRun
end BfgsVerification
