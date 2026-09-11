import BfgsVerification.HomogeneousConsequences

/-! Actual finite maxima of linear slopes. Their accepted gradients are proved
to belong to the slope alphabet from differentiability, never assumed to do so. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

def finiteMaxLinear {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) (x : Vec n) : ℝ :=
  A.sup' hA (fun a => dot a x)

theorem slope_le_finiteMaxLinear {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    {a : Vec n} (ha : a ∈ A) (x : Vec n) : dot a x ≤ finiteMaxLinear A hA x :=
  Finset.le_sup' (fun a => dot a x) ha

theorem finiteMaxLinear_active {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) (x : Vec n) :
    ∃ a ∈ A, finiteMaxLinear A hA x = dot a x := Finset.exists_mem_eq_sup' hA _

theorem finiteMaxLinear_convex {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) :
    ConvexOn ℝ Set.univ (finiteMaxLinear A hA) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  apply Finset.sup'_le
  intro v hv
  have heq : dot v (a • x + b • z) = a * dot v x + b * dot v z := by
    change v ⬝ᵥ (a • x + b • z) = _
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    rfl
  rw [heq]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (slope_le_finiteMaxLinear A hA hv x) ha)
    (mul_le_mul_of_nonneg_left (slope_le_finiteMaxLinear A hA hv z) hb)

theorem finiteMaxLinear_homogeneous {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) :
    PositiveDegreeOne (finiteMaxLinear A hA) := by
  intro t ht x
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    rw [dot_smul_right]
    exact mul_le_mul_of_nonneg_left (slope_le_finiteMaxLinear A hA ha x) ht
  · obtain ⟨a, ha, he⟩ := finiteMaxLinear_active A hA x
    rw [he, ← dot_smul_right]
    exact slope_le_finiteMaxLinear A hA ha (t • x)

/-- An active slope supports the finite maximum globally. -/
theorem finiteMaxLinear_active_supports {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    {x a : Vec n} (ha : a ∈ A) (he : finiteMaxLinear A hA x = dot a x) :
    Supports (finiteMaxLinear A hA) x a := by
  intro z
  change a ⬝ᵥ (z - x) ≤ _
  rw [dotProduct_sub, he]
  exact sub_le_sub_right (slope_le_finiteMaxLinear A hA ha z) _

/-- Fermat's theorem identifies an active linear slope with the actual derivative. -/
theorem finiteMaxLinear_active_eq_gradient {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    {x a g : Vec n} (ha : a ∈ A) (he : finiteMaxLinear A hA x = dot a x)
    (hg : HasFDerivAt (finiteMaxLinear A hA) (gradientFunctional g) x) : a = g := by
  have hlocal : IsLocalMin (fun z => finiteMaxLinear A hA z - dot a z) x := by
    apply IsMinOn.isLocalMin (s := Set.univ) _ (by simp)
    intro z _
    change finiteMaxLinear A hA x - dot a x ≤ finiteMaxLinear A hA z - dot a z
    rw [he, sub_self]
    exact sub_nonneg.mpr (slope_le_finiteMaxLinear A hA ha z)
  have hlinear : HasFDerivAt (fun z => dot a z) (gradientFunctional a) x := by
    have hfun : (fun z => dot a z) = (gradientFunctional a : Vec n → ℝ) := by
      funext z
      exact (gradientFunctional_apply a z).symm
    rw [hfun]
    exact (gradientFunctional a).hasFDerivAt
  have hzero := hlocal.hasFDerivAt_eq_zero (hg.sub hlinear)
  funext i
  have hi := congrArg (fun f : Vec n →L[ℝ] ℝ => f (Pi.single i 1)) hzero
  simp only [ContinuousLinearMap.sub_apply, gradientFunctional_apply, ContinuousLinearMap.zero_apply]
    at hi
  change dotProduct g (Pi.single i 1) - dotProduct a (Pi.single i 1) = 0 at hi
  rw [dotProduct_single_one, dotProduct_single_one] at hi
  linarith

/-- At every differentiable point, the derivative is one of the supplied slopes. -/
theorem finiteMaxLinear_gradient_mem {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    {x g : Vec n} (hg : HasFDerivAt (finiteMaxLinear A hA) (gradientFunctional g) x) : g ∈ A := by
  obtain ⟨a, ha, he⟩ := finiteMaxLinear_active A hA x
  rwa [finiteMaxLinear_active_eq_gradient A hA ha he hg] at ha

end Homogeneous

namespace AdmissibleBFGSRun

variable {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA))

theorem maxLinear_gradient_mem (k : ℕ) : R.g k ∈ A :=
  Homogeneous.finiteMaxLinear_gradient_mem A hA (R.hasGradient k)

theorem maxLinear_gradient_range_finite : (Set.range R.g).Finite :=
  A.finite_toSet.subset (by rintro x ⟨k, rfl⟩; exact R.maxLinear_gradient_mem A hA k)

theorem maxLinear_value_dichotomy :
    Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∨
      Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop atBot :=
  R.homogeneous_value_dichotomy (Homogeneous.finiteMaxLinear_homogeneous A hA)

end AdmissibleBFGSRun
end BfgsVerification
