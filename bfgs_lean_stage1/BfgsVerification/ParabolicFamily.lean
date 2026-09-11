import BfgsVerification.ConvexGradientLimits
import BfgsVerification.Localization
import BfgsVerification.TransportedCertificateVariants

/-! Module Q: the actual arbitrary finite parabolic maximum. Input branches
may repeat, have zero normal slope, or be active only at ties. -/

noncomputable section
open scoped BigOperators Topology
open Set Matrix

namespace BfgsVerification
namespace Parabolic

structure Family (m : ℕ) where
  a : Fin m → ℝ
  b : Fin m → ℝ
  a_pos : ∀ i, 0 < a i
  negative_slope : ∃ i, b i < 0
  positive_slope : ∃ i, 0 < b i

namespace Family
variable {m : ℕ} (P : Family m)

theorem indices_nonempty (P : Family m) : (Finset.univ : Finset (Fin m)).Nonempty := by
  obtain ⟨i, _⟩ := P.negative_slope
  exact ⟨i, Finset.mem_univ i⟩

def branch (i : Fin m) (x : Vec 2) : ℝ := P.a i * (x 0)^2 + P.b i * x 1
def objective (x : Vec 2) : ℝ := Finset.univ.sup' P.indices_nonempty (fun i => P.branch i x)
def branchGradient (i : Fin m) (x : Vec 2) : Vec 2 := ![2 * P.a i * x 0, P.b i]
def radialDirection (x : Vec 2) : Vec 2 := ![x 0, 2 * x 1]
def Active (i : Fin m) (x : Vec 2) : Prop := P.objective x = P.branch i x

theorem branch_le (i : Fin m) (x : Vec 2) : P.branch i x ≤ P.objective x :=
  Finset.le_sup' (fun j => P.branch j x) (Finset.mem_univ i)

theorem exists_active (x : Vec 2) : ∃ i, P.Active i x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' P.indices_nonempty (fun i => P.branch i x)
  exact ⟨i, hi⟩

theorem branch_convex (i : Fin m) : ConvexOn ℝ univ (P.branch i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  change P.a i * (a * x 0 + b * z 0)^2 + P.b i * (a * x 1 + b * z 1) ≤
    a * (P.a i * (x 0)^2 + P.b i * x 1) + b * (P.a i * (z 0)^2 + P.b i * z 1)
  have he : a * (P.a i * (x 0)^2 + P.b i * x 1) + b * (P.a i * (z 0)^2 + P.b i * z 1) -
      (P.a i * (a * x 0 + b * z 0)^2 + P.b i * (a * x 1 + b * z 1)) =
      P.a i * a * b * (x 0 - z 0)^2 := by
    rw [show b = 1-a by linarith]
    ring
  have hp : 0 ≤ P.a i * a * b * (x 0 - z 0)^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (P.a_pos i).le ha) hb) (sq_nonneg _)
  linarith

theorem objective_convex : ConvexOn ℝ univ P.objective := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  apply Finset.sup'_le
  intro i _
  exact ((P.branch_convex i).2 hx hz ha hb hab).trans
    (add_le_add (mul_le_mul_of_nonneg_left (P.branch_le i x) ha)
      (mul_le_mul_of_nonneg_left (P.branch_le i z) hb))

theorem objective_continuous : Continuous P.objective := convex_continuous P.objective_convex

theorem branch_hasGradient (i : Fin m) (x : Vec 2) :
    HasFDerivAt (P.branch i) (gradientFunctional (P.branchGradient i x)) x := by
  have h0 := (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hd := ((h0.mul h0).const_mul (P.a i)).add (h1.const_mul (P.b i))
  convert hd using 1
  · funext z
    simp only [branch, ContinuousLinearMap.proj_apply, pow_two]
  · ext v
    simp [gradientFunctional_apply, branchGradient, dot, Fin.sum_univ_two]
    <;> ring

theorem branch_supports (i : Fin m) (x z : Vec 2) :
    dot (P.branchGradient i x) (z - x) ≤ P.branch i z - P.branch i x := by
  have hp := mul_nonneg (P.a_pos i).le (sq_nonneg (z 0 - x 0))
  simp [dot, Fin.sum_univ_two, branchGradient, branch] at *
  nlinarith

theorem active_supports {i : Fin m} {x : Vec 2} (hi : P.Active i x) :
    ∀ z, dot (P.branchGradient i x) (z-x) ≤ P.objective z - P.objective x := by
  intro z
  exact (P.branch_supports i x z).trans (by rw [hi]; exact sub_le_sub_right (P.branch_le i z) _)

/-- Every active branch has the actual gradient at a differentiable endpoint,
including a differentiable tie. No unique-activity premise is introduced. -/
theorem active_eq_gradient {i : Fin m} {x g : Vec 2} (hi : P.Active i x)
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) : P.branchGradient i x = g :=
  supporting_vector_eq_gradient (P.active_supports hi) hg

theorem gradient_from_active {x g : Vec 2}
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    ∃ i, P.Active i x ∧ g = P.branchGradient i x := by
  obtain ⟨i, hi⟩ := P.exists_active x
  exact ⟨i, hi, (P.active_eq_gradient hi hg).symm⟩

theorem objective_zero : P.objective 0 = 0 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    simp [branch]
  · obtain ⟨i, _⟩ := P.negative_slope
    simpa [branch] using P.branch_le i 0

/-- Any common positive lower bound on the quadratic coefficients bounds F.
The proof selects an extreme-sign branch according to v and does not divide
by any intermediate normal slope. -/
theorem quadratic_lower_bound {a₀ : ℝ} (ha : ∀ i, a₀ ≤ P.a i) (x : Vec 2) :
    a₀ * (x 0)^2 ≤ P.objective x := by
  by_cases hv : 0 ≤ x 1
  · obtain ⟨i, hi⟩ := P.positive_slope
    have h1 := mul_nonneg hi.le hv
    have h2 := mul_le_mul_of_nonneg_right (ha i) (sq_nonneg (x 0))
    have h3 := P.branch_le i x
    dsimp [branch] at h3
    linarith
  · obtain ⟨i, hi⟩ := P.negative_slope
    have h1 := mul_nonneg_of_nonpos_of_nonpos hi.le (le_of_not_ge hv)
    have h2 := mul_le_mul_of_nonneg_right (ha i) (sq_nonneg (x 0))
    have h3 := P.branch_le i x
    dsimp [branch] at h3
    linarith

def minQuadratic : ℝ := Finset.univ.inf' P.indices_nonempty P.a

theorem minQuadratic_pos : 0 < P.minQuadratic := by
  exact (Finset.lt_inf'_iff P.indices_nonempty).mpr (fun i _ => P.a_pos i)

theorem minQuadratic_le (i : Fin m) : P.minQuadratic ≤ P.a i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem objective_nonneg (x : Vec 2) : 0 ≤ P.objective x :=
  (mul_nonneg P.minQuadratic_pos.le (sq_nonneg (x 0))).trans
    (P.quadratic_lower_bound P.minQuadratic_le x)

theorem unique_zero (x : Vec 2) (hx : P.objective x = 0) : x = 0 := by
  have hq := P.quadratic_lower_bound P.minQuadratic_le x
  rw [hx] at hq
  have hu : x 0 = 0 := by
    have hs : (x 0)^2 ≤ 0 := by nlinarith [P.minQuadratic_pos]
    nlinarith [sq_nonneg (x 0)]
  obtain ⟨i, hi⟩ := P.positive_slope
  obtain ⟨j, hj⟩ := P.negative_slope
  have hv₁ := P.branch_le i x
  have hv₂ := P.branch_le j x
  simp only [branch, hu, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, hx] at hv₁ hv₂
  have hv : x 1 = 0 := by
    have hle : x 1 ≤ 0 := by nlinarith
    have hge : 0 ≤ x 1 := by nlinarith
    exact le_antisymm hle hge
  funext k
  fin_cases k <;> assumption

theorem unique_minimum : (∀ x, P.objective 0 ≤ P.objective x) ∧
    (∀ x, P.objective x = P.objective 0 → x = 0) := by
  rw [P.objective_zero]
  exact ⟨P.objective_nonneg, P.unique_zero⟩

theorem sublevel_compact (B : ℝ) : IsCompact {x | P.objective x ≤ B} :=
  Localization.sublevel_compact P.objective_convex 0 P.unique_minimum.1 P.unique_minimum.2 B

end Family
end Parabolic
end BfgsVerification
