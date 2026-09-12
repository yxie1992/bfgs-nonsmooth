import BfgsVerification.OptimizerInterceptExamples
import BfgsVerification.AffineCriticalGeometry
import BfgsVerification.AffineBarycentricCoordinates
import BfgsVerification.DLiteralIdentities
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Article-only elementary deductions. The sealed research sources are unchanged. -/
noncomputable section
open scoped BigOperators Topology
open Set Matrix
open BfgsVerification

namespace ArticleGeometry

theorem affine_balance_iff {n : ℕ} {ι : Type*}
    (a : ι → EuclideanSpace ℝ (Fin n)) (i : ι) :
    (∃ v, ∀ j, inner (a j) v = (-1 : ℝ)) ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (range a) :=
  AffineCriticalGeometry.equal_rate_exists_iff a i

theorem affine_negative_common_rate_iff {n : ℕ} {ι : Type*}
    (a : ι → EuclideanSpace ℝ (Fin n)) (i : ι) :
    (∃ v κ, κ < (0 : ℝ) ∧ ∀ j, inner (a j) v = κ) ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (range a) := by
  constructor
  · rintro ⟨v,κ,hκ,h⟩ hz
    have he := AffineCriticalGeometry.affine_pairing_of_constant a v κ h 0 hz
    simp only [inner_zero_left] at he
    linarith
  · intro h
    obtain ⟨v,hv⟩ := (affine_balance_iff a i).mpr h
    exact ⟨v,-1,by norm_num,hv⟩

theorem mixed_ridge_inward {x g : Vec 2}
    (hg : HasFDerivAt UnexcitedMetric.objective (gradientFunctional g) x)
    {τ : ℝ} (hτ : τ ≤ 1) :
    UnexcitedMetric.objective ((1-τ) • x)-UnexcitedMetric.objective x+
      τ*dot g x = τ^2*(x 0)^2 := by
  rw [InterceptExamples.quadratic_absolute_radial_pairing hg]
  simp only [UnexcitedMetric.objective, Pi.smul_apply, smul_eq_mul,
    abs_mul, abs_of_nonneg (sub_nonneg.mpr hτ)]
  ring

theorem mixed_ridge_gradient {u v : ℝ} (hv : v ≠ 0) :
    HasFDerivAt UnexcitedMetric.objective
      (gradientFunctional ![2*u, Real.sign v]) ![u,v] := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt
    (x := (![u,v] : Vec 2))
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt
    (x := (![u,v] : Vec 2))
  have hsq := ((hasDerivAt_id u).pow 2).comp_hasFDerivAt (![u,v] : Vec 2) h0
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · have hh := hsq.add (h1.abs_of_neg (by simpa using hneg))
    convert hh using 1
    ext z
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two, Real.sign_of_neg hneg]
  · have hh := hsq.add (h1.abs_of_pos (by simpa using hpos))
    convert hh using 1
    ext z
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two, Real.sign_of_pos hpos]

theorem mixed_ridge_equal_descent (u : ℝ) (hu : u ≠ 0) :
    dot (![2*u,1] : Vec 2) ![-u,0] = -2*u^2 ∧
    dot (![2*u,-1] : Vec 2) ![-u,0] = -2*u^2 ∧ -2*u^2 < 0 := by
  constructor
  · simp [dot, Fin.sum_univ_two]; ring
  constructor
  · simp [dot, Fin.sum_univ_two]; ring
  nlinarith [sq_pos_of_ne_zero hu]

theorem seed_slope_bounds :
    (318/1000 : ℝ) < SeedOrbit.seedC ∧ SeedOrbit.seedC < 319/1000 ∧
    (-1026/1000 : ℝ) < SeedOrbit.seedD ∧ SeedOrbit.seedD < -1025/1000 :=
  AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1

theorem seed_affine_determinant_pos :
    0 < (SeedOrbit.seedC-1)/8-2*SeedOrbit.seedD := by
  obtain ⟨hc,_,_,hd⟩ := seed_slope_bounds
  linarith

theorem seed_affine_independent :
    AffineIndependent ℝ (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs i
  rw [AffineBarycentric.weightedVSub_eq_sum_of_sum_zero _ _ hw] at hs
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  norm_num [Fin.sum_univ_succ] at hw
  norm_num [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g1, SeedCycle.g2,
    Fin.sum_univ_succ] at h0 h1
  have hdet := seed_affine_determinant_pos
  have hw2 : w 2 = 0 := by
    have hz : w 2 * ((SeedOrbit.seedC-1)/8-2*SeedOrbit.seedD)=0 := by
      linear_combination (1/8 : ℝ)*h0-(1/8 : ℝ)*hw-2*h1
    exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hdet)
  have hw1 : w 1 = 0 := by rw [hw2, zero_mul] at h1; linarith
  have hw0 : w 0 = 0 := by rw [hw1,hw2] at hw; linarith
  fin_cases i <;> assumption

theorem seed_affine_span_top :
    affineSpan ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) = ⊤ := by
  apply seed_affine_independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [Vec, Module.finrank_pi]

theorem seed_equal_pairings_force_zero {v : Vec 2} {κ : ℝ}
    (h : ∀ j, dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) v = κ) :
    v = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g1, SeedCycle.g2,
    dot, Fin.sum_univ_two] at h0 h1 h2
  change SeedOrbit.seedC * v 0 + SeedOrbit.seedD * v 1 = κ at h2
  have hz : v 0 * ((SeedOrbit.seedC-1)/8-2*SeedOrbit.seedD)=0 := by
    linear_combination (1/8 : ℝ)*(h2-h0)+SeedOrbit.seedD*(h1-h0)
  have hv0 : v 0 = 0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt seed_affine_determinant_pos)
  have hv1 : v 1 = 0 := by rw [hv0] at h0 h1; linarith
  ext i
  fin_cases i <;> assumption

theorem seed_strict_common_descent (j : Fin 3) :
    dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) ![-1,16] < 0 := by
  obtain ⟨hc,_,_,hd⟩ := seed_slope_bounds
  fin_cases j <;>
    norm_num [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g1, SeedCycle.g2,
      dot, Fin.sum_univ_two]
  linarith

theorem seed_convex_hull_excludes_zero :
    (0 : Vec 2) ∉ convexHull ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) :=
  DLiteralIdentities.zero_not_mem_gradient_hull

end ArticleGeometry

#print axioms ArticleGeometry.affine_balance_iff
#print axioms ArticleGeometry.affine_negative_common_rate_iff
#print axioms ArticleGeometry.mixed_ridge_inward
#print axioms ArticleGeometry.mixed_ridge_gradient
#print axioms ArticleGeometry.mixed_ridge_equal_descent
#print axioms ArticleGeometry.seed_slope_bounds
#print axioms ArticleGeometry.seed_affine_determinant_pos
#print axioms ArticleGeometry.seed_affine_independent
#print axioms ArticleGeometry.seed_affine_span_top
#print axioms ArticleGeometry.seed_equal_pairings_force_zero
#print axioms ArticleGeometry.seed_strict_common_descent
#print axioms ArticleGeometry.seed_convex_hull_excludes_zero
