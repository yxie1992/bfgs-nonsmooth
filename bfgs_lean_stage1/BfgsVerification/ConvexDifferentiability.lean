import BfgsVerification.ConvexGradientLimits
import Mathlib.Analysis.Calculus.Rademacher

/-! Actual coordinate gradients and simultaneous differentiable approximations
for finite convex functions. No continuity of gradients is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory Matrix

namespace BfgsVerification

/-- Every actual derivative functional has its Euclidean coordinate representation. -/
theorem gradientFunctional_coordinates {n : ℕ} (l : Vec n →L[ℝ] ℝ) :
    gradientFunctional (fun i => l (Pi.single i 1)) = l := by
  ext v
  rw [gradientFunctional_apply]
  conv_rhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  have he : Pi.single i (v i) = v i • (Pi.single i (1 : ℝ) : Vec n) := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i (v i) (1 : ℝ)
  rw [he, map_smul, smul_eq_mul, mul_comm]

/-- Coordinates of the actual Fréchet derivative; values at nondifferentiable
points are irrelevant to all subsequent derivative claims. -/
def coordinateGradient {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Vec n :=
  fun i => (fderiv ℝ F x) (Pi.single i 1)

theorem hasFDerivAt_coordinateGradient {n : ℕ} {F : Vec n → ℝ} {x : Vec n}
    (h : DifferentiableAt ℝ F x) : HasFDerivAt F (gradientFunctional (coordinateGradient F x)) x := by
  change HasFDerivAt F (gradientFunctional (fun i => (fderiv ℝ F x) (Pi.single i 1))) x
  rw [gradientFunctional_coordinates]
  exact h.hasFDerivAt

/-- Rademacher on a countable family of balls gives almost-everywhere
Fréchet differentiability of every finite convex objective. -/
theorem convex_ae_differentiable {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) :
    ∀ᵐ x ∂(volume : Measure (Vec n)), DifferentiableAt ℝ F x := by
  have hc := convex_continuous hF
  have hball (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Vec n)),
      x ∈ Metric.ball 0 (k : ℝ) → DifferentiableAt ℝ F x := by
    have hb : Bornology.IsBounded (F '' Metric.ball (0 : Vec n) ((k : ℝ) + 1)) :=
      ((isCompact_closedBall (0 : Vec n) ((k : ℝ) + 1)).image hc).isBounded.subset
        (image_mono Metric.ball_subset_closedBall)
    have hconv : ConvexOn ℝ (Metric.ball (0 : Vec n) ((k : ℝ) + 1)) F :=
      hF.subset (subset_univ _) (convex_ball _ _)
    obtain ⟨C, hC⟩ := hconv.exists_lipschitzOnWith_of_isBounded
      (show (k : ℝ) < (k : ℝ) + 1 by linarith) hb
    filter_upwards [hC.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hmem
    exact (hx hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  filter_upwards [ae_all_iff.mpr hball] with x hx
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  exact hx k (by simpa only [Metric.mem_ball, dist_zero_right] using hk)

/-- The affine dilation about a reference point is differentiable at every point. -/
theorem homothety_differentiable {n : ℕ} (star : Vec n) (a : ℝ) :
    Differentiable ℝ (AffineMap.homothety star a : Vec n → Vec n) := by
  simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using
    ((differentiable_id.sub_const star).const_smul a).add_const star

/-- Composition with a nondegenerate affine dilation reflects differentiability. -/
theorem differentiableAt_of_comp_homothety {n : ℕ} {F : Vec n → ℝ}
    (star : Vec n) {a : ℝ} (ha : a ≠ 0) (x : Vec n)
    (h : DifferentiableAt ℝ (F ∘ AffineMap.homothety star a) x) :
    DifferentiableAt ℝ F (AffineMap.homothety star a x) := by
  let A := AffineMap.homothety star a
  let B := AffineMap.homothety star a⁻¹
  have hBA : B (A x) = x := by
    dsimp only [A, B]
    rw [← AffineMap.homothety_mul_apply, inv_mul_cancel₀ ha, AffineMap.homothety_one]
    rfl
  have hAB : (F ∘ A) ∘ B = F := by
    funext w
    simp only [Function.comp_def, A, B, ← AffineMap.homothety_mul_apply,
      mul_inv_cancel₀ ha, AffineMap.homothety_one, AffineMap.id_apply]
  have h' : DifferentiableAt ℝ (F ∘ A) (B (A x)) := by rwa [hBA]
  have hc := h'.comp (A x) (homothety_differentiable star a⁻¹ (A x))
  rwa [hAB] at hc

/-- Joint differentiability follows from an intersection of two full-measure
sets. No general intersection-of-dense-sets principle is used. -/
theorem dense_homothety_differentiable_pairs {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {a : ℝ} (ha : a ≠ 0) :
    Dense {x : Vec n | DifferentiableAt ℝ F x ∧
      DifferentiableAt ℝ F (AffineMap.homothety star a x)} := by
  have hcomp : ConvexOn ℝ univ (F ∘ AffineMap.homothety star a) := by
    simpa only [preimage_univ] using hF.comp_affineMap (AffineMap.homothety star a)
  apply MeasureTheory.Measure.dense_of_ae (μ := volume)
  filter_upwards [convex_ae_differentiable hF, convex_ae_differentiable hcomp] with x hx hc
  exact ⟨hx, differentiableAt_of_comp_homothety star ha x hc⟩

end BfgsVerification
