import BfgsArticle.AdmissibleRunExistence
import BfgsVerification.PlanarMaxHessianBasin

/-!
# A globally convergent two-quadratic family

For `a,b,c > 0`, the objective is
`max (a*u^2 + b*v^2 + v) (c*u^2 + b*v^2 - v)`.
All objective hypotheses of the article's planar convergence and nondegenerate
finite-maximum theorems are verified for this same family. The switching set is
the parabola `v = (c-a)*u^2/2` (a line when `a=c`). Differentiability always means
Fréchet differentiability on the full ambient plane, not on a search ray.

Euclidean strong convexity uses `sqNorm`, not the sup norm on `Vec 2`.

Principal results:
* `paper_planar_hypotheses`, `planar_hypotheses`, `finite_max_hypotheses` verify
  the complete simultaneous hypotheses, rather than assume them.
* `joint_witness` combines these hypotheses and universal convergence with an
  actual convergent run for every differentiable start, SPD matrix and valid
  fixed line-search pair.
* `Radial.radial_obstruction_in_every_neighborhood` proves the fixed-band radial
  obstruction for `(a,b,c)=(1,1,2)`, using eligible endpoint pairs.
* `concrete_joint_witness` specializes to `(0,1/4)`, identity initialization and
  constants `(1/4,1/2)`, with initial value `5/16`.
-/

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix

namespace BfgsVerification.TwoQuadraticExample

open FixedNormal ConvexSubdifferential AffineCriticalObjective HomogeneousPlanar

variable (a b c : ℝ)

/-- The two specified polynomial branches, with their original indices. -/
def branch (i : Fin 2) (x : Vec 2) : ℝ :=
  ![a * x 0 ^ 2 + b * x 1 ^ 2 + x 1,
    c * x 0 ^ 2 + b * x 1 ^ 2 - x 1] i

/-- The finite real-valued objective. -/
def objective (x : Vec 2) : ℝ := max (branch a b c 0 x) (branch a b c 1 x)

def linearPart (i : Fin 2) : Vec 2 := ![![0, 1], ![0, -1]] i

def hessianDiagonal (i : Fin 2) : Vec 2 := ![![2 * a, 2 * b], ![2 * c, 2 * b]] i

def hessian (i : Fin 2) : Mat 2 := diagonal (hessianDiagonal a b c i)

def gradient (i : Fin 2) (x : Vec 2) : Vec 2 :=
  linearPart i + (hessian a b c i).mulVec x

/-- The common Euclidean strong-convexity modulus `2 min(a,b,c)`. -/
def modulus : ℝ := 2 * min a (min b c)

theorem modulus_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < modulus a b c := by
  exact mul_pos (by norm_num) (lt_min ha (lt_min hb hc))

theorem branch_quadratic (i : Fin 2) (x : Vec 2) :
    branch a b c i x = metricEnergy (hessian a b c i) x / 2 + dot (linearPart i) x := by
  fin_cases i <;>
    simp [branch, hessian, hessianDiagonal, linearPart, metricEnergy, dot,
      Fin.sum_univ_two, Matrix.mulVec_diagonal] <;> ring

/-- Each branch is polynomial, in particular `C²` and `C∞` on the whole plane. -/
theorem branch_contDiff (i : Fin 2) {N : WithTop ℕ∞} :
    ContDiff ℝ N (branch a b c i) := by
  fin_cases i
  · change ContDiff ℝ N (fun x : Vec 2 => a * x 0 ^ 2 + b * x 1 ^ 2 + x 1)
    fun_prop
  · change ContDiff ℝ N (fun x : Vec 2 => c * x 0 ^ 2 + b * x 1 ^ 2 - x 1)
    fun_prop

theorem branch_hasGradient (i : Fin 2) (x : Vec 2) :
    HasFDerivAt (branch a b c i) (gradientFunctional (gradient a b c i x)) x := by
  have hl : HasFDerivAt (fun z => dot (linearPart i) z)
      (gradientFunctional (linearPart i)) x := by
    simpa only [gradientFunctional_apply] using
      (gradientFunctional (linearPart i)).hasFDerivAt (x := x)
  have hq := QuadraticGauge.quadratic_hasGradient (hessian a b c i)
    (Matrix.isSymm_diagonal _) x
  convert hq.add hl using 1
  · funext z
    exact branch_quadratic a b c i z
  · ext z
    simp only [gradientFunctional_apply, ContinuousLinearMap.add_apply, gradient, dot,
      Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring

theorem gradient_coordinates (x : Vec 2) :
    gradient a b c 0 x = ![2 * a * x 0, 2 * b * x 1 + 1] ∧
      gradient a b c 1 x = ![2 * c * x 0, 2 * b * x 1 - 1] := by
  constructor <;> ext j <;> fin_cases j <;>
    simp [gradient, hessian, hessianDiagonal, linearPart, Matrix.mulVec_diagonal] <;> ring

theorem coordinateGradient_eq (i : Fin 2) (x : Vec 2) :
    coordinateGradient (branch a b c i) x = gradient a b c i x :=
  AffineProjection.gradientFunctional_injective
    ((hasFDerivAt_coordinateGradient (branch_hasGradient a b c i x).differentiableAt).unique
      (branch_hasGradient a b c i x))

def hessianFunctional (i : Fin 2) : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ :=
  ∑ j : Fin 2, (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).smulRight
    (hessianDiagonal a b c i j • ContinuousLinearMap.proj j)

theorem hessianFunctional_apply (i : Fin 2) (x : Vec 2) :
    hessianFunctional a b c i x = gradientFunctional ((hessian a b c i).mulVec x) := by
  ext z
  simp only [hessianFunctional, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    gradientFunctional_apply, hessian, Matrix.mulVec_diagonal, dot]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem branch_second_hasFDerivAt (i : Fin 2) (x : Vec 2) :
    HasFDerivAt (fderiv ℝ (branch a b c i)) (hessianFunctional a b c i) x := by
  have he : fderiv ℝ (branch a b c i) =
      fun z => hessianFunctional a b c i z + gradientFunctional (linearPart i) := by
    funext z
    rw [(branch_hasGradient a b c i z).fderiv]
    ext v
    simp only [hessianFunctional_apply, gradientFunctional_apply, ContinuousLinearMap.add_apply,
      gradient, dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [he]
  exact (hessianFunctional a b c i).hasFDerivAt.add_const _

/-- These are the matrices of the actual second Fréchet derivatives. -/
theorem branch_actual_hessian (i : Fin 2) (x : Vec 2) :
    RadialHessian.matrix (branch a b c i) x = hessian a b c i := by
  rw [RadialHessian.matrix, (branch_second_hasFDerivAt a b c i x).fderiv]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [RadialHessian.bilinearMatrix, hessianFunctional_apply, gradientFunctional_apply,
      hessian, Matrix.mulVec_diagonal, dot, Fin.sum_univ_two]

theorem hessian_lower_bound (i : Fin 2) :
    (hessian a b c i - modulus a b c • (1 : Mat 2)).PosSemidef := by
  have he : hessian a b c i - modulus a b c • (1 : Mat 2) =
      diagonal (fun j => hessianDiagonal a b c i j - modulus a b c) := by
    ext j k
    simp [hessian, Matrix.diagonal, Matrix.one_apply]
    split_ifs <;> ring
  rw [he]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [hessianDiagonal, modulus]

theorem branch_actual_hessian_lower_bound (i : Fin 2) (x : Vec 2) :
    (RadialHessian.matrix (branch a b c i) x - modulus a b c • (1 : Mat 2)).PosSemidef := by
  rw [branch_actual_hessian]
  exact hessian_lower_bound a b c i

theorem branch_convex (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (i : Fin 2) :
    ConvexOn ℝ univ (branch a b c i) := by
  have hQ : (hessian a b c i).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [hessianDiagonal] <;> positivity
  apply ((QuadraticGauge.quadratic_convex (hessian a b c i) hQ).add
    ((gradientFunctional (linearPart i)).toLinearMap.convexOn convex_univ)).congr
  intro x _
  simp only [Pi.add_apply, ContinuousLinearMap.coe_coe, gradientFunctional_apply]
  exact (branch_quadratic a b c i x).symm

theorem branch_strongConvex (i : Fin 2) :
    EuclideanStrongConvexOn univ (modulus a b c) (branch a b c i) := by
  apply ((QuadraticGauge.quadratic_convex
    (hessian a b c i - modulus a b c • (1 : Mat 2)) (hessian_lower_bound a b c i)).add
      ((gradientFunctional (linearPart i)).toLinearMap.convexOn convex_univ)).congr
  intro x _
  simp only [Pi.add_apply, ContinuousLinearMap.coe_coe, gradientFunctional_apply]
  rw [branch_quadratic]
  simp [metricEnergy, dot, sqNorm, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, mul_sub, pow_two, Finset.mul_sum]
  ring

theorem branch_le_objective (i : Fin 2) (x : Vec 2) :
    branch a b c i x ≤ objective a b c x := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem objective_isGreatest (x : Vec 2) :
    IsGreatest (range (fun i => branch a b c i x)) (objective a b c x) := by
  refine ⟨?_, ?_⟩
  · rcases le_total (branch a b c 1 x) (branch a b c 0 x) with h | h
    · exact ⟨0, (max_eq_left h).symm⟩
    · exact ⟨1, (max_eq_right h).symm⟩
  · rintro _ ⟨i, rfl⟩
    exact branch_le_objective a b c i x

theorem localFiniteMax (x : Vec 2) :
    LocalFiniteMax (objective a b c) (branch a b c) x :=
  Eventually.of_forall (objective_isGreatest a b c)

theorem objective_convex (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ConvexOn ℝ univ (objective a b c) :=
  (branch_convex a b c ha hb hc 0).sup (branch_convex a b c ha hb hc 1)

theorem objective_strongConvex :
    EuclideanStrongConvexOn univ (modulus a b c) (objective a b c) := by
  apply ((branch_strongConvex a b c 0).sup (branch_strongConvex a b c 1)).congr
  intro x _
  simp only [Pi.sup_apply, objective, max_sub_sub_right]

/-- Averaging the branches gives a positive quadratic lower bound. -/
theorem objective_lower (x : Vec 2) :
    (a + c) / 2 * x 0 ^ 2 + b * x 1 ^ 2 ≤ objective a b c x := by
  have h0 := branch_le_objective a b c 0 x
  have h1 := branch_le_objective a b c 1 x
  simp only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  linarith

theorem objective_zero : objective a b c 0 = 0 := by simp [objective, branch]

theorem objective_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x : Vec 2) :
    0 ≤ objective a b c x := by
  exact (by positivity : 0 ≤ (a + c) / 2 * x 0 ^ 2 + b * x 1 ^ 2).trans
    (objective_lower a b c x)

theorem objective_unique_zero (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : Vec 2) (hx : objective a b c x = 0) : x = 0 := by
  have h := objective_lower a b c x
  rw [hx] at h
  have hu : x 0 ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0), mul_nonneg hb.le (sq_nonneg (x 1))]
  have hv : x 1 ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 1), mul_nonneg (by positivity : 0 ≤ (a + c) / 2) (sq_nonneg (x 0))]
  ext i
  fin_cases i
  · simpa using hu
  · simpa using hv

theorem objective_minimum (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x : Vec 2) :
    objective a b c 0 ≤ objective a b c x := by
  rw [objective_zero]
  exact objective_nonneg a b c ha hb hc x

theorem objective_isLeast (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    IsLeast (range (objective a b c)) 0 :=
  ⟨⟨0, objective_zero a b c⟩, by rintro _ ⟨x, rfl⟩; exact objective_nonneg a b c ha hb hc x⟩

theorem sublevel_compact (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (B : ℝ) :
    IsCompact {x | objective a b c x ≤ B} :=
  Localization.sublevel_compact (objective_convex a b c ha.le hb.le hc.le) 0
    (objective_minimum a b c ha.le hb.le hc.le)
    (fun x hx => objective_unique_zero a b c ha hb hc x (by rwa [objective_zero] at hx)) B

/-! ## Full-space differentiability and the affine-critical set -/

/-- Equality of the two branch values is precisely the stated parabola. -/
theorem tie_equation (x : Vec 2) :
    branch a b c 0 x = branch a b c 1 x ↔ x 1 = (c - a) * x 0 ^ 2 / 2 := by
  simp only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor <;> intro h <;> nlinarith

theorem winner_zero_eventuallyEq {x : Vec 2}
    (h : branch a b c 1 x < branch a b c 0 x) :
    objective a b c =ᶠ[𝓝 x] branch a b c 0 := by
  have hc (i : Fin 2) := (branch_contDiff a b c i (N := 0)).continuous.continuousAt (x := x)
  filter_upwards [(hc 1).eventually_lt (hc 0) h] with z hz
  exact max_eq_left hz.le

theorem winner_one_eventuallyEq {x : Vec 2}
    (h : branch a b c 0 x < branch a b c 1 x) :
    objective a b c =ᶠ[𝓝 x] branch a b c 1 := by
  have hc (i : Fin 2) := (branch_contDiff a b c i (N := 0)).continuous.continuousAt (x := x)
  filter_upwards [(hc 0).eventually_lt (hc 1) h] with z hz
  exact max_eq_right hz.le

theorem winner_zero_hasGradient {x : Vec 2}
    (h : branch a b c 1 x < branch a b c 0 x) :
    HasFDerivAt (objective a b c) (gradientFunctional (gradient a b c 0 x)) x :=
  (branch_hasGradient a b c 0 x).congr_of_eventuallyEq (winner_zero_eventuallyEq a b c h)

theorem winner_one_hasGradient {x : Vec 2}
    (h : branch a b c 0 x < branch a b c 1 x) :
    HasFDerivAt (objective a b c) (gradientFunctional (gradient a b c 1 x)) x :=
  (branch_hasGradient a b c 1 x).congr_of_eventuallyEq (winner_one_eventuallyEq a b c h)

theorem gradient_eq_of_active {x g : Vec 2}
    (hg : HasFDerivAt (objective a b c) (gradientFunctional g) x) (i : Fin 2)
    (hi : branch a b c i x = objective a b c x) : g = gradient a b c i x := by
  have hmin : IsLocalMin (fun z => objective a b c z - branch a b c i z) x := by
    refine Eventually.of_forall fun z => ?_
    change objective a b c x - branch a b c i x ≤ objective a b c z - branch a b c i z
    rw [hi, sub_self]
    exact sub_nonneg.mpr (branch_le_objective a b c i z)
  exact AffineProjection.gradientFunctional_injective
    (sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hg.sub (branch_hasGradient a b c i x))))

/-- On a tie, two different full-space gradients would be forced by differentiability. -/
theorem not_differentiableAt_of_tie {x : Vec 2}
    (ht : branch a b c 0 x = branch a b c 1 x) :
    ¬ DifferentiableAt ℝ (objective a b c) x := by
  intro hd
  have h0 : branch a b c 0 x = objective a b c x := by simp [objective, ht]
  have h1 : branch a b c 1 x = objective a b c x := ht.symm.trans h0
  have he := (gradient_eq_of_active a b c (hasFDerivAt_coordinateGradient hd) 0 h0).symm.trans
    (gradient_eq_of_active a b c (hasFDerivAt_coordinateGradient hd) 1 h1)
  rw [(gradient_coordinates a b c x).1, (gradient_coordinates a b c x).2] at he
  have hv := congrFun he 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at hv
  linarith

/-- Exact differentiability locus in the ambient plane; valid even without positivity. -/
theorem differentiableAt_iff (x : Vec 2) :
    DifferentiableAt ℝ (objective a b c) x ↔ x 1 ≠ (c - a) * x 0 ^ 2 / 2 := by
  rw [ne_eq, ← tie_equation a b c x]
  constructor
  · exact fun hd ht => not_differentiableAt_of_tie a b c ht hd
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact (winner_one_hasGradient a b c h).differentiableAt
    · exact (winner_zero_hasGradient a b c h).differentiableAt

theorem contDiffAt_of_not_tie {x : Vec 2}
    (h : x 1 ≠ (c - a) * x 0 ^ 2 / 2) {N : WithTop ℕ∞} :
    ContDiffAt ℝ N (objective a b c) x := by
  have ht : branch a b c 0 x ≠ branch a b c 1 x := by
    rwa [ne_eq, tie_equation a b c x]
  rcases lt_or_gt_of_ne ht with ht | ht
  · exact (branch_contDiff a b c 1).contDiffAt.congr_of_eventuallyEq
      (winner_one_eventuallyEq a b c ht)
  · exact (branch_contDiff a b c 0).contDiffAt.congr_of_eventuallyEq
      (winner_zero_eventuallyEq a b c ht)

/-- The two indexed gradients are affinely independent everywhere: their second
coordinates differ by two. This preserves the original branch indices. -/
theorem gradient_affineIndependent (x : Vec 2) :
    AffineIndependent ℝ (fun i => gradient a b c i x) := by
  have he : (fun i => gradient a b c i x) =
      ![![2 * a * x 0, 2 * b * x 1 + 1], ![2 * c * x 0, 2 * b * x 1 - 1]] := by
    funext i
    fin_cases i
    · exact (gradient_coordinates a b c x).1
    · exact (gradient_coordinates a b c x).2
  rw [he]
  apply affineIndependent_of_ne
  intro h
  have hv := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at hv
  linarith

/-- The exact determinant on the switching parabola. -/
theorem tie_determinant {x : Vec 2} (ht : branch a b c 0 x = branch a b c 1 x) :
    pairDet (gradient a b c 0 x) (gradient a b c 1 x) =
      -2 * x 0 * (a + c + b * (c - a) ^ 2 * x 0 ^ 2) := by
  rw [(gradient_coordinates a b c x).1, (gradient_coordinates a b c x).2]
  simp only [pairDet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [(tie_equation a b c x).mp ht]
  ring

theorem tie_determinant_ne_zero (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x : Vec 2} (ht : branch a b c 0 x = branch a b c 1 x) (hx : x ≠ 0) :
    pairDet (gradient a b c 0 x) (gradient a b c 1 x) ≠ 0 := by
  have hu : x 0 ≠ 0 := by
    intro hu
    have hv := (tie_equation a b c x).mp ht
    simp only [hu, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] at hv
    apply hx
    ext i
    fin_cases i
    · exact hu
    · exact hv
  rw [tie_determinant a b c ht]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hu) (by positivity)

private theorem linearIndependent_of_pairDet_ne_zero {p q : Vec 2}
    (hd : pairDet p q ≠ 0) : LinearIndependent ℝ ![p, q] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  have hs : s * pairDet p q = 0 := by
    dsimp only [pairDet]
    linear_combination q 1 * h0 - q 0 * h1
  have ht : t * pairDet p q = 0 := by
    dsimp only [pairDet]
    linear_combination p 0 * h1 - p 1 * h0
  exact ⟨(mul_eq_zero.mp hs).resolve_right hd, (mul_eq_zero.mp ht).resolve_right hd⟩

theorem tie_gradients_linearIndependent (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x : Vec 2} (ht : branch a b c 0 x = branch a b c 1 x) (hx : x ≠ 0) :
    LinearIndependent ℝ ![gradient a b c 0 x, gradient a b c 1 x] :=
  linearIndependent_of_pairDet_ne_zero (tie_determinant_ne_zero a b c ha hb hc ht hx)

theorem subdifferential_formula (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x : Vec 2) :
    subdifferential (objective a b c) x = convexHull ℝ
      ((fun i => gradient a b c i x) '' (activeIndices (objective a b c) (branch a b c) x : Set (Fin 2))) :=
  subdifferential_eq_active_convexHull (objective_convex a b c ha hb hc)
    (localFiniteMax a b c x) (fun i => branch_hasGradient a b c i x)

/-- There are no nonoptimal affine-critical points, anywhere in the plane. -/
theorem affineCritical_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x : Vec 2) :
    IsAffineCritical (objective a b c) x ↔ x = 0 := by
  constructor
  · intro hcrit
    by_cases ht : branch a b c 0 x = branch a b c 1 x
    · by_contra hx
      have hspan := (isAffineCritical_iff_coordinate_affineSpan (objective a b c) x).mp hcrit
      rw [subdifferential_formula a b c ha.le hb.le hc.le x, affineSpan_convexHull] at hspan
      obtain ⟨w, hw, _⟩ := AffineBarycentric.affine_zero_subset_coefficients
        (fun i => gradient a b c i x) (activeIndices (objective a b c) (branch a b c) x) hspan
      obtain ⟨hs, hz⟩ := (AffineBarycentric.augmented_equation_iff _ w).mp hw
      rw [Fin.sum_univ_two] at hs hz
      have hw0 := (LinearIndependent.pair_iff.mp
        (tie_gradients_linearIndependent a b c ha hb hc ht hx)) (w 0) (w 1) hz
      linarith [hw0.1, hw0.2]
    · have hd : DifferentiableAt ℝ (objective a b c) x := by
        rw [differentiableAt_iff, ne_eq, ← tie_equation a b c x]
        exact ht
      have hmin := zero_mem_iff_global_minimum.mp
        (affineCorrectAt_of_hasFDerivAt (objective_convex a b c ha.le hb.le hc.le)
          (hasFDerivAt_coordinateGradient hd) hcrit)
      apply objective_unique_zero a b c ha hb hc x
      exact le_antisymm (by simpa only [objective_zero] using hmin 0)
        (objective_nonneg a b c ha.le hb.le hc.le x)
  · rintro rfl
    rw [isAffineCritical_iff_coordinate_affineSpan]
    exact subset_affineSpan ℝ _ (zero_mem_iff_global_minimum.mpr
      (objective_minimum a b c ha.le hb.le hc.le))

theorem affineCritical_set (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    {x | IsAffineCritical (objective a b c) x} = {0} := by
  ext x
  exact affineCritical_iff a b c ha hb hc x

theorem affineCorrect (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x : Vec 2) :
    AffineCorrectAt (objective a b c) x := by
  intro hx
  rw [(affineCritical_iff a b c ha hb hc x).mp hx]
  exact zero_mem_iff_global_minimum.mpr (objective_minimum a b c ha.le hb.le hc.le)

/-- Strong convexity excludes nontrivial segments on the boundary of every
sublevel, hence in particular every positive sublevel used by the article. -/
theorem strict_contours (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (level : ℝ) (x y : Vec 2)
    (hseg : segment ℝ x y ⊆ frontier {z | objective a b c z ≤ level}) : x = y := by
  let mid : Vec 2 := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hm : mid ∈ segment ℝ x y := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have he (z : Vec 2) (hz : z ∈ segment ℝ x y) : objective a b c z = level :=
    frontier_le_subset_eq (convex_continuous (objective_convex a b c ha.le hb.le hc.le))
      continuous_const (hseg hz)
  have hx := he x (left_mem_segment ℝ x y)
  have hy := he y (right_mem_segment ℝ x y)
  have hmid := he mid hm
  have hs := (objective_strongConvex a b c).2 (mem_univ x) (mem_univ y)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hsq : sqNorm mid = (sqNorm x + sqNorm y) / 2 - sqNorm (y - x) / 4 := by
    dsimp [mid]
    convert sqNorm_convex_combination x y (1 / 2) using 1 <;> norm_num
    ring
  change objective a b c mid - (modulus a b c / 2) * sqNorm mid ≤
    (1 / 2) * (objective a b c x - (modulus a b c / 2) * sqNorm x) +
    (1 / 2) * (objective a b c y - (modulus a b c / 2) * sqNorm y) at hs
  rw [hx, hy, hmid, hsq] at hs
  have hz : sqNorm (y - x) = 0 := by
    have hμ := modulus_pos a b c ha hb hc
    apply le_antisymm _ (sqNorm_nonneg _)
    nlinarith
  exact (sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hz)).symm

theorem regular (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x : Vec 2)
    (hn : ¬ IsAffineCritical (objective a b c) x) :
    ContDiffAt ℝ 2 (objective a b c) x ∨
      PlanarCornerCharts.ConvexTwoBranchRegularAt (objective a b c) x := by
  apply PlanarMaxRegular.regular_of_finite_max_independent (objective_convex a b c ha hb hc)
    isOpen_univ (mem_univ x)
    (fun i => ⟨branch_convex a b c ha hb hc i, (branch_contDiff a b c i).contDiffOn⟩)
    (localFiniteMax a b c x) _ hn
  simpa only [coordinateGradient_eq] using gradient_affineIndependent a b c x

/-! ## Exact hypotheses of the planar and finite-maximum results -/

/-- The neighborhood regularity alternative as written in `art:planar-cluster`.
The differentiability and smoothness in this definition are full-space notions. -/
def PaperRegularAt (F : Vec 2 → ℝ) (p : Vec 2) : Prop :=
  (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
    (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₀ f₁ : Vec 2 → ℝ,
      ConvexOn ℝ V f₀ ∧ ConvexOn ℝ V f₁ ∧ ContDiffOn ℝ 2 f₀ V ∧ ContDiffOn ℝ 2 f₁ V ∧
      (∀ z ∈ V, F z = max (f₀ z) (f₁ z)) ∧ f₀ p = F p ∧ f₁ p = F p ∧
      LinearIndependent ℝ ![coordinateGradient f₀ p, coordinateGradient f₁ p])

theorem regular_paper (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x : Vec 2)
    (hn : ¬ IsAffineCritical (objective a b c) x) : PaperRegularAt (objective a b c) x := by
  by_cases ht : branch a b c 0 x = branch a b c 1 x
  · right
    have hx : x ≠ 0 := fun hx => hn ((affineCritical_iff a b c ha hb hc x).mpr hx)
    refine ⟨univ, isOpen_univ, mem_univ _, branch a b c 0, branch a b c 1,
      branch_convex a b c ha.le hb.le hc.le 0, branch_convex a b c ha.le hb.le hc.le 1,
      (branch_contDiff a b c 0).contDiffOn, (branch_contDiff a b c 1).contDiffOn,
      fun _ _ => rfl, ?_, ?_, ?_⟩
    · simp [objective, ht]
    · simp [objective, ht]
    · simpa only [coordinateGradient_eq] using tie_gradients_linearIndependent a b c ha hb hc ht hx
  · left
    refine ⟨{z | branch a b c 0 z ≠ branch a b c 1 z},
      isOpen_ne_fun (branch_contDiff a b c 0 (N := 0)).continuous
        (branch_contDiff a b c 1 (N := 0)).continuous, ht, ?_⟩
    intro z hz
    exact (contDiffAt_of_not_tie a b c
      (fun h => hz ((tie_equation a b c z).mpr h))).contDiffWithinAt

theorem argmin_eq (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    argmin (objective a b c) = {0} := by
  ext x
  constructor
  · intro hx
    exact objective_unique_zero a b c ha hb hc x
      (le_antisymm (by simpa only [objective_zero] using hx 0)
        (objective_nonneg a b c ha.le hb.le hc.le x))
  · rintro rfl
    exact objective_minimum a b c ha.le hb.le hc.le

/-- The literal article hypotheses, jointly, for every prescribed positive
sublevel. In particular the affine-critical correctness is a proved conclusion. -/
theorem paper_planar_hypotheses (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (B : ℝ) (hB : 0 < B) :
    ConvexOn ℝ univ (objective a b c) ∧ IsLeast (range (objective a b c)) 0 ∧ 0 < B ∧
      IsCompact {x | objective a b c x ≤ B} ∧
      (∀ t, 0 < t → t ≤ B → ∀ x y : Vec 2,
        segment ℝ x y ⊆ frontier {z | objective a b c z ≤ t} → x = y) ∧
      (∀ p, objective a b c p ≤ B → ¬ IsAffineCritical (objective a b c) p →
        PaperRegularAt (objective a b c) p) ∧
      {p | IsAffineCritical (objective a b c) p} ∩ {x | objective a b c x ≤ B} ⊆
        argmin (objective a b c) := by
  refine ⟨objective_convex a b c ha.le hb.le hc.le, objective_isLeast a b c ha.le hb.le hc.le,
    hB, sublevel_compact a b c ha hb hc B, fun t _ _ => strict_contours a b c ha hb hc t,
    fun p _ hn => regular_paper a b c ha hb hc p hn, ?_⟩
  rintro p ⟨hp, _⟩
  exact zero_mem_iff_global_minimum.mp (affineCorrect a b c ha hb hc p hp)

/-- Native library hypotheses for `planar_convergence_on_sublevel`, with attained
minimum zero and a positive upper level. They are obtained from the parameters,
before choosing a BFGS run. -/
structure PlanarHypotheses (F : Vec 2 → ℝ) (B : ℝ) : Prop where
  convex : ConvexOn ℝ univ F
  minimum : IsLeast (range F) 0
  positive_level : 0 < B
  compact : IsCompact {x | F x ≤ B}
  strict : ∀ t, 0 < t → t ≤ B → ∀ x y : Vec 2,
    segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y
  regular : ∀ p, F p ≤ B → ¬ IsAffineCritical F p →
    ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p
  correct : ∀ p, F p ≤ B → AffineCorrectAt F p

theorem planar_hypotheses (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (B : ℝ) (hB : 0 < B) : PlanarHypotheses (objective a b c) B :=
  ⟨objective_convex a b c ha.le hb.le hc.le, objective_isLeast a b c ha.le hb.le hc.le, hB,
    sublevel_compact a b c ha hb hc B, fun t _ _ => strict_contours a b c ha hb hc t,
    fun p _ hn => regular a b c ha.le hb.le hc.le p hn,
    fun p _ => affineCorrect a b c ha hb hc p⟩

theorem initial_active (i : Fin 2) : branch a b c i 0 = objective a b c 0 := by
  fin_cases i <;> simp [branch, objective_zero]

theorem initial_activeIndices :
    activeIndices (objective a b c) (branch a b c) 0 = Finset.univ := by
  ext i
  simp [initial_active]

/-- The original, indexed active gradients at the unique minimizer. -/
theorem initial_gradients :
    gradient a b c 0 0 = ![0, 1] ∧ gradient a b c 1 0 = ![0, -1] := by
  simpa using gradient_coordinates a b c 0

theorem initial_balance :
    (∑ i : Fin 2, (1 / 2 : ℝ) • gradient a b c i 0) = 0 := by
  rw [Fin.sum_univ_two, (initial_gradients a b c).1, (initial_gradients a b c).2]
  ext j
  fin_cases j <;> norm_num

/-- Half weights on the actual active index subtype, not just on a deduplicated
set of vectors. -/
theorem initial_active_family :
    AffineIndependent ℝ
      (fun i : activeIndices (objective a b c) (branch a b c) 0 =>
        coordinateGradient (branch a b c i) 0) ∧
      (∀ i : activeIndices (objective a b c) (branch a b c) 0, 0 < (fun _ => (1 / 2 : ℝ)) i) ∧
      (∑ _i : activeIndices (objective a b c) (branch a b c) 0, (1 / 2 : ℝ)) = 1 ∧
      (∑ i : activeIndices (objective a b c) (branch a b c) 0,
        (1 / 2 : ℝ) • coordinateGradient (branch a b c i) 0) = 0 := by
  refine ⟨?_, fun _ => by norm_num, ?_, ?_⟩
  · simpa only [coordinateGradient_eq] using
      (gradient_affineIndependent a b c 0).comp_embedding
        (Function.Embedding.subtype fun i : Fin 2 =>
          i ∈ activeIndices (objective a b c) (branch a b c) 0)
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, initial_activeIndices]
    norm_num
  · rw [Finset.sum_coe_sort (activeIndices (objective a b c) (branch a b c) 0)
      (fun i => (1 / 2 : ℝ) • coordinateGradient (branch a b c i) 0), initial_activeIndices]
    simpa only [coordinateGradient_eq] using initial_balance a b c

/-- Literal finite-max hypotheses with `x*=0`, `U=univ` and the actual active
indices. The weight function is explicit data, rather than an assumed balance. -/
structure FiniteMaxHypotheses {m : ℕ} (F : Vec 2 → ℝ) (f : Fin m → Vec 2 → ℝ)
    (w : activeIndices F f 0 → ℝ) : Prop where
  convex : ConvexOn ℝ univ F
  minimum : ∀ x, F 0 ≤ F x
  unique : ∀ x, F x = F 0 → x = 0
  branches : ∀ i, ConvexOn ℝ univ (f i) ∧ ContDiffOn ℝ 2 (f i) univ
  representation : ∀ x, IsGreatest (range fun i => f i x) (F x)
  contours : ∃ B, F 0 < B ∧ ∀ t, F 0 < t → t ≤ B → ∀ x y : Vec 2,
    segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y
  independent : AffineIndependent ℝ (fun i : activeIndices F f 0 => coordinateGradient (f i) 0)
  positive : ∀ i, 0 < w i
  sum_one : ∑ i, w i = 1
  balance : ∑ i, w i • coordinateGradient (f i) 0 = 0

theorem finite_max_hypotheses (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    FiniteMaxHypotheses (objective a b c) (branch a b c) (fun _ => 1 / 2) := by
  obtain ⟨hind, hpos, hsum, hbal⟩ := initial_active_family a b c
  exact ⟨objective_convex a b c ha.le hb.le hc.le,
    objective_minimum a b c ha.le hb.le hc.le,
    fun x hx => objective_unique_zero a b c ha hb hc x (by rwa [objective_zero] at hx),
    fun i => ⟨branch_convex a b c ha.le hb.le hc.le i, (branch_contDiff a b c i).contDiffOn⟩,
    objective_isGreatest a b c,
    ⟨1, by rw [objective_zero]; norm_num, fun t _ _ => strict_contours a b c ha hb hc t⟩,
    hind, hpos, hsum, hbal⟩

private theorem active_family_conversion {F : Vec 2 → ℝ} {m : ℕ} (f : Fin m → Vec 2 → ℝ)
    (hind : AffineIndependent ℝ fun i : activeIndices F f 0 => coordinateGradient (f i) 0)
    (w : activeIndices F f 0 → ℝ) (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hzero : ∑ i, w i • coordinateGradient (f i) 0 = 0) :
    AffineIndependent ℝ (fun j => coordinateGradient (f (activeIndexMap F f 0 j)) 0) ∧
      ∃ v : Vec (activeIndices F f 0).card, (∀ j, 0 < v j) ∧ ∑ j, v j = 1 ∧
        ∑ j, v j • coordinateGradient (f (activeIndexMap F f 0 j)) 0 = 0 := by
  set e := (activeIndices F f 0).orderIsoOfFin rfl
  have he : ∀ j, ((e j : activeIndices F f 0) : Fin m) = activeIndexMap F f 0 j :=
    fun j => Finset.coe_orderIsoOfFin_apply _ _ j
  refine ⟨?_, fun j => w (e j), fun j => hpos _, (Equiv.sum_comp e.toEquiv w).trans hsum, ?_⟩
  · convert hind.comp_embedding e.toEquiv.toEmbedding using 1
  · calc
      _ = ∑ i : activeIndices F f 0, w i • coordinateGradient (f i) 0 := by
        rw [← Equiv.sum_comp e.toEquiv
          (fun i : activeIndices F f 0 => w i • coordinateGradient (f i) 0)]
        apply Finset.sum_congr rfl
        intro j _
        rw [← he j]
        rfl
      _ = 0 := hzero

/-- A direct instantiation of the library theorem behind `art:planar-max`.
The basin is chosen before the run, its matrix and its line-search constants. -/
theorem local_finite_max_convergence (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 (objective a b c),
      objective a b c (R.x 0) < ε →
        Tendsto (fun k => objective a b c (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have H := finite_max_hypotheses a b c ha hb hc
  obtain ⟨hind, w, hpos, hsum, hbal⟩ := active_family_conversion (branch a b c) H.independent
    (fun _ => 1 / 2) H.positive H.sum_one H.balance
  obtain ⟨B, hB, hstrict⟩ := H.contours
  simpa only [objective_zero, zero_add] using
    PlanarMaxRegular.finite_max_local_basin H.convex 0 H.minimum H.unique isOpen_univ
      (mem_univ _) H.branches (localFiniteMax a b c 0) hind w hpos hsum hbal hB hstrict

/-- All positive sublevels give the same global convergence conclusion. -/
theorem convergence_on_sublevel (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (B : ℝ) (hB : 0 < B) (R : AdmissibleBFGSRun 2 (objective a b c))
    (hstart : objective a b c (R.x 0) ≤ B) :
    Tendsto (fun k => objective a b c (R.x k)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance (objective a b c) (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  have H := planar_hypotheses a b c ha hb hc B hB
  obtain ⟨hv, _, hed, hx⟩ := R.planar_convergence_on_sublevel 0
    (objective_minimum a b c ha.le hb.le hc.le) B H.compact hstart
    (fun t ht htb => H.strict t (by simpa only [objective_zero] using ht) htb)
    H.regular H.correct
  exact ⟨by simpa only [objective_zero] using hv, hed,
    hx (fun x hx => objective_unique_zero a b c ha hb hc x (by rwa [objective_zero] at hx))⟩

/-- Every infinite admissible run converges, without an initial-value restriction. -/
theorem global_convergence (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (R : AdmissibleBFGSRun 2 (objective a b c)) :
    Tendsto (fun k => objective a b c (R.x k)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance (objective a b c) (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) :=
  convergence_on_sublevel a b c ha hb hc (objective a b c (R.x 0) + 1)
    (by linarith [objective_nonneg a b c ha.le hb.le hc.le (R.x 0)]) R (by linarith)

/-! ## Existence of actual infinite full-BFGS runs -/

/-- Along any line through a differentiability point the tie polynomial has a
nonzero constant term. Thus the full-space nondifferentiability times are finite;
no nonzero-direction hypothesis is needed for this stronger assertion. -/
theorem nondifferentiable_line_finite (x p : Vec 2)
    (hx : DifferentiableAt ℝ (objective a b c) x) :
    {t : ℝ | ¬ DifferentiableAt ℝ (objective a b c) (x + t • p)}.Finite := by
  refine (AdmissibleRunExistence.quadratic_zeros_finite
    (a := (a - c) * p 0 ^ 2) (b := 2 * (a - c) * x 0 * p 0 + 2 * p 1)
    (c := (a - c) * x 0 ^ 2 + 2 * x 1) ?_).subset ?_
  · rintro ⟨_, _, hconst⟩
    apply (differentiableAt_iff a b c x).mp hx
    nlinarith
  · intro t ht
    have he : branch a b c 0 (x + t • p) = branch a b c 1 (x + t • p) := by
      by_contra hn
      exact ht ((differentiableAt_iff a b c _).mpr
        (fun h => hn ((tie_equation a b c _).mpr h)))
    simp only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
    change (a - c) * p 0 ^ 2 * t ^ 2 + (2 * (a - c) * x 0 * p 0 + 2 * p 1) * t +
      ((a - c) * x 0 ^ 2 + 2 * x 1) = 0
    linear_combination he

theorem gradient_ne_zero_of_hasFDerivAt (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x g : Vec 2} (hg : HasFDerivAt (objective a b c) (gradientFunctional g) x) : g ≠ 0 := by
  rintro rfl
  have hmin : ∀ z, objective a b c x ≤ objective a b c z := by
    intro z
    have hs := convex_supporting_inequality (objective_convex a b c ha.le hb.le hc.le) hg z
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hs
    linarith
  have hx : x = 0 := objective_unique_zero a b c ha hb hc x
    (le_antisymm (by simpa only [objective_zero] using hmin 0)
      (objective_nonneg a b c ha.le hb.le hc.le x))
  subst hx
  exact not_differentiableAt_of_tie a b c (by simp [branch]) hg.differentiableAt

/-- All hypotheses of the general arbitrary-initial-data existence theorem,
proved simultaneously for the same objective. -/
theorem objective_run_hypotheses (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ConvexOn ℝ univ (objective a b c) ∧ BddBelow (range (objective a b c)) ∧
      (∀ x p : Vec 2, DifferentiableAt ℝ (objective a b c) x →
        {t : ℝ | ¬ DifferentiableAt ℝ (objective a b c) (x + t • p)}.Finite) ∧
      ∀ x g, HasFDerivAt (objective a b c) (gradientFunctional g) x → g ≠ 0 :=
  ⟨objective_convex a b c ha.le hb.le hc.le,
    ⟨0, by rintro _ ⟨x, rfl⟩; exact objective_nonneg a b c ha.le hb.le hc.le x⟩,
    nondifferentiable_line_finite a b c,
    fun _ _ hg => gradient_ne_zero_of_hasFDerivAt a b c ha hb hc hg⟩

/-- Every differentiable start, every SPD initial matrix, and every fixed valid
Armijo--weak-Wolfe pair have an actual infinite full-BFGS run. This is an
existence statement about accepted steps, not a particular search implementation. -/
theorem exists_admissible_run (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x₀ : Vec 2} (hx₀ : DifferentiableAt ℝ (objective a b c) x₀)
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 (objective a b c),
      R.x 0 = x₀ ∧ R.g 0 = coordinateGradient (objective a b c) x₀ ∧
      R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ := by
  obtain ⟨hconv, hbdd, hline, hstat⟩ := objective_run_hypotheses a b c ha hb hc
  exact AdmissibleRunExistence.exists_admissible_run hconv hbdd
    (fun x p hx _ => (hline x p hx).countable) hstat
    (hasFDerivAt_coordinateGradient hx₀) hH₀ hc₁ hc₁₂ hc₂

/-- Joint non-vacuity: the full planar hypotheses on every positive sublevel,
the full finite-max hypotheses with positive half weights, convergence of every
admissible run, and a convergent actual run from arbitrary prescribed admissible
initial data all hold for this same parameterized objective. -/
theorem joint_witness (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x₀ : Vec 2} (hx₀ : DifferentiableAt ℝ (objective a b c) x₀)
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    (∀ B : ℝ, 0 < B → PlanarHypotheses (objective a b c) B) ∧
      FiniteMaxHypotheses (objective a b c) (branch a b c) (fun _ => 1 / 2) ∧
      (∀ R : AdmissibleBFGSRun 2 (objective a b c),
        Tendsto (fun k => objective a b c (R.x k)) atTop (𝓝 0) ∧
        Tendsto (fun k => euclideanSolutionDistance (objective a b c) (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0)) ∧
      ∃ R : AdmissibleBFGSRun 2 (objective a b c),
        R.x 0 = x₀ ∧ R.g 0 = coordinateGradient (objective a b c) x₀ ∧
        R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
        Tendsto (fun k => objective a b c (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨R, hx, hg, hH, h1, h2⟩ := exists_admissible_run a b c ha hb hc hx₀ H₀ hH₀ hc₁ hc₁₂ hc₂
  obtain ⟨hv, _, hxlim⟩ := global_convergence a b c ha hb hc R
  exact ⟨planar_hypotheses a b c ha hb hc, finite_max_hypotheses a b c ha hb hc,
    global_convergence a b c ha hb hc, R, hx, hg, hH, h1, h2, hv, hxlim⟩

/-! ## A fixed-band radial obstruction for `a=b=1`, `c=2` -/

namespace Radial

open TransportedCertificate RadialCertificate

abbrev F : Vec 2 → ℝ := objective 1 1 2

def base (r : ℝ) : Vec 2 := ![r, r ^ 2 / 2]
def oldPoint (r ε : ℝ) : Vec 2 := ![r, r ^ 2 / 2 + ε]
def newPoint (r ε : ℝ) : Vec 2 := ![r, r ^ 2 / 2 - ε / 2]
def oldGradient (r ε : ℝ) : Vec 2 := gradient 1 1 2 0 (oldPoint r ε)
def newGradient (r ε : ℝ) : Vec 2 := gradient 1 1 2 1 (newPoint r ε)
def tieValue (r : ℝ) : ℝ := 3 * r ^ 2 / 2 + r ^ 4 / 4

/-- The band is fixed by `r` before any endpoint separation or candidate bound. -/
def band (r : ℝ) : Set (Vec 2) := {x | tieValue r / 2 ≤ F x ∧ F x ≤ 2 * tieValue r}

theorem base_value (r : ℝ) : F (base r) = tieValue r := by
  have h0 : branch 1 1 2 0 (base r) = tieValue r := by
    simp [branch, base, tieValue]
    ring
  have h1 : branch 1 1 2 1 (base r) = tieValue r := by
    simp [branch, base, tieValue]
    ring
  rw [F, objective, h0, h1, max_self]

theorem tieValue_pos {r : ℝ} (hr : 0 < r) : 0 < tieValue r := by
  dsimp only [tieValue]
  positivity

theorem crossing_active (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    branch 1 1 2 1 (oldPoint r ε) < branch 1 1 2 0 (oldPoint r ε) ∧
      branch 1 1 2 0 (newPoint r ε) < branch 1 1 2 1 (newPoint r ε) := by
  simp only [branch, oldPoint, newPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, one_mul]
  constructor <;> nlinarith

theorem pair_step (r ε : ℝ) : pairStep (oldPoint r ε) (newPoint r ε) = ![0, -3 * ε / 2] := by
  ext i
  fin_cases i <;> simp [pairStep, oldPoint, newPoint]
  ring

theorem pair_decrease (r ε : ℝ) :
    pairDecrease (oldPoint r ε) (newPoint r ε) (oldGradient r ε) =
      3 * ε * (1 + r ^ 2 + 2 * ε) / 2 := by
  rw [pairDecrease, pair_step, oldGradient, (gradient_coordinates 1 1 2 _).1]
  simp [oldPoint, dot, Fin.sum_univ_two]
  ring

theorem pair_curvature (r ε : ℝ) :
    pairCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) =
      3 * ε + 9 * ε ^ 2 / 2 := by
  rw [pairCurvature, pair_step, oldGradient, newGradient,
    (gradient_coordinates 1 1 2 _).1, (gradient_coordinates 1 1 2 _).2]
  simp [oldPoint, newPoint, dot, Fin.sum_univ_two]
  ring

theorem pair_value_difference (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    F (oldPoint r ε) - F (newPoint r ε) =
      (1 / 2 + 3 * r ^ 2 / 2) * ε + 3 * ε ^ 2 / 4 := by
  obtain ⟨h0, h1⟩ := crossing_active r hε
  rw [F, objective, max_eq_left h0.le, objective, max_eq_right h1.le]
  simp [branch, oldPoint, newPoint]
  ring

theorem radial_numerator (r ε : ℝ) :
    radialNumerator 0 (newPoint r ε) (oldGradient r ε) (newGradient r ε) =
      r ^ 2 + (1 - 3 * r ^ 2 / 2) * ε + 3 * ε ^ 2 / 2 := by
  rw [radialNumerator, oldGradient, newGradient,
    (gradient_coordinates 1 1 2 _).1, (gradient_coordinates 1 1 2 _).2]
  simp [oldPoint, newPoint, dot, Fin.sum_univ_two]
  ring

/-- The explicit crossing pairs are eligible for `(c₁,c₂)=(1/4,1/2)` for
every `ε>0` whenever `r²<3`; in particular this holds for all sufficiently
small positive separations at any fixed sufficiently small `r>0`. -/
theorem pair_eligible {r ε : ℝ} (hr : r ^ 2 < 3) (hε : 0 < ε) :
    EligiblePair F (1 / 4) (1 / 2)
      (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) := by
  obtain ⟨h0, h1⟩ := crossing_active r hε
  refine ⟨winner_zero_hasGradient 1 1 2 h0, winner_one_hasGradient 1 1 2 h1, ?_, ?_, ?_, ?_⟩
  · rw [pair_decrease]
    positivity
  · rw [pair_decrease, pair_value_difference r hε]
    nlinarith [mul_nonneg hε.le (sq_nonneg r)]
  · rw [pair_decrease, pair_value_difference r hε]
    nlinarith [sq_nonneg ε]
  · rw [pair_decrease, pair_curvature]
    nlinarith [mul_pos hε (sub_pos.mpr hr), sq_nonneg ε]

theorem pair_points_tendsto (r : ℝ) :
    Tendsto (oldPoint r) (𝓝[>] 0) (𝓝 (base r)) ∧
      Tendsto (newPoint r) (𝓝[>] 0) (𝓝 (base r)) := by
  have h0 : Continuous (oldPoint r) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · change Continuous (fun ε : ℝ => r ^ 2 / 2 + ε)
      fun_prop
  have h1 : Continuous (newPoint r) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · change Continuous (fun ε : ℝ => r ^ 2 / 2 - ε / 2)
      fun_prop
  exact ⟨by simpa [oldPoint, base] using (h0.tendsto 0).mono_left nhdsWithin_le_nhds,
    by simpa [newPoint, base] using (h1.tendsto 0).mono_left nhdsWithin_le_nhds⟩

theorem radial_numerator_tendsto (r : ℝ) :
    Tendsto (fun ε => radialNumerator 0 (newPoint r ε) (oldGradient r ε) (newGradient r ε))
      (𝓝[>] 0) (𝓝 (r ^ 2)) := by
  simp_rw [radial_numerator]
  have h : Continuous (fun ε : ℝ => r ^ 2 + (1 - 3 * r ^ 2 / 2) * ε + 3 * ε ^ 2 / 2) := by
    fun_prop
  simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds

theorem pair_decrease_tendsto (r : ℝ) :
    Tendsto (fun ε => pairDecrease (oldPoint r ε) (newPoint r ε) (oldGradient r ε))
      (𝓝[>] 0) (𝓝 0) := by
  simp_rw [pair_decrease]
  have h : Continuous (fun ε : ℝ => 3 * ε * (1 + r ^ 2 + 2 * ε) / 2) := by fun_prop
  simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds

theorem pair_curvature_tendsto (r : ℝ) :
    Tendsto (fun ε => pairCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε))
      (𝓝[>] 0) (𝓝[>] 0) := by
  simp_rw [pair_curvature]
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have h : Continuous (fun ε : ℝ => 3 * ε + 9 * ε ^ 2 / 2) := by fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    change 0 < 3 * ε + 9 * ε ^ 2 / 2
    positivity

theorem radial_quotient_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => (radialNumerator 0 (newPoint r ε) (oldGradient r ε) (newGradient r ε)) ^ 2 /
      pairCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε))
      (𝓝[>] 0) atTop := by
  have hn := (radial_numerator_tendsto r).pow 2
  simpa only [div_eq_mul_inv] using hn.pos_mul_atTop (sq_pos_of_pos (sq_pos_of_pos hr))
    (pair_curvature_tendsto r).inv_tendsto_nhdsGT_zero

/-- Arbitrarily small eligible decreases violate every proposed radial bound
on this one fixed positive band. The band is independent of `δ`, `C`, and `ε`. -/
theorem eligible_radial_unbounded_on_fixed_band {r : ℝ} (hr : 0 < r) (hr3 : r ^ 2 < 3) :
    ∀ δ : ℝ, 0 < δ → ∀ C : ℝ, ∃ ε : ℝ, 0 < ε ∧
      oldPoint r ε ∈ band r ∧ newPoint r ε ∈ band r ∧
      EligiblePair F (1 / 4) (1 / 2)
        (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) ∧
      pairDecrease (oldPoint r ε) (newPoint r ε) (oldGradient r ε) ≤ δ ∧
      C * pairCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) <
        (radialNumerator 0 (newPoint r ε) (oldGradient r ε) (newGradient r ε)) ^ 2 := by
  intro δ hδ C
  have hℓ := tieValue_pos hr
  have hcont : Continuous F := convex_continuous (objective_convex 1 1 2 (by norm_num)
    (by norm_num) (by norm_num))
  have hvals0 : Tendsto (fun ε => F (oldPoint r ε)) (𝓝[>] 0) (𝓝 (tieValue r)) := by
    simpa only [base_value] using (hcont.tendsto _).comp (pair_points_tendsto r).1
  have hvals1 : Tendsto (fun ε => F (newPoint r ε)) (𝓝[>] 0) (𝓝 (tieValue r)) := by
    simpa only [base_value] using (hcont.tendsto _).comp (pair_points_tendsto r).2
  have hband0 := hvals0.eventually (Ioo_mem_nhds (by linarith : tieValue r / 2 < tieValue r)
    (by linarith : tieValue r < 2 * tieValue r))
  have hband1 := hvals1.eventually (Ioo_mem_nhds (by linarith : tieValue r / 2 < tieValue r)
    (by linarith : tieValue r < 2 * tieValue r))
  have hd := (pair_decrease_tendsto r).eventually (eventually_lt_nhds hδ)
  have hq := (radial_quotient_tendsto hr).eventually (eventually_gt_atTop C)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hx, hz, hdε, hqε⟩ := (hp.and (hband0.and (hband1.and (hd.and hq)))).exists
  refine ⟨ε, hε, ⟨hx.1.le, hx.2.le⟩, ⟨hz.1.le, hz.2.le⟩,
    pair_eligible hr3 hε, hdε.le, ?_⟩
  exact (lt_div_iff₀ (by rw [pair_curvature]; positivity)).mp hqε

/-- Every neighborhood of the minimizer contains an entire positive band on
which the eligible radial quotient is unbounded. A positive band and a fixed
`r` are chosen before the small-step threshold and proposed radial constant. -/
theorem radial_obstruction_in_every_neighborhood {U : Set (Vec 2)} (hU : U ∈ 𝓝 (0 : Vec 2)) :
    ∃ r : ℝ, 0 < r ∧ r ^ 2 < 3 ∧ 0 < tieValue r ∧ band r ⊆ U ∧
      ∀ δ : ℝ, 0 < δ → ∀ C : ℝ, ∃ ε : ℝ, 0 < ε ∧
        oldPoint r ε ∈ band r ∧ newPoint r ε ∈ band r ∧
        EligiblePair F (1 / 4) (1 / 2)
          (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) ∧
        pairDecrease (oldPoint r ε) (newPoint r ε) (oldGradient r ε) ≤ δ ∧
        C * pairCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) <
          (radialNumerator 0 (newPoint r ε) (oldGradient r ε) (newGradient r ε)) ^ 2 := by
  obtain ⟨η, hη, hsub⟩ := Localization.neighborhood_basin
    (objective_convex 1 1 2 (by norm_num) (by norm_num) (by norm_num)) 0
    (objective_minimum 1 1 2 (by norm_num) (by norm_num) (by norm_num))
    (fun x hx => objective_unique_zero 1 1 2 (by norm_num) (by norm_num) (by norm_num) x
      (by rwa [objective_zero] at hx)) hU
  simp only [objective_zero, zero_add] at hsub
  have hlim : Tendsto (fun r => 2 * tieValue r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Continuous (fun r => 2 * tieValue r) := by unfold tieValue; fun_prop
    simpa [tieValue] using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsquare : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_id.pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hr3, hrη⟩ := (hp.and
    ((hsquare.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3))).and
      (hlim.eventually (eventually_lt_nhds hη)))).exists
  refine ⟨r, hr, hr3, tieValue_pos hr, ?_, eligible_radial_unbounded_on_fixed_band hr hr3⟩
  intro x hx
  exact hsub (hx.2.trans hrη.le)

theorem not_radial_secant_on_neighborhood {U : Set (Vec 2)} (hU : U ∈ 𝓝 (0 : Vec 2)) :
    ¬ HasRadialSecantBounds F U 0 := by
  obtain ⟨r, _, _, hℓ, hband, hex⟩ := radial_obstruction_in_every_neighborhood hU
  intro hRS
  obtain ⟨C, hC⟩ := hRS (tieValue r / 2) (by positivity)
  obtain ⟨ε, _, hx, hz, hp, _, hbad⟩ := hex 1 zero_lt_one C
  have ht : 0 < secantCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε) := by
    change 0 < pairCurvature (oldPoint r ε) (newPoint r ε) (oldGradient r ε) (newGradient r ε)
    nlinarith [hp.curvature, hp.decrease_pos]
  have horder : F (newPoint r ε) ≤ F (oldPoint r ε) := by
    linarith [hp.armijo, hp.decrease_pos]
  have hbound := hC _ _ _ _ (hband hx) (hband hz)
    (by simpa only [F, objective_zero, zero_add] using hz.1) horder hp.gradient_x hp.gradient_z ht
  exact (not_lt_of_ge hbound) hbad

theorem not_radial_secant_on_sublevel {B : ℝ} (hB : 0 < B) :
    ¬ HasRadialSecantBounds F {x | F x ≤ B} 0 := by
  apply not_radial_secant_on_neighborhood
  have hn : {x | F x < B} ∈ 𝓝 (0 : Vec 2) :=
    (isOpen_lt (convex_continuous (objective_convex 1 1 2 (by norm_num) (by norm_num)
      (by norm_num))) continuous_const).mem_nhds (by
        change objective 1 1 2 0 < B
        rwa [objective_zero])
  exact mem_of_superset hn (fun x (hx : F x < B) => show F x ≤ B from hx.le)

end Radial

/-- A numerical joint witness, including an actual infinite run, on the genuinely
curved-switching objective. Its initial sublevel is contained in `{F≤1}`. -/
theorem concrete_joint_witness :
    (∀ B : ℝ, 0 < B → PlanarHypotheses (objective 1 1 2) B) ∧
      FiniteMaxHypotheses (objective 1 1 2) (branch 1 1 2) (fun _ => 1 / 2) ∧
      (∀ U : Set (Vec 2), U ∈ 𝓝 (0 : Vec 2) →
        ¬ RadialCertificate.HasRadialSecantBounds (objective 1 1 2) U 0) ∧
      ∃ R : AdmissibleBFGSRun 2 (objective 1 1 2),
        R.x 0 = ![0, 1 / 4] ∧ R.H 0 = 1 ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
        objective 1 1 2 (R.x 0) = 5 / 16 ∧
        Tendsto (fun k => objective 1 1 2 (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hd : DifferentiableAt ℝ (objective 1 1 2) ![0, 1 / 4] := by
    rw [differentiableAt_iff]
    norm_num
  obtain ⟨hp, hf, _, R, hx, _, hH, h1, h2, hv, hxlim⟩ :=
    joint_witness 1 1 2 (by norm_num) (by norm_num) (by norm_num) hd 1 Matrix.PosDef.one
      (c₁ := 1 / 4) (c₂ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, hf, fun _ hU => Radial.not_radial_secant_on_neighborhood hU,
    R, hx, hH, h1, h2, ?_, hv, hxlim⟩
  rw [hx]
  norm_num [objective, branch]

end BfgsVerification.TwoQuadraticExample
