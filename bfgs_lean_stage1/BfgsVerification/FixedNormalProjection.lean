import BfgsVerification.FrameNorms
import BfgsVerification.SubdifferentialDifferentiability
import BfgsVerification.FixedNormalStrongConvex

/-! Actual Euclidean projection onto a fixed normal complement, with a derived
orthonormal matrix representation. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace FixedNormal

def tangentProjection {n : ℕ} (a v : Vec n) : Vec n := v - dot a v • a

def tangentMap {n : ℕ} (a : Vec n) : Vec n →ₗ[ℝ] Vec n where
  toFun := tangentProjection a
  map_add' := by
    intro v w
    unfold tangentProjection
    change v + w - (a ⬝ᵥ (v + w)) • a = _
    rw [dotProduct_add]
    unfold dot dotProduct
    module
  map_smul' := by
    intro c v
    unfold tangentProjection
    change c • v - (a ⬝ᵥ (c • v)) • a = c • (v - dot a v • a)
    rw [dotProduct_smul]
    simp only [smul_eq_mul, id_eq]
    unfold dot dotProduct
    module

@[simp] theorem tangentMap_apply {n : ℕ} (a v : Vec n) :
    tangentMap a v = tangentProjection a v := rfl

theorem continuous_tangentProjection {n : ℕ} (a : Vec n) :
    Continuous (tangentProjection a) := by
  unfold tangentProjection dot
  fun_prop

theorem tangentProjection_normal_zero {n : ℕ} {a : Vec n} (ha : sqNorm a = 1) (v : Vec n) :
    dot a (tangentProjection a v) = 0 := by
  change a ⬝ᵥ (v - dot a v • a) = 0
  rw [dotProduct_sub, dotProduct_smul]
  have haa : a ⬝ᵥ a = 1 := by simpa only [dotProduct, sqNorm, pow_two] using ha
  rw [haa]
  change dot a v - dot a v * 1 = 0
  ring

theorem tangentProjection_eq_self {n : ℕ} {a v : Vec n} (hv : dot a v = 0) :
    tangentProjection a v = v := by simp [tangentProjection, hv]

theorem sqNorm_sub_smul {n : ℕ} (v a : Vec n) (c : ℝ) :
    sqNorm (v - c • a) = sqNorm v - 2 * c * dot a v + c ^ 2 * sqNorm a := by
  simp only [sqNorm, dot, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tangentProjection_pythagorean {n : ℕ} {a : Vec n} (ha : sqNorm a = 1) (v : Vec n) :
    sqNorm (tangentProjection a v) + (dot a v) ^ 2 = sqNorm v := by
  rw [tangentProjection, sqNorm_sub_smul, ha]
  ring

theorem sqNorm_tangentProjection_le {n : ℕ} {a : Vec n} (ha : sqNorm a = 1) (v : Vec n) :
    sqNorm (tangentProjection a v) ≤ sqNorm v := by
  nlinarith [tangentProjection_pythagorean ha v, sq_nonneg (dot a v)]

/-- An actual orthonormal-column matrix for the normal complement, including the
zero-dimensional tangent space in dimension one. -/
theorem exists_tangent_matrix {n : ℕ} {a : Vec n} (ha : sqNorm a = 1) :
    ∃ r : ℕ, ∃ U : Matrix (Fin n) (Fin r) ℝ,
      Uᵀ * U = 1 ∧ Uᵀ.mulVec a = 0 ∧
      ∀ v : Vec n, (U * Uᵀ).mulVec v = tangentProjection a v := by
  let ae : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Vec n)).symm a
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (ℝ ∙ ae)ᗮ
  obtain ⟨U, hU, hrange⟩ := FrameNorms.orthonormal_matrix_for_subspace S
  have hr (v : Vec n) : dot a v = 0 ↔ ∃ c, U.mulVec c = v := by
    have he := hrange ((WithLp.equiv 2 (Vec n)).symm v)
    simp only [S, Submodule.mem_orthogonal_singleton_iff_inner_right,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ae] at he
    change v ⬝ᵥ a = 0 ↔ ∃ c, U.mulVec c = v at he
    simpa only [dot, dotProduct_comm] using he
  have hUa : Uᵀ.mulVec a = 0 := by
    ext j
    have hc : U.mulVec (Pi.single j 1) = fun i => U i j := by
      ext i
      simp only [Matrix.mulVec, dotProduct_single_one]
    have hz := (hr (fun i => U i j)).mpr ⟨Pi.single j 1, hc⟩
    change dotProduct (fun i => U i j) a = 0
    simpa only [dot, dotProduct_comm] using hz
  refine ⟨Module.finrank ℝ S, U, hU, hUa, ?_⟩
  intro v
  obtain ⟨c, hc⟩ := (hr (tangentProjection a v)).mp (tangentProjection_normal_zero ha v)
  have hUv : Uᵀ.mulVec (tangentProjection a v) = Uᵀ.mulVec v := by
    simp only [tangentProjection, Matrix.mulVec_sub, Matrix.mulVec_smul, hUa, smul_zero, sub_zero]
  have he : c = Uᵀ.mulVec v := by
    calc
      c = (Uᵀ * U).mulVec c := by rw [hU, Matrix.one_mulVec]
      _ = Uᵀ.mulVec (U.mulVec c) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = Uᵀ.mulVec v := by rw [hc, hUv]
  rw [← Matrix.mulVec_mulVec, ← he, hc]

/-- The squared norm of tangential frame coordinates is the actual tangential
projection norm; this is a derived identity, not a norm equivalence assumption. -/
theorem tangent_matrix_sqNorm {n r : ℕ} (a : Vec n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = tangentProjection a v) (v : Vec n) :
    sqNorm (Uᵀ.mulVec v) = sqNorm (tangentProjection a v) := by
  rw [← SmoothSubspace.sqNorm_projection U hU, hproj]

/-- If all vectors have the same tangential projection, their affine hull does
as well. This implication needs no nondegeneracy of that set. -/
theorem projection_of_mem_affineSpan {n : ℕ} (a A : Vec n) {G : Set (Vec n)}
    (hG : ∀ g ∈ G, tangentProjection a g = A) {v : Vec n}
    (hv : v ∈ affineSpan ℝ G) : tangentProjection a v = A := by
  let C : AffineSubspace ℝ (Vec n) :=
    { carrier := {v | tangentMap a v = A}
      smul_vsub_vadd_mem := by
        intro c p q r hp hq hr
        change tangentMap a (c • (p - q) + r) = A
        rw [map_add, map_smul, map_sub, hp, hq, hr, sub_self, smul_zero, zero_add] }
  have hGC : affineSpan ℝ G ≤ C := affineSpan_le.mpr hG
  exact hGC hv

/-- Distinct parallel supports span the entire normal affine line, in the form
needed for affine-zero detection. -/
theorem zero_mem_affineSpan_of_projection_zero {n : ℕ} (a : Vec n) {G : Set (Vec n)}
    (hG : ∀ g ∈ G, tangentProjection a g = 0)
    {g h : Vec n} (hg : g ∈ G) (hh : h ∈ G) (hne : g ≠ h) :
    (0 : Vec n) ∈ affineSpan ℝ G := by
  have hge : g = dot a g • a := sub_eq_zero.mp (hG g hg)
  have hhe : h = dot a h • a := sub_eq_zero.mp (hG h hh)
  have hd : dot a h - dot a g ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    apply hne
    rw [hge, hhe, he']
  have hmem := (affineSpan ℝ G).smul_vsub_vadd_mem
    (-dot a g / (dot a h - dot a g)) (subset_affineSpan ℝ G hh)
    (subset_affineSpan ℝ G hg) (subset_affineSpan ℝ G hg)
  let c : ℝ := -dot a g / (dot a h - dot a g)
  have hcoef : c * (dot a h - dot a g) + dot a g = 0 := by
    dsimp [c]
    field_simp [hd]
  have heq : c • (h - g) + g = (0 : Vec n) := by
    calc
      _ = c • (dot a h • a - dot a g • a) + dot a g • a :=
        congrArg₂ (fun v w : Vec n => c • (v - w) + w) hhe hge
      _ = (c * (dot a h - dot a g) + dot a g) • a := by module
      _ = 0 := by rw [hcoef, zero_smul]
  change c • (h - g) + g ∈ affineSpan ℝ G at hmem
  rwa [heq] at hmem

/-- At a genuinely nondifferentiable point, a common tangential projection
vanishes exactly when the actual subdifferential is affine critical. -/
theorem affine_critical_iff_tangent_zero {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x a A : Vec n}
    (hA : ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A)
    (hx : ¬DifferentiableAt ℝ F x) :
    (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F x) ↔ A = 0 := by
  constructor
  · intro hz
    have he := projection_of_mem_affineSpan a A (fun g hg => hA g hg) hz
    simpa [tangentProjection, dot] using he.symm
  · intro hAz
    obtain ⟨g, hg, h, hh, hne⟩ :=
      ConvexSubdifferential.exists_distinct_supports_of_not_differentiableAt hF hx
    apply zero_mem_affineSpan_of_projection_zero a (fun g hg => (hA g hg).trans hAz) hg hh hne

/-- On the optimizer's hyperplane, a vanishing common tangential support forces
the point to be the optimizer, including differentiable exceptional points. -/
theorem tangent_zero_on_minimizer_plane {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {U : Set (Vec n)} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : EuclideanStrongConvexOn U μ F) {star p a : Vec n}
    (hstar : star ∈ U) (hp : p ∈ U) (hmin : ∀ z, F star ≤ F z)
    (hplane : dot a p = dot a star)
    (hA : ∀ g, Homogeneous.Supports F p g → tangentProjection a g = 0) : p = star := by
  obtain ⟨g, hg⟩ := ConvexSubdifferential.subdifferential_nonempty hF p
  have hz : Homogeneous.Supports F star (0 : Vec n) :=
    ConvexSubdifferential.zero_mem_iff_global_minimum.mpr hmin
  have hs := strong_support_monotonicity hstrong hstar hp hz hg
  have hge : g = dot a g • a := sub_eq_zero.mp (hA g hg)
  have had : dot a (p - star) = 0 := by
    change dotProduct a (p - star) = 0
    rw [dotProduct_sub]
    exact sub_eq_zero.mpr hplane
  have hgd : dot (g - 0) (p - star) = 0 := by
    simp only [sub_zero]
    change dotProduct g (p - star) = 0
    conv_lhs => arg 1; rw [hge]
    rw [smul_dotProduct]
    change dot a g * dot a (p - star) = 0
    rw [had, mul_zero]
  rw [hgd] at hs
  have hsq : sqNorm (p - star) ≤ 0 := by nlinarith
  have hnorm : ‖p - star‖ ≤ 0 :=
    ConvexSubdifferential.norm_le_of_sqNorm_le le_rfl (by simpa using hsq)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

end FixedNormal
end BfgsVerification
