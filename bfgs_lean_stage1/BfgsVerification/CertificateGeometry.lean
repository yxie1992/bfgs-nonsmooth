import BfgsVerification.IncomingJumpObstruction
import BfgsVerification.EuclideanEstimates
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Module G comparison ellipsoids use the actual Euclidean unit ball.
All square roots, projections, supports, and ranges below are finite-matrix
objects; no regularity of a field of such matrices is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Set Matrix Filter

namespace BfgsVerification.CertificateGeometry

def euclideanUnitBall {n : ℕ} : Set (Vec n) := {v | sqNorm v ≤ 1}

theorem sqNorm_smul {n : ℕ} (a : ℝ) (v : Vec n) :
    sqNorm (a • v) = a ^ 2 * sqNorm v := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem sqNorm_eq_zero_iff {n : ℕ} (v : Vec n) : sqNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hi : (v i) ^ 2 ≤ sqNorm v :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    rw [h] at hi
    have : v i = 0 := by nlinarith [sq_nonneg (v i)]
    exact this
  · rintro rfl
    simp [sqNorm]

theorem dot_self {n : ℕ} (v : Vec n) : dot v v = sqNorm v := by
  simp [dot, sqNorm, pow_two]

theorem dot_mulVec {n : ℕ} (A : Mat n) (a v : Vec n) :
    dot a (A.mulVec v) = dot (Aᵀ.mulVec a) v := by
  exact (dotProduct_mulVec a A v).trans (by rw [Matrix.mulVec_transpose]; rfl)

theorem linear_functional_eq_dot {n : ℕ} (f : Vec n →ₗ[ℝ] ℝ) :
    ∃ a : Vec n, ∀ v, f v = dot a v := by
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  intro v
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  have hs : Pi.single i (v i) = v i • (Pi.single i 1 : Vec n) := by
    ext j
    by_cases h : j = i <;> simp [h, Pi.single_apply]
  rw [hs, map_smul, smul_eq_mul, mul_comm]

theorem euclideanUnitBall_eq {n : ℕ} :
    (euclideanUnitBall : Set (Vec n)) =
      euclideanVector ⁻¹' Metric.closedBall 0 1 := by
  ext v
  simp only [euclideanUnitBall, mem_setOf_eq, mem_preimage, Metric.mem_closedBall,
    dist_zero_right]
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector v)
  change ‖euclideanVector v‖ ^ 2 = sqNorm v at hn
  rw [← hn]
  constructor <;> intro h <;> nlinarith [norm_nonneg (euclideanVector v)]

theorem euclideanUnitBall_convex {n : ℕ} : Convex ℝ (euclideanUnitBall : Set (Vec n)) := by
  rw [euclideanUnitBall_eq]
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).linear_preimage
    (WithLp.linearEquiv 2 ℝ (Vec n)).symm.toLinearMap

theorem euclideanUnitBall_compact {n : ℕ} : IsCompact (euclideanUnitBall : Set (Vec n)) := by
  have hclosed : IsClosed (euclideanUnitBall : Set (Vec n)) :=
    isClosed_le continuous_sqNorm continuous_const
  apply (isCompact_closedBall (0 : Vec n) 1).of_isClosed_subset hclosed
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hi : (v i) ^ 2 ≤ sqNorm v :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  have hs : |v i| ^ 2 ≤ 1 := by simpa using hi.trans hv
  nlinarith [abs_nonneg (v i)]

theorem unitBall_support_upper {n : ℕ} (a : Vec n) {v : Vec n}
    (hv : v ∈ euclideanUnitBall) : dot a v ≤ Real.sqrt (sqNorm a) := by
  have h := abs_dot_le_of_sqNorm_le a v (Real.sqrt (sqNorm a)) 1
    (Real.sqrt_nonneg _) zero_le_one (by rw [Real.sq_sqrt (sqNorm_nonneg a)]) (by simpa using hv)
  simpa only [mul_one] using (le_abs_self (dot a v)).trans h

theorem unitBall_support_attained {n : ℕ} (a : Vec n) :
    ∃ v ∈ euclideanUnitBall, dot a v = Real.sqrt (sqNorm a) := by
  by_cases ha : a = 0
  · subst a
    exact ⟨0, by simp [euclideanUnitBall, sqNorm], by simp [dot, sqNorm]⟩
  have hq : 0 < sqNorm a := (sqNorm_nonneg a).lt_of_ne'
    (fun hz => ha ((sqNorm_eq_zero_iff a).mp hz))
  have hr : 0 < Real.sqrt (sqNorm a) := Real.sqrt_pos.mpr hq
  refine ⟨(Real.sqrt (sqNorm a))⁻¹ • a, ?_, ?_⟩
  · change sqNorm ((Real.sqrt (sqNorm a))⁻¹ • a) ≤ 1
    rw [sqNorm_smul, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']
  · rw [dot_smul_right, dot_self, ← Real.sq_sqrt hq.le]
    field_simp [hr.ne']

/-- A linear image of the Euclidean unit ball, in the coordinate model. -/
def matrixBall {n : ℕ} (A : Mat n) : Set (Vec n) := A.mulVec '' euclideanUnitBall

theorem matrixBall_compact {n : ℕ} (A : Mat n) : IsCompact (matrixBall A) := by
  apply euclideanUnitBall_compact.image
  fun_prop

theorem matrixBall_convex {n : ℕ} (A : Mat n) : Convex ℝ (matrixBall A) :=
  euclideanUnitBall_convex.linear_image A.mulVecLin

theorem matrixBall_support_upper {n : ℕ} (A : Mat n) (a : Vec n)
    {v : Vec n} (hv : v ∈ matrixBall A) :
    dot a v ≤ Real.sqrt (sqNorm (Aᵀ.mulVec a)) := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [dot_mulVec]
  exact unitBall_support_upper _ hw

theorem matrixBall_support_attained {n : ℕ} (A : Mat n) (a : Vec n) :
    ∃ v ∈ matrixBall A, dot a v = Real.sqrt (sqNorm (Aᵀ.mulVec a)) := by
  obtain ⟨w, hw, he⟩ := unitBall_support_attained (Aᵀ.mulVec a)
  exact ⟨A.mulVec w, ⟨w, hw, rfl⟩, by rwa [dot_mulVec]⟩

/-- Actual finite PSD square-root ellipsoid printed in Module G. -/
def ellipsoid {n : ℕ} {W : Mat n} (hW : W.PosSemidef) : Set (Vec n) := matrixBall hW.sqrt

theorem sqrt_support_energy {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (a : Vec n) :
    sqNorm (hW.sqrtᵀ.mulVec a) = metricEnergy W a := by
  have hs : hW.sqrtᵀ = hW.sqrt := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.posSemidef_sqrt.isHermitian
  have he := IncomingJump.metricEnergy_gram hW.sqrt a
  rw [hs, ← pow_two, hW.sq_sqrt] at he
  simpa only [hs] using he.symm

theorem ellipsoid_support_upper {n : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (a : Vec n) {v : Vec n} (hv : v ∈ ellipsoid hW) : dot a v ≤ Real.sqrt (metricEnergy W a) := by
  simpa only [sqrt_support_energy] using matrixBall_support_upper hW.sqrt a hv

theorem ellipsoid_support_attained {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (a : Vec n) :
    ∃ v ∈ ellipsoid hW, dot a v = Real.sqrt (metricEnergy W a) := by
  simpa only [sqrt_support_energy] using matrixBall_support_attained hW.sqrt a

/-- The literal support supremum is attained, also for degenerate ellipsoids. -/
theorem ellipsoid_support {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (a : Vec n) :
    sSup ((dot a) '' ellipsoid hW) = Real.sqrt (metricEnergy W a) := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ellipsoid_support_attained hW a
  · rintro t ⟨v, hv, rfl⟩
    exact ellipsoid_support_upper hW a hv

theorem ellipsoid_neg_mem {n : ℕ} {W : Mat n} (hW : W.PosSemidef)
    {v : Vec n} (hv : v ∈ ellipsoid hW) : -v ∈ ellipsoid hW := by
  rcases hv with ⟨w, hw, rfl⟩
  refine ⟨-w, ?_, Matrix.mulVec_neg w hW.sqrt⟩
  change sqNorm (-w) ≤ 1
  simpa [sqNorm] using hw

theorem ellipsoid_abs_support_upper {n : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (a : Vec n) {v : Vec n} (hv : v ∈ ellipsoid hW) :
    |dot a v| ≤ Real.sqrt (metricEnergy W a) := by
  apply abs_le.mpr
  have hn := ellipsoid_support_upper hW a (ellipsoid_neg_mem hW hv)
  have hp := ellipsoid_support_upper hW a hv
  simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at hn
  change -dot a v ≤ Real.sqrt (metricEnergy W a) at hn
  exact ⟨by linarith, hp⟩

/-- Visibility is exactly the presence of a direction with the stated descent
magnitude in the comparison ellipsoid. -/
theorem ellipsoid_visibility_iff {n : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (g : Vec n) (m : ℝ) (hm : 0 ≤ m) :
    m ≤ metricEnergy W g ↔ ∃ v ∈ ellipsoid hW, Real.sqrt m ≤ -dot g v := by
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := ellipsoid_support_attained hW g
    refine ⟨-v, ellipsoid_neg_mem hW hv, ?_⟩
    have hd : -dot g (-v) = dot g v := by simp [dot]
    rw [hd, he]
    exact Real.sqrt_le_sqrt h
  · rintro ⟨v, hv, h⟩
    have hb := ellipsoid_abs_support_upper hW g hv
    have hh := h.trans ((neg_le_abs (dot g v)).trans hb)
    have he : 0 ≤ metricEnergy W g := by simpa only [metricEnergy, dot, star_trivial] using hW.2 g
    nlinarith [Real.sq_sqrt hm, Real.sq_sqrt he, Real.sqrt_nonneg m]

/-- Incoming-jump suppression is exactly uniform testing against the
ellipsoid. The nonnegative right side is derived on the forward direction,
so no sign hypothesis on the source suppression constant is hidden. -/
theorem ellipsoid_suppression_iff {n : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (y : Vec n) (b : ℝ) :
    metricEnergy W y ≤ b ↔ 0 ≤ b ∧ ∀ v ∈ ellipsoid hW, |dot y v| ≤ Real.sqrt b := by
  have he : 0 ≤ metricEnergy W y := by simpa only [metricEnergy, dot, star_trivial] using hW.2 y
  constructor
  · intro h
    exact ⟨he.trans h, fun v hv => (ellipsoid_abs_support_upper hW y hv).trans (Real.sqrt_le_sqrt h)⟩
  · rintro ⟨hb, h⟩
    obtain ⟨v, hv, hvEq⟩ := ellipsoid_support_attained hW y
    have hh := h v hv
    rw [hvEq, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    nlinarith [Real.sq_sqrt he, Real.sq_sqrt hb, Real.sqrt_nonneg (metricEnergy W y)]

/-- Support comparison characterizes inclusion of actual matrix images of the
Euclidean ball. The converse uses separation of the compact convex image. -/
theorem matrixBall_subset_iff {n : ℕ} (A B : Mat n) :
    matrixBall A ⊆ matrixBall B ↔
      ∀ a, Real.sqrt (sqNorm (Aᵀ.mulVec a)) ≤ Real.sqrt (sqNorm (Bᵀ.mulVec a)) := by
  constructor
  · intro h a
    obtain ⟨v, hv, he⟩ := matrixBall_support_attained A a
    rw [← he]
    exact matrixBall_support_upper B a (h hv)
  · intro h v hv
    by_contra hn
    obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point
      (matrixBall_convex B) (matrixBall_compact B).isClosed hn
    obtain ⟨a, ha⟩ := linear_functional_eq_dot f.toLinearMap
    change ∀ v, f v = dot a v at ha
    obtain ⟨w, hw, he⟩ := matrixBall_support_attained B a
    have hl := (matrixBall_support_upper A a hv).trans (h a)
    have hh := hf w hw
    rw [ha w, he] at hh
    rw [ha v] at hc
    linarith

theorem matrixBall_image {n : ℕ} (P A : Mat n) :
    P.mulVec '' matrixBall A = matrixBall (P * A) := by
  simp only [matrixBall, Set.image_image, Function.comp_def, Matrix.mulVec_mulVec]

theorem projected_support_energy {n : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (P : Mat n) (a : Vec n) :
    sqNorm ((P * hW.sqrt)ᵀ.mulVec a) = metricEnergy (P * W * Pᵀ) a := by
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, sqrt_support_energy]
  have h := metricEnergy_congruence W Pᵀ a
  simpa only [Matrix.transpose_transpose] using h.symm

/-- Projected ellipsoid inclusion is exactly projected Loewner ordering.
The projection matrix can be arbitrary here, so orthogonal step projectors
are included without imposing a rank or nondegeneracy hypothesis. -/
theorem projected_ellipsoid_subset_iff {n : ℕ} {W Z : Mat n}
    (hW : W.PosSemidef) (hZ : Z.PosSemidef) (P : Mat n) :
    P.mulVec '' ellipsoid hZ ⊆ P.mulVec '' ellipsoid hW ↔
      (P * W * Pᵀ - P * Z * Pᵀ).PosSemidef := by
  change P.mulVec '' matrixBall hZ.sqrt ⊆ P.mulVec '' matrixBall hW.sqrt ↔ _
  rw [matrixBall_image, matrixBall_image, matrixBall_subset_iff]
  simp_rw [projected_support_energy]
  have hw : (P * W * Pᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.mul_mul_conjTranspose_same P
  have hz : (P * Z * Pᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hZ.mul_mul_conjTranspose_same P
  constructor
  · intro h
    refine ⟨hw.isHermitian.sub hz.isHermitian, ?_⟩
    intro a
    have hwa : 0 ≤ metricEnergy (P * W * Pᵀ) a := by simpa [metricEnergy] using hw.2 a
    have hza : 0 ≤ metricEnergy (P * Z * Pᵀ) a := by simpa [metricEnergy] using hz.2 a
    have he := h a
    have hle : metricEnergy (P * Z * Pᵀ) a ≤ metricEnergy (P * W * Pᵀ) a := by
      nlinarith [Real.sq_sqrt hwa, Real.sq_sqrt hza, Real.sqrt_nonneg (metricEnergy (P * Z * Pᵀ) a)]
    simpa [metricEnergy, Matrix.sub_mulVec, dot, dotProduct_sub, sub_nonneg] using hle
  · intro h a
    have he : 0 ≤ metricEnergy (P * W * Pᵀ - P * Z * Pᵀ) a := by
      simpa [metricEnergy] using h.2 a
    rw [EnergyIdentities.energy_sub_matrix] at he
    exact Real.sqrt_le_sqrt (sub_nonneg.mp he)

theorem step_projected_ellipsoid_subset_iff {n : ℕ} {W Z : Mat n}
    (hW : W.PosSemidef) (hZ : Z.PosSemidef) (s : Vec n) :
    (TransportedCertificate.stepProjector s).mulVec '' ellipsoid hZ ⊆
      (TransportedCertificate.stepProjector s).mulVec '' ellipsoid hW ↔
    (TransportedCertificate.stepProjector s * W * TransportedCertificate.stepProjector s -
      TransportedCertificate.stepProjector s * Z * TransportedCertificate.stepProjector s).PosSemidef := by
  simpa only [(TransportedCertificate.stepProjector_isSymm s).eq] using
    projected_ellipsoid_subset_iff hW hZ (TransportedCertificate.stepProjector s)

def matrixRange {n : ℕ} (A : Mat n) : Submodule ℝ (Vec n) := LinearMap.range A.mulVecLin

theorem matrixRange_mul {n : ℕ} (A B : Mat n) :
    matrixRange (A * B) = (matrixRange B).map A.mulVecLin := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨B.mulVec u, ⟨u, rfl⟩, by change A.mulVec (B.mulVec u) = (A * B).mulVec u; rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, by change (A * B).mulVec u = A.mulVec (B.mulVec u); rw [Matrix.mulVec_mulVec]⟩

/-- Finite real Gram matrices have the same actual range as their factor,
including singular and zero factors. -/
theorem matrixRange_mul_transpose {n : ℕ} (A : Mat n) :
    matrixRange (A * Aᵀ) = matrixRange A := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact ⟨Aᵀ.mulVec u, by change A.mulVec (Aᵀ.mulVec u) = (A * Aᵀ).mulVec u; rw [Matrix.mulVec_mulVec]⟩
  · rintro v ⟨u, rfl⟩
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (matrixRange (A * Aᵀ)) _).mp
    intro f hf
    have hfR := ((matrixRange (A * Aᵀ)).mem_dualAnnihilator f).mp hf
    obtain ⟨a, ha⟩ := linear_functional_eq_dot f
    have he : metricEnergy (A * Aᵀ) a = 0 := by
      change dot a ((A * Aᵀ).mulVec a) = 0
      rw [← ha]
      exact hfR _ ⟨a, rfl⟩
    have hg := IncomingJump.metricEnergy_gram Aᵀ a
    rw [Matrix.transpose_transpose] at hg
    have hz : Aᵀ.mulVec a = 0 := (sqNorm_eq_zero_iff _).mp (hg.symm.trans he)
    rw [ha]
    change dot a (A.mulVec u) = 0
    rw [dot_mulVec, hz]
    simp [dot]

theorem matrixRange_sqrt {n : ℕ} {W : Mat n} (hW : W.PosSemidef) :
    matrixRange hW.sqrt = matrixRange W := by
  have hs : hW.sqrtᵀ = hW.sqrt := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.posSemidef_sqrt.isHermitian
  have h := matrixRange_mul_transpose hW.sqrt
  rw [hs, ← pow_two, hW.sq_sqrt] at h
  exact h.symm

/-- The range of the projected PSD matrix is exactly the projection of its
range, the intermediate range identity used in the source proof. -/
theorem projected_matrixRange {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (P : Mat n) :
    matrixRange (P * W * Pᵀ) = (matrixRange W).map P.mulVecLin := by
  have hs : hW.sqrtᵀ = hW.sqrt := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.posSemidef_sqrt.isHermitian
  have he : (P * hW.sqrt) * (P * hW.sqrt)ᵀ = P * W * Pᵀ := by
    rw [Matrix.transpose_mul, hs, Matrix.mul_assoc, ← Matrix.mul_assoc hW.sqrt,
      ← pow_two, hW.sq_sqrt, ← Matrix.mul_assoc]
  rw [← he, matrixRange_mul_transpose, matrixRange_mul, matrixRange_sqrt]

theorem posSemidef_energy_zero_iff {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (a : Vec n) :
    metricEnergy W a = 0 ↔ W.mulVec a = 0 := by
  simpa only [metricEnergy, dot, star_trivial] using hW.dotProduct_mulVec_zero_iff a

theorem stepProjector_fix_of_dot_zero {n : ℕ} (s a : Vec n) (h : dot a s = 0) :
    (TransportedCertificate.stepProjector s).mulVec a = a := by
  have hh : dot s a = 0 := (dotProduct_comm s a).trans h
  simp [TransportedCertificate.stepProjector, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    outer_mulVec, hh]

/-- The source necessary rank/range condition follows directly from the
projected PSD order, including singular matrices and zero steps. -/
theorem range_le_sup_span_of_projected_order {n : ℕ} {W Z : Mat n}
    (hW : W.PosSemidef) (hZ : Z.PosSemidef) (s : Vec n)
    (hT : (TransportedCertificate.stepProjector s * W * TransportedCertificate.stepProjector s -
      TransportedCertificate.stepProjector s * Z * TransportedCertificate.stepProjector s).PosSemidef) :
    matrixRange Z ≤ matrixRange W ⊔ Submodule.span ℝ {s} := by
  let S := matrixRange W ⊔ Submodule.span ℝ {s}
  rintro v ⟨u, rfl⟩
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S (Z.mulVec u)).mp
  intro f hf
  have hfS : ∀ w ∈ S, f w = 0 := (S.mem_dualAnnihilator f).mp hf
  obtain ⟨a, ha⟩ := linear_functional_eq_dot f
  have hsa : dot a s = 0 := by
    rw [← ha]
    apply hfS
    exact (show Submodule.span ℝ {s} ≤ S from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton s))
  have heW : metricEnergy W a = 0 := by
    change dot a (W.mulVec a) = 0
    rw [← ha]
    exact hfS _ ((show matrixRange W ≤ S from le_sup_left) ⟨a, rfl⟩)
  have hP := stepProjector_fix_of_dot_zero s a hsa
  have he (M : Mat n) :
      metricEnergy (TransportedCertificate.stepProjector s * M * TransportedCertificate.stepProjector s) a =
        metricEnergy M a := by
    have hc := metricEnergy_congruence M (TransportedCertificate.stepProjector s) a
    rw [(TransportedCertificate.stepProjector_isSymm s).eq, hP] at hc
    exact hc
  have ht : 0 ≤ metricEnergy
      (TransportedCertificate.stepProjector s * W * TransportedCertificate.stepProjector s -
        TransportedCertificate.stepProjector s * Z * TransportedCertificate.stepProjector s) a := by
    simpa only [metricEnergy, dot, star_trivial] using hT.2 a
  rw [EnergyIdentities.energy_sub_matrix, he W, he Z, heW] at ht
  have hz : 0 ≤ metricEnergy Z a := by simpa only [metricEnergy, dot, star_trivial] using hZ.2 a
  have hZa : Z.mulVec a = 0 := (posSemidef_energy_zero_iff hZ a).mp (by linarith)
  have hs : Zᵀ = Z := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hZ.isHermitian
  rw [ha, dot_mulVec, hs, hZa]
  simp [dot]

theorem vector_mem_own_outer_range {n : ℕ} (v : Vec n) : v ∈ matrixRange (outer v v) := by
  by_cases hv : v = 0
  · subst v
    exact ⟨0, by simp [outer, Matrix.mulVec, dotProduct]⟩
  have hq : sqNorm v ≠ 0 := fun h => hv ((sqNorm_eq_zero_iff v).mp h)
  refine ⟨(sqNorm v)⁻¹ • v, ?_⟩
  change (outer v v).mulVec ((sqNorm v)⁻¹ • v) = v
  rw [outer_mulVec, dot_smul_right, dot_self, inv_mul_cancel₀ hq, one_smul]

/-- In the rank-one case the new comparison direction lies in the plane
spanned by the previous direction and the executed step, exactly as in G.2. -/
theorem rankOne_direction_mem_plane {n : ℕ} (w v s : Vec n)
    (hT : (TransportedCertificate.stepProjector s * outer w w * TransportedCertificate.stepProjector s -
      TransportedCertificate.stepProjector s * outer v v * TransportedCertificate.stepProjector s).PosSemidef) :
    v ∈ Submodule.span ℝ ({w, s} : Set (Vec n)) := by
  have hW : (outer w w).PosSemidef := by
    simpa only [one_smul] using SmoothSubspace.scaled_outer_posSemidef w 1 zero_le_one
  have hZ : (outer v v).PosSemidef := by
    simpa only [one_smul] using SmoothSubspace.scaled_outer_posSemidef v 1 zero_le_one
  have hv := range_le_sup_span_of_projected_order hW hZ s hT (vector_mem_own_outer_range v)
  apply (show matrixRange (outer w w) ⊔ Submodule.span ℝ {s} ≤
      Submodule.span ℝ ({w, s} : Set (Vec n)) from ?_) hv
  apply sup_le
  · rintro z ⟨u, rfl⟩
    change (outer w w).mulVec u ∈ _
    rw [outer_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert w {s}))
  · exact Submodule.span_mono (by intro z hz; simp only [Set.mem_singleton_iff] at hz; subst z; simp)

end BfgsVerification.CertificateGeometry
