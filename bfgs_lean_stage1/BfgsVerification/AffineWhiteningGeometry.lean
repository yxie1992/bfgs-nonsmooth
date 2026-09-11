import BfgsVerification.SpectralMetricBounds

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection EnergyIdentities
variable {n : ℕ}

theorem min_sub_posSemidef [NeZero n] (H : Mat n) (hH : H.PosDef) :
    (H-minEigenvalue H hH.1 • (1 : Mat n)).PosSemidef := by
  have hM := TransportedCertificate.psd_smul (Matrix.PosDef.one : (1 : Mat n).PosDef).posSemidef
    (minEigenvalue_pos H hH).le
  refine ⟨hH.1.sub hM.1,?_⟩
  intro x
  have hl := (actual_extreme_metric_bounds H hH.1 x).1
  simpa [metricEnergy,Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,
    dot,dotProduct_sub,dotProduct_smul,sqNorm,pow_two,sub_nonneg] using hl

theorem strongConvex_whitening [NeZero n] (H : Mat n) (hH : H.PosDef)
    {F : Vec n → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hF : FixedNormal.EuclideanStrongConvexOn univ μ F) :
    FixedNormal.EuclideanStrongConvexOn univ (μ*minEigenvalue H hH.1)
      (objective (squareRoot H hH) F) := by
  let A := squareRoot H hH
  let m := minEigenvalue H hH.1
  have hc : ConvexOn ℝ univ (fun x => F (A.mulVec x)-μ/2*sqNorm (A.mulVec x)) := by
    simpa only [preimage_univ,Function.comp_def] using hF.comp_linearMap A.mulVecLin
  have hq := (QuadraticGauge.quadratic_convex (H-m • (1 : Mat n)) (min_sub_posSemidef H hH)).smul hμ
  apply (hc.add hq).congr
  intro x _
  change F (A.mulVec x)-μ/2*sqNorm (A.mulVec x)+μ*(metricEnergy (H-m • (1 : Mat n)) x/2)=
    F (A.mulVec x)-(μ*m)/2*sqNorm x
  rw [squareRoot_sqNorm,energy_sub_matrix,energy_smul_matrix]
  have he : metricEnergy (1 : Mat n) x=sqNorm x := by simp [metricEnergy,Matrix.one_mulVec,dot,sqNorm,pow_two]
  rw [he]
  ring

/-- The actual Euclidean gradient bound transforms with L times the largest
actual eigenvalue of the one initial SPD matrix. -/
theorem gradient_bound_whitening [NeZero n] (H : Mat n) (hH : H.PosDef)
    (g : Vec n → Vec n) (L : ℝ)
    (hg : ∀x y,sqNorm (g x-g y) ≤ L^2*sqNorm (x-y)) (x y : Vec n) :
    sqNorm (gradient (squareRoot H hH) (g ((squareRoot H hH).mulVec x))-
      gradient (squareRoot H hH) (g ((squareRoot H hH).mulVec y))) ≤
      (L*maxEigenvalue H hH.1)^2*sqNorm (x-y) := by
  let A := squareRoot H hH
  let M := maxEigenvalue H hH.1
  have hM : 0 ≤ M := (maxEigenvalue_pos H hH).le
  change sqNorm (Aᵀ.mulVec (g (A.mulVec x))-Aᵀ.mulVec (g (A.mulVec y))) ≤ _
  rw [← Matrix.mulVec_sub,squareRoot_transpose]
  have h1 := (squareRoot_norm_bounds H hH (g (A.mulVec x)-g (A.mulVec y))).2
  have h2 := mul_le_mul_of_nonneg_left (hg (A.mulVec x) (A.mulVec y)) hM
  have h3 := mul_le_mul_of_nonneg_left (squareRoot_norm_bounds H hH (x-y)).2
    (mul_nonneg hM (sq_nonneg L))
  rw [Matrix.mulVec_sub] at h3
  calc
    sqNorm (A.mulVec (g (A.mulVec x)-g (A.mulVec y))) ≤ M*sqNorm (g (A.mulVec x)-g (A.mulVec y)) := h1
    _ ≤ M*(L^2*sqNorm (A.mulVec x-A.mulVec y)) := h2
    _ ≤ (L*M)^2*sqNorm (x-y) := by nlinarith [h3]

theorem contDiff_whitening (A : Mat n) {F : Vec n → ℝ} {k : WithTop ℕ∞}
    (hF : ContDiff ℝ k F) : ContDiff ℝ k (objective A F) :=
  hF.comp (matrixCLM A).contDiff

theorem sublevels_compact_whitening (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (hF : ∀a,IsCompact {x | F x ≤ a}) (a : ℝ) :
    IsCompact {x | objective A F x ≤ a} := by
  exact (linearEquiv A hA).toHomeomorph.isCompact_preimage.mpr (hF a)

theorem zero_unique_whitening (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (hF : ∀x,F x=0 → x=0) {x : Vec n} (hx : objective A F x=0) : x=0 := by
  have h := hF (A.mulVec x) hx
  have hh := congrArg (point A) h
  rw [point_map A hA] at hh
  simpa only [point,Matrix.mulVec_zero] using hh

theorem nonstationary_whitening (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ} (p : Vec n)
    (hp : (0 : Vec n)∉ConvexSubdifferential.subdifferential F p) :
    (0 : Vec n)∉ConvexSubdifferential.subdifferential (objective A F) (point A p) := by
  intro hh
  apply hp
  apply ConvexSubdifferential.zero_mem_iff_global_minimum.mpr
  intro x
  have h := ConvexSubdifferential.zero_mem_iff_global_minimum.mp hh (point A x)
  simpa only [objective,map_point A hA] using h

theorem coercive_of_compact_sublevels {F : Vec n → ℝ}
    (hF : ∀a,IsCompact {x | F x ≤ a}) : Tendsto F (cocompact (Vec n)) atTop := by
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [(hF a).compl_mem_cocompact] with x hx
  change ¬F x ≤ a at hx
  exact (not_le.mp hx).le

end BfgsVerification.AffineWhitening
