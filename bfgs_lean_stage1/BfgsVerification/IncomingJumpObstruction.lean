import BfgsVerification.TransportedCertificateAlgebra
import BfgsVerification.FrameNorms
import BfgsVerification.CompactConvergence

/-! Module G's finite common-target incoming-jump obstruction. The PSD value
at the target may vary without any boundedness or continuity hypothesis. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification.IncomingJump

theorem metricEnergy_gram {n : ℕ} (A : Mat n) (v : Vec n) :
    metricEnergy (Aᵀ * A) v = sqNorm (A.mulVec v) := by
  have h := metricEnergy_congruence (1 : Mat n) A v
  simpa only [Matrix.mul_one, metricEnergy, Matrix.one_mulVec, dot, sqNorm, pow_two] using h

theorem sqrt_metricEnergy_gram {n : ℕ} (A : Mat n) (v : Vec n) :
    Real.sqrt (metricEnergy (Aᵀ * A) v) =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (euclideanVector v)‖ := by
  rw [metricEnergy_gram]
  have h := FrameNorms.euclidean_norm_sq (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (euclideanVector v))
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (euclideanVector v)‖ ^ 2 = sqNorm (A.mulVec v) at h
  rw [← h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The seminorm triangle inequality for a finite linear combination under an
actual PSD matrix, including singular matrices and an empty family. -/
theorem sqrt_metricEnergy_sum_le {n r : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (coeff : Fin r → ℝ) (y : Fin r → Vec n) :
    Real.sqrt (metricEnergy W (∑ j, coeff j • y j)) ≤
      ∑ j, |coeff j| * Real.sqrt (metricEnergy W (y j)) := by
  obtain ⟨A, hA⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hW
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hA
  rw [hA]
  simp only [sqrt_metricEnergy_gram]
  have he : euclideanVector (∑ j, coeff j • y j) =
      ∑ j, coeff j • euclideanVector (y j) := by
    change (WithLp.linearEquiv 2 ℝ (Vec n)).symm (∑ j, coeff j • y j) = _
    simp only [map_sum, map_smul]
    rfl
  rw [he, map_sum]
  calc
    _ ≤ ∑ j, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (coeff j • euclideanVector (y j))‖ := norm_sum_le _ _
    _ = _ := by simp only [map_smul, norm_smul, Real.norm_eq_abs]

/-- Source weighted finite-jump bound, with the suppression constant's sign
handled by `max C 0`; no sign premise on C is added. -/
theorem weighted_jump_bound {n r : ℕ} {W : Mat n} (hW : W.PosSemidef)
    (coeff : Fin r → ℝ) (y : Fin r → Vec n) (t : Fin r → ℝ) (C : ℝ)
    (ht : ∀ j, 0 ≤ t j) (hS : ∀ j, metricEnergy W (y j) ≤ C * t j) :
    Real.sqrt (metricEnergy W (∑ j, coeff j • y j)) ≤
      Real.sqrt (max C 0) * ∑ j, |coeff j| * Real.sqrt (t j) := by
  calc
    _ ≤ ∑ j, |coeff j| * Real.sqrt (metricEnergy W (y j)) :=
      sqrt_metricEnergy_sum_le hW coeff y
    _ ≤ ∑ j, |coeff j| * (Real.sqrt (max C 0) * Real.sqrt (t j)) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [← Real.sqrt_mul (le_max_right C 0)]
      exact Real.sqrt_le_sqrt ((hS j).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (ht j)))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

/-- Abstract common-target obstruction for any nontrivial limiting filter.
All matrices are actual finite PSD matrices; they may vary without bounds. -/
theorem no_visible_suppression {ι : Type*} {l : Filter ι} [NeBot l]
    {n r : ℕ} (W : ι → Mat n) (h : ι → Vec n)
    (y : ι → Fin r → Vec n) (t coeff : ι → Fin r → ℝ) (m C : ℝ)
    (hm : 0 < m) (hW : ∀ᶠ a in l, (W a).PosSemidef)
    (hV : ∀ᶠ a in l, m ≤ metricEnergy (W a) (h a))
    (ht : ∀ᶠ a in l, ∀ j, 0 ≤ t a j)
    (hS : ∀ᶠ a in l, ∀ j, metricEnergy (W a) (y a j) ≤ C * t a j)
    (hrep : ∀ᶠ a in l, h a = ∑ j, coeff a j • y a j)
    (hcost : Tendsto (fun a => ∑ j, |coeff a j| * Real.sqrt (t a j)) l (𝓝 0)) : False := by
  have hlim : Tendsto (fun a => Real.sqrt (max C 0) *
      ∑ j, |coeff a j| * Real.sqrt (t a j)) l (𝓝 0) := by
    simpa using hcost.const_mul (Real.sqrt (max C 0))
  have hlower : ∀ᶠ a in l, Real.sqrt m ≤ Real.sqrt (max C 0) *
      ∑ j, |coeff a j| * Real.sqrt (t a j) := by
    filter_upwards [hW, hV, ht, hS, hrep] with a ha hv ht hs hr
    calc
      _ ≤ Real.sqrt (metricEnergy (W a) (h a)) := Real.sqrt_le_sqrt hv
      _ = Real.sqrt (metricEnergy (W a) (∑ j, coeff a j • y a j)) := by rw [hr]
      _ ≤ _ := weighted_jump_bound ha (coeff a) (y a) (t a) C ht hs
  have hzero : Real.sqrt m ≤ 0 := ge_of_tendsto hlim hlower
  exact (Real.sqrt_pos.2 hm).not_le hzero

/-- A family of columns converging to an invertible matrix represents every
bounded target with bounded coefficients on a tail. Vanishing curvature then
gives the source's vanishing weighted incoming-jump cost. -/
theorem basis_limit_coefficients {ι : Type*} {l : Filter ι}
    {n : ℕ} (Y : ι → Mat n) (Y₀ : Mat n) (hY : Tendsto Y l (𝓝 Y₀))
    (hdet : Y₀.det ≠ 0) (h : ι → Vec n) (B : ℝ)
    (hB : ∀ᶠ a in l, ‖h a‖ ≤ B) (t : ι → Fin n → ℝ)
    (ht : ∀ j, Tendsto (fun a => t a j) l (𝓝 0)) :
    ∃ coeff : ι → Fin n → ℝ,
      (∀ᶠ a in l, h a = ∑ j, coeff a j • (fun i => Y a i j)) ∧
      Tendsto (fun a => ∑ j, |coeff a j| * Real.sqrt (t a j)) l (𝓝 0) := by
  let coeff : ι → Fin n → ℝ := fun a => (Y a)⁻¹.mulVec (h a)
  have hInv : Tendsto (fun a => (Y a)⁻¹) l (𝓝 Y₀⁻¹) := by
    apply (continuousAt_matrix_inv Y₀ ?_).tendsto.comp hY
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have hunit : ∀ᶠ a in l, IsUnit (Y a).det := by
    have hdlim := (continuous_id.matrix_det.continuousAt.tendsto).comp hY
    exact (hdlim.eventually (isOpen_ne.mem_nhds hdet)).mono (fun _ ha => isUnit_iff_ne_zero.mpr ha)
  refine ⟨coeff, ?_, ?_⟩
  · filter_upwards [hunit] with a ha
    have he : (Y a).mulVec (coeff a) = h a := by
      change (Y a).mulVec ((Y a)⁻¹.mulVec (h a)) = h a
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ha, Matrix.one_mulVec]
    rw [← he]
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have hterm : ∀ j, Tendsto (fun a => |coeff a j| * Real.sqrt (t a j)) l (𝓝 0) := by
      intro j
      let D : ℝ := ∑ i, (|Y₀⁻¹ j i| + 1) * max B 0
      have hinvbound : ∀ᶠ a in l, ∀ i, |(Y a)⁻¹ j i| ≤ |Y₀⁻¹ j i| + 1 := by
        apply eventually_all.mpr
        intro i
        have hi := ((hInv.apply_nhds j).apply_nhds i).abs
        exact (hi.eventually (eventually_lt_nhds (lt_add_one _))).mono (fun _ ha => ha.le)
      have hc : ∀ᶠ a in l, |coeff a j| ≤ D := by
        filter_upwards [hinvbound, hB] with a ha hb
        calc
          |coeff a j| = |∑ i, (Y a)⁻¹ j i * h a i| := rfl
          _ ≤ ∑ i, |(Y a)⁻¹ j i * h a i| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ D := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            apply mul_le_mul (ha i) _ (abs_nonneg _) (by positivity)
            exact ((show |h a i| ≤ ‖h a‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (h a) i).trans hb).trans (le_max_left B 0)
      apply squeeze_zero' (Eventually.of_forall (fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))
        (hc.mono (fun a ha => mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)))
      simpa only [Real.sqrt_zero, mul_zero] using ((ht j).sqrt.const_mul D)
    simpa using tendsto_finset_sum Finset.univ (fun j _ => hterm j)

end BfgsVerification.IncomingJump

namespace BfgsVerification.TransportedCertificate

/-- Only source conditions (V) and (S), without any transport condition. -/
structure VisibilitySecantCertificate {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ η : ℝ) where
  W : Vec n → Mat n
  m : ℝ
  C : ℝ
  δ : ℝ
  m_pos : 0 < m
  delta_pos : 0 < δ
  positive_semidefinite : ∀ x ∈ positiveBand F K fstar η,
    DifferentiableAt ℝ F x → (W x).PosSemidef
  visibility : ∀ x ∈ positiveBand F K fstar η, ∀ g,
    HasFDerivAt F (gradientFunctional g) x → m ≤ metricEnergy (W x) g
  secant : ∀ x z g h,
    x ∈ positiveBand F K fstar η → z ∈ positiveBand F K fstar η →
    EligiblePair F c₁ c₂ x z g h → pairDecrease x z g ≤ δ →
    metricEnergy (W z) (h - g) ≤ C * pairCurvature x z g h

/-- Forget transport without changing the field, domain, or pair threshold. -/
def BandCertificate.toVisibilitySecant {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (B : BandCertificate F K fstar c₁ c₂ η) :
    VisibilitySecantCertificate F K fstar c₁ c₂ η where
  W := B.W
  m := B.m
  C := B.C
  δ := B.δ
  m_pos := B.m_pos
  delta_pos := B.delta_pos
  positive_semidefinite := B.positive_semidefinite
  visibility := B.visibility
  secant := B.secant

/-- Module G's incoming-jump obstruction for actual differentiable objective
pairs in one fixed band. Transport is not used. The pairs share the target z,
and no common accepted-iterate history is required. -/
theorem incoming_jump_no_visibility_secant {ι : Type*} {l : Filter ι} [NeBot l]
    {n r : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (z h : ι → Vec n) (x g : ι → Fin r → Vec n)
    (coeff : ι → Fin r → ℝ)
    (hz : ∀ a, z a ∈ positiveBand F K fstar η)
    (hx : ∀ a j, x a j ∈ positiveBand F K fstar η)
    (hdiff : ∀ a, HasFDerivAt F (gradientFunctional (h a)) (z a))
    (hp : ∀ a j, EligiblePair F c₁ c₂ (x a j) (z a) (g a j) (h a))
    (hd : ∀ j, Tendsto (fun a => pairDecrease (x a j) (z a) (g a j)) l (𝓝 0))
    (hrep : ∀ᶠ a in l, h a = ∑ j, coeff a j • (h a - g a j))
    (hcost : Tendsto (fun a => ∑ j, |coeff a j| *
      Real.sqrt (pairCurvature (x a j) (z a) (g a j) (h a))) l (𝓝 0)) :
    ¬ Nonempty (VisibilitySecantCertificate F K fstar c₁ c₂ η) := by
  rintro ⟨B⟩
  have hsmall : ∀ᶠ a in l, ∀ j, pairDecrease (x a j) (z a) (g a j) ≤ B.δ := by
    apply eventually_all.mpr
    intro j
    exact ((hd j).eventually (eventually_lt_nhds B.delta_pos)).mono (fun _ h => h.le)
  apply IncomingJump.no_visible_suppression (l := l) (fun a => B.W (z a)) h
    (fun a j => h a - g a j)
    (fun a j => pairCurvature (x a j) (z a) (g a j) (h a)) coeff B.m B.C B.m_pos
  · exact Eventually.of_forall (fun a => B.positive_semidefinite (z a) (hz a) (hdiff a).differentiableAt)
  · exact Eventually.of_forall (fun a => B.visibility (z a) (hz a) (h a) (hdiff a))
  · exact Eventually.of_forall (fun a j => (mul_pos (sub_pos.mpr hc₂) (hp a j).decrease_pos).le.trans (hp a j).curvature)
  · exact hsmall.mono (fun a ha j => B.secant (x a j) (z a) (g a j) (h a)
      (hx a j) (hz a) (hp a j) (ha j))
  · exact hrep
  · exact hcost

/-- Module G's incoming-jump obstruction for actual differentiable objective
pairs in one fixed band. Transport is not used. The pairs share the target z,
and no common accepted-iterate history is required. -/
theorem incoming_jump_no_band_certificate {ι : Type*} {l : Filter ι} [NeBot l]
    {n r : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (z h : ι → Vec n) (x g : ι → Fin r → Vec n)
    (coeff : ι → Fin r → ℝ)
    (hz : ∀ a, z a ∈ positiveBand F K fstar η)
    (hx : ∀ a j, x a j ∈ positiveBand F K fstar η)
    (hdiff : ∀ a, HasFDerivAt F (gradientFunctional (h a)) (z a))
    (hp : ∀ a j, EligiblePair F c₁ c₂ (x a j) (z a) (g a j) (h a))
    (hd : ∀ j, Tendsto (fun a => pairDecrease (x a j) (z a) (g a j)) l (𝓝 0))
    (hrep : ∀ᶠ a in l, h a = ∑ j, coeff a j • (h a - g a j))
    (hcost : Tendsto (fun a => ∑ j, |coeff a j| *
      Real.sqrt (pairCurvature (x a j) (z a) (g a j) (h a))) l (𝓝 0)) :
    ¬ Nonempty (BandCertificate F K fstar c₁ c₂ η) := by
  rintro ⟨B⟩
  exact incoming_jump_no_visibility_secant (l := l) hc₂ z h x g coeff hz hx hdiff hp hd hrep hcost
    ⟨B.toVisibilitySecant⟩

/-- Source basis-limit corollary: the n actual incoming jumps converge to a
basis, their curvatures vanish, and the common-target gradients are bounded.
No convergence of those target gradients is required. -/
theorem basis_limit_no_visibility_secant {ι : Type*} {l : Filter ι} [NeBot l]
    {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (z h : ι → Vec n) (x g : ι → Fin n → Vec n)
    (hz : ∀ a, z a ∈ positiveBand F K fstar η)
    (hx : ∀ a j, x a j ∈ positiveBand F K fstar η)
    (hdiff : ∀ a, HasFDerivAt F (gradientFunctional (h a)) (z a))
    (hp : ∀ a j, EligiblePair F c₁ c₂ (x a j) (z a) (g a j) (h a))
    (hd : ∀ j, Tendsto (fun a => pairDecrease (x a j) (z a) (g a j)) l (𝓝 0))
    (b : Basis (Fin n) ℝ (Vec n))
    (hy : ∀ j, Tendsto (fun a => h a - g a j) l (𝓝 (b j)))
    (ht : ∀ j, Tendsto (fun a => pairCurvature (x a j) (z a) (g a j) (h a)) l (𝓝 0))
    (B : ℝ) (hB : ∀ᶠ a in l, ‖h a‖ ≤ B) :
    ¬ Nonempty (VisibilitySecantCertificate F K fstar c₁ c₂ η) := by
  let Y : ι → Mat n := fun a i j => (h a - g a j) i
  let Y₀ : Mat n := fun i j => b j i
  have hY : Tendsto Y l (𝓝 Y₀) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (hy j).apply_nhds i
  have hdet : Y₀.det ≠ 0 := by
    have hunit := (Pi.basisFun ℝ (Fin n)).isUnit_det b
    simpa only [Basis.det_apply, Basis.toMatrix_apply, Pi.basisFun_repr] using hunit.ne_zero
  obtain ⟨coeff, hrep, hcost⟩ := IncomingJump.basis_limit_coefficients Y Y₀ hY hdet h B hB
    (fun a j => pairCurvature (x a j) (z a) (g a j) (h a)) ht
  exact incoming_jump_no_visibility_secant (l := l) hc₂ z h x g coeff hz hx hdiff hp hd hrep hcost

/-- The basis-limit obstruction excludes the full transported certificate. -/
theorem basis_limit_no_band_certificate {ι : Type*} {l : Filter ι} [NeBot l]
    {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (z h : ι → Vec n) (x g : ι → Fin n → Vec n)
    (hz : ∀ a, z a ∈ positiveBand F K fstar η)
    (hx : ∀ a j, x a j ∈ positiveBand F K fstar η)
    (hdiff : ∀ a, HasFDerivAt F (gradientFunctional (h a)) (z a))
    (hp : ∀ a j, EligiblePair F c₁ c₂ (x a j) (z a) (g a j) (h a))
    (hd : ∀ j, Tendsto (fun a => pairDecrease (x a j) (z a) (g a j)) l (𝓝 0))
    (b : Basis (Fin n) ℝ (Vec n))
    (hy : ∀ j, Tendsto (fun a => h a - g a j) l (𝓝 (b j)))
    (ht : ∀ j, Tendsto (fun a => pairCurvature (x a j) (z a) (g a j) (h a)) l (𝓝 0))
    (B : ℝ) (hB : ∀ᶠ a in l, ‖h a‖ ≤ B) :
    ¬ Nonempty (BandCertificate F K fstar c₁ c₂ η) := by
  rintro ⟨C⟩
  exact basis_limit_no_visibility_secant (l := l) hc₂ z h x g hz hx hdiff hp hd b hy ht B hB
    ⟨C.toVisibilitySecant⟩

end BfgsVerification.TransportedCertificate
