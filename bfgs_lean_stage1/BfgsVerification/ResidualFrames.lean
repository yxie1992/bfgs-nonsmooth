import BfgsVerification.SmoothSubspace
import BfgsVerification.FrameBounds
import BfgsVerification.ResidualBudget
import BfgsVerification.RunShift

/-! Module M's imperfect-transport contradiction for actual full-BFGS matrices.
The fixed subspace is represented by an orthonormal basis U; residual columns
are fixed by its actual orthogonal projection. No frame rank is required. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem frame_descent_nonneg {p : ℕ} (k : ℕ) (V : Matrix (Fin n) (Fin p) ℝ)
    (m : ℝ) (ha : m ≤ sqNorm (Vᵀ.mulVec (R.g k))) :
    0 ≤ (metricGram (R.hessian k) V).trace - m / R.q k := by
  have hn := FrameBounds.gram_trace_nonneg (R.annihilated_hessian_posSemidef k) V
  rw [EnergyIdentities.gram_sub, EnergyIdentities.gram_smul,
    EnergyIdentities.gram_outer, Matrix.trace_sub, Matrix.trace_smul,
    FrameBounds.trace_outer] at hn
  have hdiv := div_le_div_of_nonneg_right ha (R.q_pos k).le
  simp only [smul_eq_mul, div_eq_mul_inv] at hn hdiv ⊢
  nlinarith

/-- Young's inequality and the derived smooth-subspace budget supply the
one-step residual estimate for the actual frame energy. -/
theorem residual_frame_step {r p : ℕ} (k : ℕ)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (L : ℝ) (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec (R.gradientChange k)) ≤ L * R.curvature k)
    (V W Z : Matrix (Fin n) (Fin p) ℝ) (T : Mat p) (b : Vec p)
    (m C₀ C_T C_R : ℝ) (hCT : 0 ≤ C_T)
    (hpair : m ≤ sqNorm (Vᵀ.mulVec (R.g k)))
    (hchange : sqNorm (Wᵀ.mulVec (R.gradientChange k)) ≤ C₀ * R.curvature k)
    (htransport : W = V * T + EnergyIdentities.rectOuter (R.displacement k) b + Z)
    (hT : FrameBounds.OperatorSqBound T (1 + C_T * R.d k))
    (hZ : (U * Uᵀ) * Z = Z) (hsize : SmoothSubspace.frobSq Z ≤ C_R * R.d k) :
    (metricGram (R.hessian (k + 1)) W).trace ≤
      (1 + R.d k) * (1 + C_T * R.d k) *
        ((metricGram (R.hessian k) V).trace - m / R.q k) +
      (1 + (R.d k)⁻¹) * (C_R * R.d k *
        ((metricGram (R.hessian 0) U).trace + L * (k : ℝ))) + C₀ := by
  let M := R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)
  have hd : 0 < R.d k := R.d_pos k
  have hM : M.PosSemidef := R.annihilated_hessian_posSemidef k
  have hremove : metricGram M W = metricGram M (V * T + Z) := by
    have hw : W = (V * T + Z) + EnergyIdentities.rectOuter (R.displacement k) b := by
      rw [htransport]
      abel
    rw [hw]
    exact EnergyIdentities.gram_add_kernel (R.annihilated_hessian_isSymm k)
      (R.annihilated_hessian_mul_displacement k) _ b
  have hexact : (metricGram (R.hessian (k + 1)) W).trace =
      (metricGram M (V * T + Z)).trace +
      sqNorm (Wᵀ.mulVec (R.gradientChange k)) / R.curvature k := by
    rw [R.hessian_update, EnergyIdentities.gram_add, EnergyIdentities.gram_smul,
      EnergyIdentities.gram_outer, Matrix.trace_add, Matrix.trace_smul,
      FrameBounds.trace_outer]
    change (metricGram M W).trace + _ = _
    rw [hremove]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbase : (metricGram M V).trace ≤ (metricGram (R.hessian k) V).trace - m / R.q k := by
    dsimp only [M]
    rw [EnergyIdentities.gram_sub, EnergyIdentities.gram_smul,
      EnergyIdentities.gram_outer, Matrix.trace_sub, Matrix.trace_smul, FrameBounds.trace_outer]
    have hd := div_le_div_of_nonneg_right hpair (R.q_pos k).le
    simp only [smul_eq_mul, div_eq_mul_inv] at hd ⊢
    linarith
  have htrans := (FrameBounds.gram_trace_transport_le hM V T _ hT).trans
    (mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 1 + C_T * R.d k))
  have hyoung := FrameBounds.gram_trace_add_le hM (V * T) Z (R.d k) (R.d_pos k)
  have hres := R.smooth_subspace_residual_budget U hU L hsmooth C_R k Z hZ hsize
  have hcorr : sqNorm (Wᵀ.mulVec (R.gradientChange k)) / R.curvature k ≤ C₀ :=
    (div_le_iff₀ (R.curvature_pos k)).mpr hchange
  have h1 := mul_le_mul_of_nonneg_left htrans (by linarith [R.d_pos k] : 0 ≤ 1 + R.d k)
  have h2 := mul_le_mul_of_nonneg_left hres (by positivity : 0 ≤ 1 + (R.d k)⁻¹)
  rw [hexact]
  dsimp only [M] at hyoung h1
  nlinarith

/-- Full matrix/sequence residual contradiction. Nonnegative budget constants
can always be enlarged, and are not extra regularity assumptions. -/
theorem residual_frames_incompatible {r p : ℕ}
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hs : Summable R.d) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (L m C₀ C_T C_R : ℝ) (hL : 0 ≤ L) (hm : 0 < m)
    (hC₀ : 0 ≤ C₀) (hCT : 0 ≤ C_T) (hCR : 0 ≤ C_R)
    (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec (R.gradientChange k)) ≤ L * R.curvature k)
    (V Z : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (hpair : ∀ k, m ≤ sqNorm ((V k)ᵀ.mulVec (R.g k)))
    (hchange : ∀ k, sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k)) ≤ C₀ * R.curvature k)
    (htransport : ∀ k, V (k + 1) = V k * T k +
      EnergyIdentities.rectOuter (R.displacement k) (b k) + Z k)
    (hT : ∀ k, FrameBounds.OperatorSqBound (T k) (1 + C_T * R.d k))
    (hZ : ∀ k, (U * Uᵀ) * Z k = Z k)
    (hsize : ∀ k, SmoothSubspace.frobSq (Z k) ≤ C_R * R.d k) : False := by
  let D := ∑' k, R.d k
  let S := (metricGram (R.hessian 0) U).trace
  let A := 1 + C_T + C_T * D
  let C := C_R * (1 + D) * (S + L) + C₀
  let E := fun k => (metricGram (R.hessian k) (V k)).trace
  have hdD : ∀ k, R.d k ≤ D := by
    intro k
    simpa only [Finset.sum_singleton] using hs.sum_le_tsum {k} (fun i _ => (R.d_pos i).le)
  have hD : 0 ≤ D := (R.d_pos 0).le.trans (hdD 0)
  have hS : 0 ≤ S := FrameBounds.gram_trace_nonneg (R.hessian_posDef 0).posSemidef U
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE : ∀ k, 0 ≤ E k := fun k =>
    FrameBounds.gram_trace_nonneg (R.hessian_posDef k).posSemidef (V k)
  have hrec : ∀ k, E (k + 1) ≤ (1 + A * R.d k) * (E k - m / R.q k) + C * (k + 1) := by
    intro k
    have hstep := R.residual_frame_step k U hU L hsmooth (V k) (V (k + 1))
      (Z k) (T k) (b k) m C₀ C_T C_R hCT (hpair k) (hchange k)
      (htransport k) (hT k) (hZ k) (hsize k)
    have hbase := R.frame_descent_nonneg k (V k) m (hpair k)
    have hfactor : (1 + R.d k) * (1 + C_T * R.d k) ≤ 1 + A * R.d k := by
      have h := mul_le_mul_of_nonneg_left (hdD k) (mul_nonneg hCT (R.d_pos k).le)
      dsimp only [A]
      nlinarith
    have hmain := mul_le_mul_of_nonneg_right hfactor hbase
    have hlinear : S + L * (k : ℝ) ≤ (S + L) * ((k : ℝ) + 1) := by
      nlinarith [mul_nonneg hS (Nat.cast_nonneg k)]
    have hres : (1 + (R.d k)⁻¹) * (C_R * R.d k * (S + L * (k : ℝ))) ≤
        C_R * (1 + D) * (S + L) * ((k : ℝ) + 1) := by
      calc
        _ = C_R * (1 + R.d k) * (S + L * (k : ℝ)) := by
          field_simp [(R.d_pos k).ne']
          ring
        _ ≤ C_R * (1 + D) * (S + L * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (add_le_add_left (hdD k) 1) hCR) (by positivity)
        _ ≤ C_R * (1 + D) * ((S + L) * ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hlinear (by positivity)
        _ = _ := by ring
    have hc0 : C₀ ≤ C₀ * ((k : ℝ) + 1) := by nlinarith [mul_nonneg hC₀ (Nat.cast_nonneg k)]
    dsimp only [E, C, S] at hstep hbase hmain hres hc0 ⊢
    nlinarith
  have hsuper := superquadraticReciprocalGrowth n R.toFullBFGSRun G (1 - R.c₂)
    hG R.wolfe_constant_pos hg R.beta_lower_bound hs
  exact ResidualBudget.residual_recurrence_incompatible hE R.q_pos
    (fun k => mul_nonneg hA (R.d_pos k).le) (hs.mul_left A) hm hC hrec hsuper

/-- The source's arbitrary-tail version uses the actual shifted run and its
derived initial SPD, never a hypothesis about later BFGS matrices. -/
theorem residual_frames_on_tail_incompatible {r p : ℕ} (J : ℕ)
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hs : Summable R.d) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (L m C₀ C_T C_R : ℝ) (hL : 0 ≤ L) (hm : 0 < m)
    (hC₀ : 0 ≤ C₀) (hCT : 0 ≤ C_T) (hCR : 0 ≤ C_R)
    (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec ((R.shift J).gradientChange k)) ≤ L * (R.shift J).curvature k)
    (V Z : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (hpair : ∀ k, m ≤ sqNorm ((V k)ᵀ.mulVec ((R.shift J).g k)))
    (hchange : ∀ k, sqNorm ((V (k + 1))ᵀ.mulVec ((R.shift J).gradientChange k)) ≤ C₀ * (R.shift J).curvature k)
    (htransport : ∀ k, V (k + 1) = V k * T k +
      EnergyIdentities.rectOuter ((R.shift J).displacement k) (b k) + Z k)
    (hT : ∀ k, FrameBounds.OperatorSqBound (T k) (1 + C_T * (R.shift J).d k))
    (hZ : ∀ k, (U * Uᵀ) * Z k = Z k)
    (hsize : ∀ k, SmoothSubspace.frobSq (Z k) ≤ C_R * (R.shift J).d k) : False :=
  (R.shift J).residual_frames_incompatible G hG (fun k => hg (J + k))
    (R.shift_summable_d hs J) U hU L m C₀ C_T C_R hL hm hC₀ hCT hCR hsmooth
    V Z T b hpair hchange htransport hT hZ hsize

end BfgsVerification.AdmissibleBFGSRun
