import BfgsVerification.RunShift

/-!
# Exact moving-frame trajectory criterion

The cumulative transports have determinant nonzero. Their uniform squared
operator bounds are written in coordinates as
`sqNorm (Pᵀ.mulVec v) ≤ K * sqNorm v` and the same bound for `(P⁻¹)ᵀ`.
These are bounds on the auxiliary frame transports, not on BFGS matrices.
Frames may be rectangular and rank deficient. The final contradiction retains
Module M's weaker vanishing-predicted-decrease hypothesis.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification
namespace MovingFrame

/-- Right-normalizing a rectangular rank-one increment stays rank one. -/
theorem rectOuter_mul {n r : ℕ} (s : Vec n) (b : Vec r) (Q : Mat r) :
    EnergyIdentities.rectOuter s b * Q = EnergyIdentities.rectOuter s (Qᵀ.mulVec b) := by
  ext i j
  simp only [Matrix.mul_apply, EnergyIdentities.rectOuter, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Cumulative products cancel the exact frame transport in the right order. -/
theorem transport_cancel {r : ℕ} (P Q T : Mat r)
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0) (hprod : Q = P * T) :
    T * Q⁻¹ = P⁻¹ := by
  calc
    T * Q⁻¹ = (P⁻¹ * P) * T * Q⁻¹ := by rw [Matrix.nonsing_inv_mul P hP.isUnit, Matrix.one_mul]
    _ = P⁻¹ * (P * T) * Q⁻¹ := by simp only [Matrix.mul_assoc]
    _ = P⁻¹ := by rw [← hprod, Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ.isUnit, Matrix.mul_one]

/-- The normalized frames move only by a multiple of the BFGS step. -/
theorem normalized_frame_step {n r : ℕ}
    (V W : Matrix (Fin n) (Fin r) ℝ) (P Q T : Mat r) (s : Vec n) (b : Vec r)
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0) (hprod : Q = P * T)
    (hframe : W = V * T + EnergyIdentities.rectOuter s b) :
    W * Q⁻¹ = V * P⁻¹ + EnergyIdentities.rectOuter s ((Q⁻¹)ᵀ.mulVec b) := by
  rw [hframe, Matrix.add_mul, Matrix.mul_assoc, transport_cancel P Q T hP hQ hprod,
    rectOuter_mul]

/-- Squared Euclidean norm of the original coordinates is controlled by the
uniform bound on the transpose transport. -/
theorem inverse_transpose_lower {r : ℕ} (P : Mat r) (hP : P.det ≠ 0)
    (K : ℝ) (hK : 0 < K) (hbound : ∀ v, sqNorm (Pᵀ.mulVec v) ≤ K * sqNorm v)
    (a : Vec r) : sqNorm a / K ≤ sqNorm ((P⁻¹)ᵀ.mulVec a) := by
  have hcancel : Pᵀ.mulVec ((P⁻¹)ᵀ.mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul P hP.isUnit,
      Matrix.transpose_one, Matrix.one_mulVec]
  have h := hbound ((P⁻¹)ᵀ.mulVec a)
  rw [hcancel] at h
  apply (div_le_iff₀ hK).2
  simpa only [mul_comm] using h

theorem trace_outer {r : ℕ} (a : Vec r) : (outer a a).trace = sqNorm a := by
  simp only [Matrix.trace, Matrix.diag, outer, sqNorm, pow_two]

theorem gram_trace_nonneg {n r : ℕ} {B : Mat n} (hB : B.PosSemidef)
    (V : Matrix (Fin n) (Fin r) ℝ) : 0 ≤ (metricGram B V).trace := by
  change 0 ≤ ∑ j, (metricGram B V) j j
  apply Finset.sum_nonneg
  intro j _
  rw [EnergyIdentities.gram_entry]
  simpa only [dot, dotProduct, star_trivial] using hB.2 (fun i => V i j)

end MovingFrame

namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Actual trace energy after congruence by the cumulative inverse transport. -/
def normalizedFrameEnergy {r : ℕ} (V : ℕ → Matrix (Fin n) (Fin r) ℝ)
    (P : ℕ → Mat r) (k : ℕ) : ℝ :=
  (metricGram (R.hessian k) (V k * (P k)⁻¹)).trace

/-- The normalized frame energy is exactly the source's inverse congruence trace. -/
theorem normalizedFrameEnergy_eq {r : ℕ} (V : ℕ → Matrix (Fin n) (Fin r) ℝ)
    (P : ℕ → Mat r) (k : ℕ) :
    R.normalizedFrameEnergy V P k =
      (((P k)⁻¹)ᵀ * metricGram (R.hessian k) (V k) * (P k)⁻¹).trace := by
  unfold normalizedFrameEnergy
  rw [EnergyIdentities.gram_transport]

theorem normalizedFrameEnergy_nonneg {r : ℕ} (V : ℕ → Matrix (Fin n) (Fin r) ℝ)
    (P : ℕ → Mat r) (k : ℕ) : 0 ≤ R.normalizedFrameEnergy V P k :=
  MovingFrame.gram_trace_nonneg (R.hessian_posDef k).posSemidef _

/-- Source M's transformed trace recurrence, derived from the actual moving-frame identity. -/
theorem normalized_frame_trace_recurrence {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T P : ℕ → Mat r) (b : ℕ → Vec r)
    (hP : ∀ k, (P k).det ≠ 0) (hprod : ∀ k, P (k + 1) = P k * T k)
    (hframe : ∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (k : ℕ) :
    R.normalizedFrameEnergy V P (k + 1) = R.normalizedFrameEnergy V P k -
      sqNorm (((P k)⁻¹)ᵀ.mulVec ((V k)ᵀ.mulVec (R.g k))) / R.q k +
      sqNorm (((P (k + 1))⁻¹)ᵀ.mulVec ((V (k + 1))ᵀ.mulVec (R.gradientChange k))) /
        R.curvature k := by
  have hstep := MovingFrame.normalized_frame_step (V k) (V (k + 1)) (P k) (P (k + 1))
    (T k) (R.displacement k) (b k) (hP k) (hP (k + 1)) (hprod k) (hframe k)
  have hident := R.moving_frame_energy k (V k * (P k)⁻¹) (V (k + 1) * (P (k + 1))⁻¹)
    1 (((P (k + 1))⁻¹)ᵀ.mulVec (b k)) (by simpa only [Matrix.mul_one] using hstep)
  unfold normalizedFrameEnergy
  rw [hident]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, MovingFrame.trace_outer,
    Matrix.transpose_mul, ← Matrix.mulVec_mulVec, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The source's trajectory hypotheses force an explicit linear bound on all
reciprocal sums. Bounds concern the cumulative frame transports only. -/
theorem moving_frame_reciprocal_sum_bound {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T P : ℕ → Mat r) (b : ℕ → Vec r)
    (hP : ∀ k, (P k).det ≠ 0) (hprod : ∀ k, P (k + 1) = P k * T k)
    (hframe : ∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (m K L C : ℝ) (hK : 0 < K) (hL : 0 ≤ L)
    (hvisible : ∀ k, m ≤ sqNorm ((V k)ᵀ.mulVec (R.g k)))
    (hcor : ∀ k, sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k)) / R.curvature k ≤ C)
    (htransport : ∀ k v, sqNorm ((P k)ᵀ.mulVec v) ≤ K * sqNorm v)
    (hinverse : ∀ k v, sqNorm (((P k)⁻¹)ᵀ.mulVec v) ≤ L * sqNorm v)
    (N : ℕ) :
    (m / K) * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      R.normalizedFrameEnergy V P 0 + L * C * (N : ℝ) := by
  have hstep : ∀ k, R.normalizedFrameEnergy V P (k + 1) ≤
      R.normalizedFrameEnergy V P k - (m / K) * (R.q k)⁻¹ + L * C := by
    intro k
    have hlower : m / K ≤ sqNorm (((P k)⁻¹)ᵀ.mulVec ((V k)ᵀ.mulVec (R.g k))) :=
      (div_le_div_of_nonneg_right (hvisible k) hK.le).trans
        (MovingFrame.inverse_transpose_lower (P k) (hP k) K hK (htransport k) _)
    have hdecr := mul_le_mul_of_nonneg_right hlower (inv_nonneg.mpr (R.q_pos k).le)
    have hcorr : sqNorm (((P (k + 1))⁻¹)ᵀ.mulVec
        ((V (k + 1))ᵀ.mulVec (R.gradientChange k))) / R.curvature k ≤ L * C := by
      calc
        _ ≤ (L * sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k))) / R.curvature k :=
          div_le_div_of_nonneg_right (hinverse (k + 1) _) (R.curvature_pos k).le
        _ = L * (sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k)) / R.curvature k) := by ring
        _ ≤ L * C := mul_le_mul_of_nonneg_left (hcor k) hL
    rw [R.normalized_frame_trace_recurrence V T P b hP hprod hframe k]
    simp only [div_eq_mul_inv] at hdecr hcorr ⊢
    linarith
  have htel : ∀ N, (m / K) * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      R.normalizedFrameEnergy V P 0 - R.normalizedFrameEnergy V P N + L * C * (N : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, mul_add]
      push_cast
      linarith [hstep M]
  linarith [htel N, R.normalizedFrameEnergy_nonneg V P N]

/-- Exact moving-frame transports with uniformly bounded products and inverse
products cannot sustain a uniformly visible frame on an infinite run satisfying
Module M's weaker bounded-gradient and vanishing-decrease hypotheses. The
visibility constant `m` is the squared norm lower bound. -/
theorem moving_frame_criterion {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T P : ℕ → Mat r) (b : ℕ → Vec r)
    (hP : ∀ k, (P k).det ≠ 0) (hprod : ∀ k, P (k + 1) = P k * T k)
    (hframe : ∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (m K L C : ℝ) (hm : 0 < m) (hK : 0 < K) (hL : 0 ≤ L)
    (hvisible : ∀ k, m ≤ sqNorm ((V k)ᵀ.mulVec (R.g k)))
    (hcor : ∀ k, sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k)) / R.curvature k ≤ C)
    (htransport : ∀ k v, sqNorm ((P k)ᵀ.mulVec v) ≤ K * sqNorm v)
    (hinverse : ∀ k v, sqNorm (((P k)⁻¹)ᵀ.mulVec v) ≤ L * sqNorm v)
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hd : Tendsto R.d atTop (𝓝 0)) : False := by
  have hmean := (objectiveReciprocalGrowth n F R G hG hg hd).2
  let E₀ := R.normalizedFrameEnergy V P 0
  let D := (E₀ + L * C) / (m / K)
  obtain ⟨N, hN, hbig⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hmean.eventually (eventually_gt_atTop D))).exists
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hcoeff : 0 < m / K := div_pos hm hK
  have hfinite := R.moving_frame_reciprocal_sum_bound V T P b hP hprod hframe
    m K L C hK hL hvisible hcor htransport hinverse N
  have hE₀ := mul_le_mul_of_nonneg_left hNreal (R.normalizedFrameEnergy_nonneg V P 0)
  have hlinear : (m / K) * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      (E₀ + L * C) * (N : ℝ) := by
    dsimp only [E₀]
    nlinarith
  have hnormalized : (m / K) * reciprocalMean R.q N ≤ E₀ + L * C := by
    unfold reciprocalMean
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hNpos).2 hlinear
  have hupper : reciprocalMean R.q N ≤ D := by
    apply (le_div_iff₀ hcoeff).2
    simpa only [mul_comm] using hnormalized
  exact not_lt_of_ge hupper hbig

/-- The exact source trajectory criterion on an arbitrary tail. The initial
normalization may in particular be `P J = 1`; the theorem is valid for any
invertible starting normalization and makes no frame rank assumption. -/
theorem moving_frame_tail_criterion {r : ℕ} (J : ℕ)
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T P : ℕ → Mat r) (b : ℕ → Vec r)
    (hP : ∀ k, J ≤ k → (P k).det ≠ 0)
    (hprod : ∀ k, J ≤ k → P (k + 1) = P k * T k)
    (hframe : ∀ k, J ≤ k →
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (m K L C : ℝ) (hm : 0 < m) (hK : 0 < K) (hL : 0 ≤ L)
    (hvisible : ∀ k, J ≤ k → m ≤ sqNorm ((V k)ᵀ.mulVec (R.g k)))
    (hcor : ∀ k, J ≤ k →
      sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k)) / R.curvature k ≤ C)
    (htransport : ∀ k, J ≤ k → ∀ v, sqNorm ((P k)ᵀ.mulVec v) ≤ K * sqNorm v)
    (hinverse : ∀ k, J ≤ k → ∀ v, sqNorm (((P k)⁻¹)ᵀ.mulVec v) ≤ L * sqNorm v)
    (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hd : Tendsto R.d atTop (𝓝 0)) : False := by
  apply (R.shift J).moving_frame_criterion (fun k => V (J + k)) (fun k => T (J + k))
    (fun k => P (J + k)) (fun k => b (J + k))
    (fun k => hP (J + k) (Nat.le_add_right J k))
    (fun k => hprod (J + k) (Nat.le_add_right J k))
    (fun k => hframe (J + k) (Nat.le_add_right J k))
    m K L C hm hK hL
    (fun k => hvisible (J + k) (Nat.le_add_right J k))
    (fun k => hcor (J + k) (Nat.le_add_right J k))
    (fun k => htransport (J + k) (Nat.le_add_right J k))
    (fun k => hinverse (J + k) (Nat.le_add_right J k))
    G hG (fun k => hg (J + k)) (R.shift_d_tendsto_zero hd J)

end AdmissibleBFGSRun
end BfgsVerification
