import BfgsVerification.MovingFrame
import BfgsVerification.ResidualBudget
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Scalar transported energy used in C, derived from actual full BFGS.
The finite bound retains the qualitative reciprocal-average contradiction. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace ScalarTransport
open ResidualBudget

theorem energy_smul_vector {n : ℕ} (B : Mat n) (w : Vec n) (a : ℝ) :
    metricEnergy B (a • w) = a^2*metricEnergy B w := by
  change dotProduct (a • w) (B.mulVec (a • w)) = a^2*dotProduct w (B.mulVec w)
  rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The source logarithmic transport budget gives its square multiplier bound
with a fixed explicit constant, once the predicted decrease is at most one. -/
theorem square_le_of_log_bound {a C d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hlog : |Real.log a| ≤ C*d) :
    a^2 ≤ 1+(Real.exp (2*C)-1)*d := by
  have hexp : a^2 ≤ Real.exp (2*C*d) := by
    calc
      a^2 = Real.exp (Real.log a+Real.log a) := by rw [Real.exp_add,Real.exp_log ha]; ring
      _ ≤ Real.exp (2*C*d) := Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log a)])
  have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (2*C))
    (show 0 ≤ 1-d by linarith) hd (show (1-d)+d=1 by ring)
  simp only [smul_eq_mul, mul_zero,zero_add,Real.exp_zero,mul_one] at hc
  have he : d*(2*C) = 2*C*d := by ring
  rw [he] at hc
  linarith

/-- Constant additive correction yields an actual linear reciprocal budget. -/
theorem reciprocal_sum_le {E q u : ℕ → ℝ} {m C : ℝ}
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k)
    (hu : ∀ k, 0 ≤ u k) (hs : Summable u) (hm : 0 < m) (hC : 0 ≤ C)
    (hrec : ∀ k, E (k+1) ≤ (1+u k)*(E k-m/q k)+C) (N : ℕ) :
    (m/Real.exp (∑' k, u k))*(∑ k ∈ Finset.range N, (q k)⁻¹) ≤ E 0+C*(N : ℝ) := by
  let P := driftProduct u
  let B := Real.exp (∑' k, u k)
  have hPone : ∀ k, 1 ≤ P k := one_le_driftProduct hu
  have hPpos : ∀ k, 0 < P k := fun k => lt_of_lt_of_le zero_lt_one (hPone k)
  have hPB : ∀ k, P k ≤ B := driftProduct_le_exp_tsum hu hs
  have hnorm : ∀ k, E (k+1)/P (k+1) ≤ E k/P k-(m/B)*(q k)⁻¹+C := by
    intro k
    have hfactor : 0 < 1+u k := by linarith [hu k]
    have hchange : ((1+u k)*(E k-m/q k)+C)/P (k+1) =
        E k/P k-(m/q k)/P k+C/P (k+1) := by
      rw [show P (k+1) = P k*(1+u k) from driftProduct_succ u k]
      field_simp [(hPpos k).ne',hfactor.ne',(hq k).ne']
      ring
    have hdes : (m/B)*(q k)⁻¹ ≤ (m/q k)/P k := by
      rw [show (m/B)*(q k)⁻¹ = (m/q k)/B by ring]
      exact div_le_div_of_nonneg_left (div_nonneg hm.le (hq k).le) (hPpos k) (hPB k)
    have hadd : C/P (k+1) ≤ C := div_le_self hC (hPone (k+1))
    have hdiv := div_le_div_of_nonneg_right (hrec k) (hPpos (k+1)).le
    rw [hchange] at hdiv
    linarith
  have hsum := descent_sum_le (fun k => div_nonneg (hE k) (hPpos k).le) hnorm N
  simpa only [← Finset.mul_sum,P,driftProduct_zero,div_one,B,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,mul_comm (N : ℝ) C] using hsum

end ScalarTransport
namespace AdmissibleBFGSRun
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem scalar_frame_residual_nonneg (k : ℕ) (w : Vec n) :
    0 ≤ metricEnergy (R.hessian k) w-(dot (R.g k) w)^2/R.q k := by
  have h := (R.annihilated_hessian_posSemidef k).2 w
  change 0 ≤ metricEnergy (R.hessian k-(R.q k)⁻¹ • outer (R.g k) (R.g k)) w at h
  rw [EnergyIdentities.energy_sub_matrix,EnergyIdentities.energy_smul_matrix,EnergyIdentities.energy_outer] at h
  simpa only [div_eq_mul_inv,mul_comm] using h

/-- C's exact scalar energy identity, with no frame or BFGS matrix limit. -/
theorem scalar_frame_energy (k : ℕ) (w z : Vec n) (a b : ℝ)
    (hz : z = a • w+b • R.displacement k) :
    metricEnergy (R.hessian (k+1)) z =
      a^2*(metricEnergy (R.hessian k) w-(dot (R.g k) w)^2/R.q k)+
        (dot (R.gradientChange k) z)^2/R.curvature k := by
  have hk : (R.hessian k-(R.q k)⁻¹ • outer (R.g k) (R.g k)).mulVec (b • R.displacement k)=0 := by
    rw [Matrix.mulVec_smul,R.annihilated_hessian_mul_displacement,smul_zero]
  rw [R.hessian_update,EnergyIdentities.energy_add_matrix,EnergyIdentities.energy_smul_matrix,
    EnergyIdentities.energy_outer]
  conv_lhs => arg 1; rw [hz]
  rw [EnergyIdentities.energy_add_kernel (R.annihilated_hessian_isSymm k) hk,
    ScalarTransport.energy_smul_vector,EnergyIdentities.energy_sub_matrix,
    EnergyIdentities.energy_smul_matrix,EnergyIdentities.energy_outer]
  simp only [div_eq_mul_inv]
  ring

/-- Every actual scalar frame satisfying the derived endpoint estimates obeys
an explicit O(N) reciprocal bound. Scalar transport positivity is not needed
once its square is bounded. -/
theorem scalar_frame_reciprocal_sum_bound (w : ℕ → Vec n) (a b : ℕ → ℝ)
    (hframe : ∀ k, w (k+1)=a k • w k+b k • R.displacement k)
    (m C C0 : ℝ) (hm : 0 < m) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hvisible : ∀ k, m ≤ (dot (R.g k) (w k))^2)
    (htransport : ∀ k, (a k)^2 ≤ 1+C*R.d k)
    (hcor : ∀ k, (dot (R.gradientChange k) (w (k+1)))^2/R.curvature k ≤ C0)
    (hs : Summable R.d) (N : ℕ) :
    (m/Real.exp (∑' k, C*R.d k))*(∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      metricEnergy (R.hessian 0) (w 0)+C0*(N : ℝ) := by
  apply ScalarTransport.reciprocal_sum_le (E := fun k => metricEnergy (R.hessian k) (w k))
    (fun k => by simpa only [metricEnergy,dot,star_trivial] using (R.hessian_posDef k).posSemidef.2 (w k))
    R.q_pos (fun k => mul_nonneg hC (R.d_pos k).le) (hs.mul_left C) hm hC0
  intro k
  rw [R.scalar_frame_energy k (w k) (w (k+1)) (a k) (b k) (hframe k)]
  have h1 := mul_le_mul_of_nonneg_right (htransport k) (R.scalar_frame_residual_nonneg k (w k))
  have h2 := div_le_div_of_nonneg_right (hvisible k) (R.q_pos k).le
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1+C*R.d k by
    linarith [mul_nonneg hC (R.d_pos k).le])
  linarith [hcor k]

/-- The scalar frame estimate contradicts M's qualitative reciprocal-average
theorem; no superquadratic strengthening is required. -/
theorem scalar_frame_incompatible (w : ℕ → Vec n) (a b : ℕ → ℝ)
    (hframe : ∀ k, w (k+1)=a k • w k+b k • R.displacement k)
    (m C C0 : ℝ) (hm : 0 < m) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hvisible : ∀ k, m ≤ (dot (R.g k) (w k))^2)
    (htransport : ∀ k, (a k)^2 ≤ 1+C*R.d k)
    (hcor : ∀ k, (dot (R.gradientChange k) (w (k+1)))^2/R.curvature k ≤ C0)
    (hs : Summable R.d) (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G^2) : False := by
  have hmean := (objectiveReciprocalGrowth n F R G hG hg hs.tendsto_atTop_zero).2
  let coeff := m/Real.exp (∑' k, C*R.d k)
  let E0 := metricEnergy (R.hessian 0) (w 0)
  have hcoeff : 0 < coeff := div_pos hm (Real.exp_pos _)
  have hE0 : 0 ≤ E0 := by
    simpa only [E0,metricEnergy,dot,star_trivial] using (R.hessian_posDef 0).posSemidef.2 (w 0)
  obtain ⟨N,hN,hbig⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hmean.eventually (eventually_gt_atTop ((E0+C0)/coeff)))).exists
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hb := R.scalar_frame_reciprocal_sum_bound w a b hframe m C C0 hm hC hC0
    hvisible htransport hcor hs N
  have hbound : coeff*(∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤ (E0+C0)*(N : ℝ) := by
    change coeff*(∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤ E0+C0*(N : ℝ) at hb
    nlinarith
  have hnorm : coeff*reciprocalMean R.q N ≤ E0+C0 := by
    unfold reciprocalMean
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hNpos).mpr hbound
  have hu : reciprocalMean R.q N ≤ (E0+C0)/coeff := by
    apply (le_div_iff₀ hcoeff).mpr
    nlinarith
  exact not_lt_of_ge hu hbig

/-- Exact source tail convention, with all earlier iterations discarded by
the verified shift of the actual run. -/
theorem scalar_frame_tail_incompatible (J : ℕ) (w : ℕ → Vec n) (a b : ℕ → ℝ)
    (hframe : ∀ k, J ≤ k → w (k+1)=a k • w k+b k • R.displacement k)
    (m C C0 : ℝ) (hm : 0 < m) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hvisible : ∀ k, J ≤ k → m ≤ (dot (R.g k) (w k))^2)
    (htransport : ∀ k, J ≤ k → (a k)^2 ≤ 1+C*R.d k)
    (hcor : ∀ k, J ≤ k → (dot (R.gradientChange k) (w (k+1)))^2/R.curvature k ≤ C0)
    (hs : Summable R.d) (G : ℝ) (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G^2) : False := by
  exact (R.shift J).scalar_frame_incompatible (fun k => w (J+k)) (fun k => a (J+k))
    (fun k => b (J+k)) (fun k => hframe (J+k) (Nat.le_add_right J k))
    m C C0 hm hC hC0 (fun k => hvisible (J+k) (Nat.le_add_right J k))
    (fun k => htransport (J+k) (Nat.le_add_right J k))
    (fun k => hcor (J+k) (Nat.le_add_right J k)) (R.shift_summable_d hs J)
    G hG (fun k => hg (J+k))

/-- The exact logarithmic endpoint estimates from C imply the contradiction
on a compact actual run. Gradient bounds, summable decreases, the small-step
threshold, and the square multiplier estimate are all discharged here. -/
theorem scalar_log_transport_tail_incompatible (hK : IsCompact R.initialSublevel)
    (J : ℕ) (w : ℕ → Vec n) (a b : ℕ → ℝ)
    (hframe : ∀ k, J ≤ k → w (k+1)=a k • w k+b k • R.displacement k)
    (η C C0 : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hvisible : ∀ k, J ≤ k → η ≤ dot (R.g k) (w k))
    (hpos : ∀ k, J ≤ k → 0 < a k)
    (hlog : ∀ k, J ≤ k → |Real.log (a k)| ≤ C*R.d k)
    (hcor : ∀ k, J ≤ k → (dot (R.gradientChange k) (w (k+1)))^2/R.curvature k ≤ C0) : False := by
  have hs := R.summable_predicted_decreases_of_compact_sublevel hK
  obtain ⟨G,hG,hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  have hd : ∀ᶠ k in atTop, R.d k ≤ 1 :=
    (hs.tendsto_atTop_zero.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).mono
      (fun _ h => h.le)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hd
  have hC' : 0 ≤ Real.exp (2*C)-1 := by
    have he := Real.one_le_exp_iff.mpr (show 0 ≤ 2*C by positivity)
    linarith
  apply R.scalar_frame_tail_incompatible (max J N) w a b
    (fun k hk => hframe k ((le_max_left J N).trans hk))
    (η^2) (Real.exp (2*C)-1) C0 (sq_pos_of_pos hη) hC' hC0
  · intro k hk
    have hv := hvisible k ((le_max_left J N).trans hk)
    nlinarith
  · intro k hk
    exact ScalarTransport.square_le_of_log_bound
      (hpos k ((le_max_left J N).trans hk)) (R.d_pos k).le
      (hN k ((le_max_right J N).trans hk)) (hlog k ((le_max_left J N).trans hk))
  · exact fun k hk => hcor k ((le_max_left J N).trans hk)
  · exact hs
  · exact hG
  · exact hg

end AdmissibleBFGSRun
end BfgsVerification
