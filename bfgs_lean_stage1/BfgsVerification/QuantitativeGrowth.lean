import BfgsVerification.ScalarHierarchy
import BfgsVerification.Definitions

/-!
# Finite-horizon estimates under an explicit normalized hierarchy

These are scalar results conditional on `NormalizedHierarchy`. They do not
by themselves prove that the actual BFGS principal determinants satisfy it.
The exponential form below is the positive-real-power bound in Module M.3.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace BfgsVerification.QuantitativeGrowth
open BfgsVerification.ScalarHierarchy

/-- A finite equal-weight logarithmic AM--GM inequality, proved directly from
`log t ≤ t - 1`, so the normalization and positivity remain explicit. -/
theorem sum_log_le_of_sum_le (x : ℕ → ℝ) (m : ℕ) (B : ℝ)
    (hx : ∀ i, 0 < x i) (hB : 0 < B)
    (hsum : (∑ i ∈ Finset.range m, x i) ≤ (m : ℝ) * B) :
    (∑ i ∈ Finset.range m, Real.log (x i)) ≤ (m : ℝ) * Real.log B := by
  have hi : ∀ i, Real.log (x i) ≤ Real.log B + x i / B - 1 := by
    intro i
    have h := Real.log_le_sub_one_of_pos (div_pos (hx i) hB)
    rw [Real.log_div (ne_of_gt (hx i)) (ne_of_gt hB)] at h
    linarith
  have hs := Finset.sum_le_sum (s := Finset.range m) (fun i _ => hi i)
  have hsum' : (∑ i ∈ Finset.range m, x i / B) ≤ (m : ℝ) := by
    rw [← Finset.sum_div]
    exact (div_le_iff₀ hB).2 hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  linarith

/-- Convert any upper bound on the logarithmic product into a lower bound on
its reciprocal arithmetic sum. -/
theorem reciprocal_sum_ge_exp (q : ℕ → ℝ) (m : ℕ) (L : ℝ)
    (hm : 0 < m) (hq : ∀ i, 0 < q i)
    (hlog : (∑ i ∈ Finset.range m, Real.log (q i)) ≤ L) :
    (m : ℝ) * Real.exp (-L / (m : ℝ)) ≤
      ∑ i ∈ Finset.range m, (q i)⁻¹ := by
  let S : ℝ := ∑ i ∈ Finset.range m, (q i)⁻¹
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i _
      exact inv_pos.mpr (hq i)
    · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hm)
  have hmean : 0 < S / (m : ℝ) := div_pos hS hmR
  have ha := sum_log_le_of_sum_le (fun i => (q i)⁻¹) m (S / (m : ℝ))
    (fun i => inv_pos.mpr (hq i)) hmean (by
      dsimp [S]
      rw [mul_div_cancel₀ _ (ne_of_gt hmR)])
  simp only [Real.log_inv, Finset.sum_neg_distrib] at ha
  have hle : -L / (m : ℝ) ≤ Real.log (S / (m : ℝ)) := by
    apply (div_le_iff₀ hmR).2
    nlinarith
  have he := Real.exp_le_exp.mpr hle
  rw [Real.exp_log hmean] at he
  simpa only [mul_comm] using (le_div_iff₀ hmR).1 he

/-- Variable-coefficient telescoping through the penultimate step, followed by
one endpoint bound. The block contains `m + 1` reciprocal energies. -/
theorem log_product_upper_of_potential
    (q V a : ℕ → ℝ) (C : ℝ) (J m : ℕ)
    (hq : ∀ k, 0 < q k) (hV : ∀ k, 0 < V k)
    (ha : ∀ k, 0 < a k) (hC : 0 < C)
    (hstep : ∀ k, q k * V (k + 1) ≤ a k * V k)
    (hbound : ∀ k, q k ≤ C * V k) :
    (∑ i ∈ Finset.range (m + 1), Real.log (q (J + i))) ≤
      Real.log (C * V J) + ∑ i ∈ Finset.range m, Real.log (a (J + i)) := by
  have ht : ∀ p : ℕ,
      (∑ i ∈ Finset.range p, Real.log (q (J + i))) + Real.log (V (J + p)) ≤
        Real.log (V J) + ∑ i ∈ Finset.range p, Real.log (a (J + i)) := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      have h := Real.log_le_log (mul_pos (hq (J + p)) (hV (J + p + 1)))
        (hstep (J + p))
      rw [Real.log_mul (ne_of_gt (hq _)) (ne_of_gt (hV _)),
        Real.log_mul (ne_of_gt (ha _)) (ne_of_gt (hV _))] at h
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.add_assoc] at h ⊢
      linarith
  have hb := Real.log_le_log (hq (J + m)) (hbound (J + m))
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (hV _))] at hb
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (hV J)), Finset.sum_range_succ]
  linarith [ht m]

/-- The finite-horizon bound from M.3, in exponential notation and with a block
of length `m+1` (hence `m>0`). `D` bounds the total normalized tail budget.
No asymptotic or matrix convergence assumption occurs. -/
theorem hierarchy_finite_horizon
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C)
    (hδ : ∀ k, 0 ≤ δ k) (J m : ℕ) (hm : 0 < m)
    (η D : ℝ) (hη : 0 < η) (hD : 0 ≤ D)
    (hbudget : (∑ i ∈ Finset.range m, δ (J + i)) ≤ D) :
    ((m + 1 : ℕ) : ℝ) * Real.exp
      (-(Real.log (C * weightedPotential n (K / η) (E J)) +
          (m : ℝ) * Real.log (η + D / (m : ℝ))) / ((m + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range (m + 1), (q (J + i))⁻¹ := by
  let V : ℕ → ℝ := fun k => weightedPotential n (K / η) (E k)
  have hdom : ∀ k, E k 1 ≤ V k := fun k => first_le_weighted n (K / η) (E k)
    H.dimension_pos (div_nonneg H.K_nonneg hη.le) (H.coefficient_nonneg k)
  have hV : ∀ k, 0 < V k := fun k => lt_of_lt_of_le (H.trace_pos k) (hdom k)
  have hstep : ∀ k, q k * V (k + 1) ≤ (η + δ k) * V k := fun k =>
    weighted_step n (E k) (E (k + 1)) (q k) K η (δ k)
      H.K_nonneg hη (H.coefficient_nonneg k) (H.terminal k) (H.step k)
  have hbound : ∀ k, q k ≤ C * V k := fun k => (H.trace_bound k).trans
    (mul_le_mul_of_nonneg_left (hdom k) H.C_pos.le)
  have hp := log_product_upper_of_potential q V (fun k => η + δ k) C J m
    H.q_pos hV (fun k => add_pos_of_pos_of_nonneg hη (hδ k)) H.C_pos hstep hbound
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha := sum_log_le_of_sum_le (fun i => η + δ (J + i)) m
    (η + D / (m : ℝ)) (fun i => add_pos_of_pos_of_nonneg hη (hδ _))
    (add_pos_of_pos_of_nonneg hη (div_nonneg hD hmR.le)) (by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hmR)]
      linarith)
  exact reciprocal_sum_ge_exp (fun i => q (J + i)) (m + 1) _
    (by omega) (fun i => H.q_pos _) (hp.trans (add_le_add_left ha _))


/-- A horizon-dependent weighted potential grows at most polynomially.
The degree `n` is a harmless overestimate of the optimal degree `n-1`. -/
theorem weightedPotential_mul_le (n : ℕ) (r t : ℝ) (e : ℕ → ℝ)
    (hr : 0 ≤ r) (ht : 1 ≤ t) (he : ∀ j, 0 ≤ e j) :
    weightedPotential n (r * t) e ≤ weightedPotential n r e * t ^ n := by
  unfold weightedPotential
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := (Finset.mem_range.mp hj).le
  have hp := pow_le_pow_right₀ ht hjn
  calc
    (r * t) ^ j * e (j + 1) = (r ^ j * e (j + 1)) * t ^ j := by
      rw [mul_pow]
      ring
    _ ≤ (r ^ j * e (j + 1)) * t ^ n :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg hr _) (he _))

/-- The explicit expression left after dividing the optimized finite-horizon
bound by the square of the block length. -/
def normalizedLower (A D : ℝ) (n m : ℕ) : ℝ :=
  (m : ℝ) / ((m : ℝ) + 1) *
    Real.exp (-(Real.log A + ((n : ℝ) + 1) * Real.log (m : ℝ)) / ((m : ℝ) + 1)
      - ((m : ℝ) / ((m : ℝ) + 1)) * Real.log (2 * D))

/-- The potential polynomial contributes a vanishing logarithmic correction.
This horizon limit holds with the tail and its initial potential fixed. -/
theorem normalizedLower_tendsto (A D : ℝ) (n : ℕ) (hD : 0 < D) :
    Tendsto (normalizedLower A D n) atTop (nhds ((2 * D)⁻¹)) := by
  have hratio : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ) / ((m : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [pow_one, one_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun m : ℕ => Real.log A / ((m : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [one_div, div_eq_mul_inv, mul_zero, one_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log A)
  have hexp : Tendsto
      (fun m : ℕ => -(Real.log A + ((n : ℝ) + 1) * Real.log (m : ℝ)) /
        ((m : ℝ) + 1) - ((m : ℝ) / ((m : ℝ) + 1)) * Real.log (2 * D))
      atTop (nhds (-Real.log (2 * D))) := by
    convert ((hconst.add (hlog.const_mul ((n : ℝ) + 1))).neg.sub
      (hratio.mul_const (Real.log (2 * D)))) using 1
    · funext m
      ring
    · simp
  have he := hratio.mul (Real.continuous_exp.tendsto _ |>.comp hexp)
  simpa only [one_mul, Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * D),
    normalizedLower] using he


/-- Optimizing `η = D/m` gives the normalized lower bound, while the
initial potential is frozen at the fixed tail index `J`. -/
theorem hierarchy_normalized_lower
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C)
    (hδ : ∀ k, 0 ≤ δ k) (J m : ℕ) (hm : 0 < m)
    (D : ℝ) (hD : 0 < D)
    (hbudget : (∑ i ∈ Finset.range m, δ (J + i)) ≤ D) :
    normalizedLower (C * weightedPotential n (K / D) (E J)) D n m ≤
      (∑ i ∈ Finset.range (m + 1), (q (J + i))⁻¹) / ((m : ℝ) + 1) ^ 2 := by
  let A : ℝ := C * weightedPotential n (K / D) (E J)
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have hbase : 0 < weightedPotential n (K / D) (E J) :=
    lt_of_lt_of_le (H.trace_pos J) (first_le_weighted n (K / D) (E J)
      H.dimension_pos (div_nonneg H.K_nonneg hD.le) (H.coefficient_nonneg J))
  have hA : 0 < A := mul_pos H.C_pos hbase
  have hη : 0 < D / (m : ℝ) := div_pos hD hmR
  have hvar : 0 < weightedPotential n (K / (D / (m : ℝ))) (E J) :=
    lt_of_lt_of_le (H.trace_pos J) (first_le_weighted n (K / (D / (m : ℝ))) (E J)
      H.dimension_pos (div_nonneg H.K_nonneg hη.le) (H.coefficient_nonneg J))
  have hpoly : C * weightedPotential n (K / (D / (m : ℝ))) (E J) ≤ A * (m : ℝ) ^ n := by
    have hi : K / (D / (m : ℝ)) = K / D * (m : ℝ) := by field_simp
    rw [hi]
    exact (mul_le_mul_of_nonneg_left
      (weightedPotential_mul_le n (K / D) (m : ℝ) (E J)
        (div_nonneg H.K_nonneg hD.le) (by exact_mod_cast hm) (H.coefficient_nonneg J))
      H.C_pos.le).trans_eq (by dsimp [A]; ring)
  have hl := Real.log_le_log (mul_pos H.C_pos hvar) hpoly
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt (pow_pos hmR n)), Real.log_pow] at hl
  have hf := hierarchy_finite_horizon H hδ J m hm (D / (m : ℝ)) D hη hD.le hbudget
  have hi : D / (m : ℝ) + D / (m : ℝ) = 2 * D / (m : ℝ) := by ring
  rw [hi] at hf
  push_cast at hf
  have he : Real.exp (-(Real.log A + (n : ℝ) * Real.log (m : ℝ) +
      (m : ℝ) * Real.log (2 * D / (m : ℝ))) / ((m : ℝ) + 1)) ≤
      Real.exp (-(Real.log (C * weightedPotential n (K / (D / (m : ℝ))) (E J)) +
      (m : ℝ) * Real.log (2 * D / (m : ℝ))) / ((m : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) hm1.le
  have hfinal := (mul_le_mul_of_nonneg_left he hm1.le).trans hf
  have hform : normalizedLower A D n m =
      (((m : ℝ) + 1) * Real.exp (-(Real.log A + (n : ℝ) * Real.log (m : ℝ) +
      (m : ℝ) * Real.log (2 * D / (m : ℝ))) / ((m : ℝ) + 1))) /
      ((m : ℝ) + 1) ^ 2 := by
    rw [Real.log_div (by positivity : 2 * D ≠ 0) (ne_of_gt hmR)]
    have hex : -(Real.log A + (n : ℝ) * Real.log (m : ℝ) +
        (m : ℝ) * (Real.log (2 * D) - Real.log (m : ℝ))) / ((m : ℝ) + 1) =
        Real.log (m : ℝ) +
          (-(Real.log A + ((n : ℝ) + 1) * Real.log (m : ℝ)) / ((m : ℝ) + 1) -
          ((m : ℝ) / ((m : ℝ) + 1)) * Real.log (2 * D)) := by
      field_simp
      ring
    rw [hex, Real.exp_add, Real.exp_log hmR]
    unfold normalizedLower
    field_simp
    ring
  rw [hform]
  exact div_le_div_of_nonneg_right hfinal (sq_nonneg _)


/-- With a tail fixed first, every number below `1/(2D)` is an eventual
lower bound for the full reciprocal sum divided by the square of its horizon.
The fixed prefix is retained explicitly. -/
theorem hierarchy_fixed_tail_lower_eventually
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C)
    (hδ : ∀ k, 0 ≤ δ k) (J : ℕ) (D : ℝ) (hD : 0 < D)
    (hbudget : ∀ m, (∑ i ∈ Finset.range m, δ (J + i)) ≤ D)
    (a : ℝ) (ha : a < (2 * D)⁻¹) :
    ∀ᶠ N : ℕ in atTop,
      a ≤ (∑ i ∈ Finset.range N, (q i)⁻¹) / (N : ℝ) ^ 2 := by
  let A : ℝ := C * weightedPotential n (K / D) (E J)
  let F : ℕ → ℝ := fun m => normalizedLower A D n m *
    (((m : ℝ) + 1) / ((J : ℝ) + (m : ℝ) + 1)) ^ 2
  have hratio : Tendsto (fun m : ℕ =>
      ((m : ℝ) + 1) / ((J : ℝ) + (m : ℝ) + 1)) atTop (nhds 1) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
      add_left_comm] using
      (tendsto_natCast_div_add_atTop (J : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hF : Tendsto F atTop (nhds ((2 * D)⁻¹)) := by
    simpa only [one_pow, mul_one, F] using
      (normalizedLower_tendsto A D n hD).mul (hratio.pow 2)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hF.eventually_const_lt ha)
  refine eventually_atTop.mpr ⟨J + (max M 1 + 1), ?_⟩
  intro N hN
  let m : ℕ := N - (J + 1)
  have hm : 0 < m := by dsimp [m]; omega
  have hMm : M ≤ m := by dsimp [m]; omega
  have hNm : J + (m + 1) = N := by dsimp [m]; omega
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have hden : 0 < (J : ℝ) + (m : ℝ) + 1 := by positivity
  have hnorm := hierarchy_normalized_lower H hδ J m hm D hD (hbudget m)
  have hmul := mul_le_mul_of_nonneg_right hnorm
    (sq_nonneg (((m : ℝ) + 1) / ((J : ℝ) + (m : ℝ) + 1)))
  have halg : ((∑ i ∈ Finset.range (m + 1), (q (J + i))⁻¹) / ((m : ℝ) + 1) ^ 2) *
      (((m : ℝ) + 1) / ((J : ℝ) + (m : ℝ) + 1)) ^ 2 =
      (∑ i ∈ Finset.range (m + 1), (q (J + i))⁻¹) /
        ((J : ℝ) + (m : ℝ) + 1) ^ 2 := by
    field_simp
  rw [halg] at hmul
  have hprefix : 0 ≤ ∑ i ∈ Finset.range J, (q i)⁻¹ :=
    Finset.sum_nonneg (fun i _ => (inv_pos.mpr (H.q_pos i)).le)
  have hsum : (∑ i ∈ Finset.range (m + 1), (q (J + i))⁻¹) ≤
      ∑ i ∈ Finset.range N, (q i)⁻¹ := by
    rw [← hNm, Finset.sum_range_add (fun i => (q i)⁻¹) J (m + 1)]
    linarith
  have hcast : (N : ℝ) = (J : ℝ) + (m : ℝ) + 1 := by
    rw [← hNm]
    push_cast
    ring
  rw [hcast]
  exact (hM m hMm).le.trans (hmul.trans
    (div_le_div_of_nonneg_right hsum (sq_nonneg _)))

/-- M.3's superquadratic conclusion for the explicit normalized scalar
hierarchy. The result remains conditional until a matrix-to-hierarchy bridge
has supplied `H` for the actual full-BFGS run. -/
theorem hierarchy_superquadratic_growth
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C)
    (hδ : ∀ k, 0 ≤ δ k) (hsummable : Summable δ) :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, (q i)⁻¹) / (N : ℝ) ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro a
  let D : ℝ := 1 / (4 * (max a 0 + 1))
  have hmax : 0 ≤ max a 0 := le_max_right _ _
  have hD : 0 < D := by dsimp [D]; positivity
  have htarget : a < (2 * D)⁻¹ := by
    have hpos : 0 < max a 0 + 1 := by positivity
    have heq : (2 * D)⁻¹ = 2 * (max a 0 + 1) := by
      dsimp [D]
      field_simp
      ring
    rw [heq]
    linarith [le_max_left a 0]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    ((tendsto_sum_nat_add δ).eventually_lt_const hD)
  have htail : (∑' i : ℕ, δ (i + J)) ≤ D := (hJ J le_rfl).le
  have hsumtail : Summable (fun i => δ (i + J)) :=
    (summable_nat_add_iff J).2 hsummable
  have hbudget : ∀ m, (∑ i ∈ Finset.range m, δ (J + i)) ≤ D := by
    intro m
    simpa only [Nat.add_comm] using
      (hsumtail.sum_le_tsum (Finset.range m) (fun i _ => hδ (i + J))).trans htail
  exact hierarchy_fixed_tail_lower_eventually H hδ J D hD hbudget a htarget


/-- The same finite-horizon estimate in the exact positive-real-power form
of Module M.3. Here the block length is `m+1` and `D` is the normalized budget. -/
theorem hierarchy_finite_horizon_rpow
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C)
    (hδ : ∀ k, 0 ≤ δ k) (J m : ℕ) (hm : 0 < m)
    (η D : ℝ) (hη : 0 < η) (hD : 0 ≤ D)
    (hbudget : (∑ i ∈ Finset.range m, δ (J + i)) ≤ D) :
    ((m + 1 : ℕ) : ℝ) *
        (C * weightedPotential n (K / η) (E J)) ^ (-1 / ((m + 1 : ℕ) : ℝ)) *
        (η + D / (m : ℝ)) ^ (-(m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range (m + 1), (q (J + i))⁻¹ := by
  have hV : 0 < weightedPotential n (K / η) (E J) :=
    lt_of_lt_of_le (H.trace_pos J) (first_le_weighted n (K / η) (E J)
      H.dimension_pos (div_nonneg H.K_nonneg hη.le) (H.coefficient_nonneg J))
  have hB : 0 < η + D / (m : ℝ) :=
    add_pos_of_pos_of_nonneg hη (div_nonneg hD (Nat.cast_nonneg m))
  rw [Real.rpow_def_of_pos (mul_pos H.C_pos hV), Real.rpow_def_of_pos hB,
    mul_assoc, ← Real.exp_add]
  have he : Real.log (C * weightedPotential n (K / η) (E J)) *
      (-1 / ((m + 1 : ℕ) : ℝ)) +
      Real.log (η + D / (m : ℝ)) * (-(m : ℝ) / ((m + 1 : ℕ) : ℝ)) =
      -(Real.log (C * weightedPotential n (K / η) (E J)) +
      (m : ℝ) * Real.log (η + D / (m : ℝ))) / ((m + 1 : ℕ) : ℝ) := by ring
  rw [he]
  exact hierarchy_finite_horizon H hδ J m hm η D hη hD hbudget

end BfgsVerification.QuantitativeGrowth
