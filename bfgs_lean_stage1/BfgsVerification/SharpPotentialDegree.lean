import BfgsVerification.Normalization

/-! The source's sharp polynomial degree for the actual finite principal potential. -/
noncomputable section
open scoped BigOperators Topology
open Filter
open BfgsVerification.ScalarHierarchy

namespace BfgsVerification.SharpPotentialDegree

/-- The actual polynomial obtained by expanding the finite weighted potential. -/
def potentialPolynomial (n : ℕ) (r : ℝ) (e : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range n, Polynomial.monomial j (r ^ j * e (j + 1))

theorem potentialPolynomial_eval (n : ℕ) (r t : ℝ) (e : ℕ → ℝ) :
    (potentialPolynomial n r e).eval t = weightedPotential n (r * t) e := by
  simp only [potentialPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial, weightedPotential]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

/-- The empty-dimensional case is also included: the polynomial is zero. -/
theorem potentialPolynomial_natDegree (n : ℕ) (r : ℝ) (e : ℕ → ℝ) :
    (potentialPolynomial n r e).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjn := Finset.mem_range.mp hj
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- The precise power is n-1, with no positive-dimension premise added. -/
theorem weightedPotential_mul_le_pred (n : ℕ) (r t : ℝ) (e : ℕ → ℝ)
    (hr : 0 ≤ r) (ht : 1 ≤ t) (he : ∀ j, 0 ≤ e j) :
    weightedPotential n (r * t) e ≤ weightedPotential n r e * t ^ (n - 1) := by
  unfold weightedPotential
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n - 1 := by have := Finset.mem_range.mp hj; omega
  have hp := pow_le_pow_right₀ ht hjn
  calc
    (r * t) ^ j * e (j + 1) = (r ^ j * e (j + 1)) * t ^ j := by
      rw [mul_pow]
      ring
    _ ≤ (r ^ j * e (j + 1)) * t ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg hr _) (he _))

/-- The optimized parameter a/t gives this actual polynomial, not a bound premise. -/
theorem optimized_potential_eq_polynomial (n : ℕ) (K a t : ℝ) (e : ℕ → ℝ) :
    weightedPotential n (K / (a / t)) e = (potentialPolynomial n (K / a) e).eval t := by
  rw [potentialPolynomial_eval]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Literal finite-horizon parameter: eta=D/[c(m-1)], with m at least two. -/
theorem principal_optimized_polynomial {n : ℕ} (H : Mat n) (K D c : ℝ) (m : ℕ) :
    weightedPotential n (K / (D / (c * ((m : ℝ) - 1)))) (principalSum H) =
      (potentialPolynomial n (K / (D / c)) (principalSum H)).eval ((m : ℝ) - 1) := by
  rw [← optimized_potential_eq_polynomial]
  rw [div_div]

/-- Source M149's sharp growth bound, with actual principal determinants. -/
theorem principal_optimized_bound {n : ℕ} (H : Mat n) (hH : H.PosSemidef)
    (K D c : ℝ) (hK : 0 ≤ K) (hD : 0 < D) (hc : 0 < c)
    (m : ℕ) (hm : 2 ≤ m) :
    weightedPotential n (K / (D / (c * ((m : ℝ) - 1)))) (principalSum H) ≤
      weightedPotential n (K / (D / c)) (principalSum H) * ((m : ℝ) - 1) ^ (n - 1) := by
  rw [principal_optimized_polynomial, potentialPolynomial_eval]
  apply weightedPotential_mul_le_pred
  · exact div_nonneg hK (div_pos hD hc).le
  · have hcast : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  · exact principalSum_nonneg hH

/-- The actual run supplies the PSD coefficients. The fixed tail is not bounded uniformly. -/
theorem run_optimized_bound {n : ℕ} (R : FullBFGSRun n) (G c : ℝ)
    (hc : 0 < c) (hd : Summable R.d) (J m : ℕ) (hm : 2 ≤ m) :
    let D := ∑' i : ℕ, R.d (J + i)
    let K := 4 * G ^ 2 / c ^ 2
    weightedPotential n (K / (D / (c * ((m : ℝ) - 1)))) (principalSum (R.H J)) ≤
      weightedPotential n (K / (D / c)) (principalSum (R.H J)) *
        ((m : ℝ) - 1) ^ (n - 1) := by
  dsimp only
  have htail : Summable (fun i => R.d (J + i)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff J).2 hd
  have hD : 0 < ∑' i : ℕ, R.d (J + i) :=
    (htail.tsum_pos (fun i => (R.d_pos (J + i)).le) 0 (R.d_pos (J + 0)))
  exact principal_optimized_bound (R.H J) (R.positive_definite J).posSemidef
    (4 * G ^ 2 / c ^ 2) _ c (by positivity) hD hc m hm

/-- The exact root limit used after the sharp degree bound, with the source's
horizon m and optimized scale proportional to m-1. -/
theorem shifted_potential_root_tendsto (n : ℕ) (hn : 0 < n) (r : ℝ)
    (hr : 0 ≤ r) (e : ℕ → ℝ) (he : ∀ j, 0 ≤ e j) (hfirst : 0 < e 1) :
    Tendsto (fun m : ℕ =>
      (weightedPotential n (r * ((m : ℝ) - 1)) e) ^ (1 / (m : ℝ)))
      atTop (𝓝 1) := by
  let A := weightedPotential n r e
  have hA : 0 < A := hfirst.trans_le (first_le_weighted n r e hn hr he)
  have hexp : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlo : Tendsto (fun m : ℕ => (e 1) ^ (1 / (m : ℝ))) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using
      (tendsto_const_nhds.rpow hexp (Or.inl hfirst.ne'))
  have hconst : Tendsto (fun m : ℕ => A ^ (1 / (m : ℝ))) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using
      (tendsto_const_nhds.rpow hexp (Or.inl hA.ne'))
  have hp : Tendsto (fun m : ℕ => (m : ℝ) ^ ((n - 1 : ℕ) / (m : ℝ)))
      atTop (𝓝 1) := by
    simpa only [one_mul, add_zero] using
      (tendsto_rpow_div_mul_add ((n - 1 : ℕ) : ℝ) 1 0 zero_ne_one).comp
        tendsto_natCast_atTop_atTop
  have hup := hconst.mul hp
  rw [one_mul] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_ge_atTop 2] with m hm
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    apply Real.rpow_le_rpow hfirst.le _ (by positivity)
    exact first_le_weighted n _ e hn (mul_nonneg hr (by linarith)) he
  · filter_upwards [eventually_ge_atTop 2] with m hm
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbound := weightedPotential_mul_le_pred n r ((m : ℝ) - 1) e hr
      (by linarith) he
    have hpowers : ((m : ℝ) - 1) ^ (n - 1) ≤ (m : ℝ) ^ (n - 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hbound' : weightedPotential n (r * ((m : ℝ) - 1)) e ≤ A * (m : ℝ) ^ (n - 1) :=
      hbound.trans (mul_le_mul_of_nonneg_left hpowers hA.le)
    have hh := Real.rpow_le_rpow (weighted_nonneg n _ e
      (mul_nonneg hr (by linarith)) he) hbound' (by positivity : 0 ≤ 1 / (m : ℝ))
    convert hh using 1
    rw [Real.mul_rpow hA.le (pow_nonneg (by linarith) _), ← Real.rpow_natCast,
      ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ m)]
    congr 2
    ring

/-- Actual run and actual summable tail: no assumed hierarchy or potential limit. -/
theorem run_optimized_root_tendsto {n : ℕ} (R : FullBFGSRun n) (G c : ℝ)
    (hc : 0 < c) (hd : Summable R.d) (J : ℕ) :
    let D := ∑' i : ℕ, R.d (J + i)
    let K := 4 * G ^ 2 / c ^ 2
    Tendsto (fun m : ℕ =>
      (weightedPotential n (K / (D / (c * ((m : ℝ) - 1))))
        (principalSum (R.H J))) ^ (1 / (m : ℝ))) atTop (𝓝 1) := by
  dsimp only
  have htail : Summable (fun i => R.d (J + i)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff J).2 hd
  have hD : 0 < ∑' i : ℕ, R.d (J + i) :=
    htail.tsum_pos (fun i => (R.d_pos (J + i)).le) 0 (R.d_pos (J + 0))
  have h := shifted_potential_root_tendsto n R.dimension_pos
    ((4 * G ^ 2 / c ^ 2) / ((∑' i : ℕ, R.d (J + i)) / c))
    (by positivity) (principalSum (R.H J))
    (principalSum_nonneg (R.positive_definite J).posSemidef)
    (principalSum_one_pos (R.positive_definite J) R.dimension_pos)
  convert h using 1
  funext m
  rw [principal_optimized_polynomial, potentialPolynomial_eval]

end BfgsVerification.SharpPotentialDegree
