import BfgsVerification.Homogeneous

/-! Module H.A for actual infinite full-BFGS runs. Global gradient bounds are
derived from homogeneity; there are no compactness or matrix-boundedness inputs.
The finite-limit branch uses the already verified actual-matrix reciprocal theorem. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Homogeneity makes the actual reference-zero corrections summable whenever
the actual predicted decreases are summable. -/
theorem homogeneous_corrections_summable (hF : Homogeneous.PositiveDegreeOne F)
    (hs : Summable R.d) : Summable (R.referenceCorrection 0) :=
  Summable.of_nonneg_of_le (R.referenceCorrection_nonneg 0)
    (R.homogeneous_referenceCorrection_le_d hF) hs

theorem homogeneous_correction_ratio_zero (hF : Homogeneous.PositiveDegreeOne F)
    (hs : Summable R.d)
    (hS : Tendsto (fun N => ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop) :
    Tendsto (fun N => (∑ k ∈ Finset.range N, R.referenceCorrection 0 k) /
      (∑ k ∈ Finset.range N, (R.q k)⁻¹)) atTop (𝓝 0) := by
  have hsR := R.homogeneous_corrections_summable hF hs
  apply squeeze_zero _ _ (hS.const_div_atTop (∑' k, R.referenceCorrection 0 k))
  · intro N
    exact div_nonneg (Finset.sum_nonneg (fun k _ => R.referenceCorrection_nonneg 0 k))
      (Finset.sum_nonneg (fun k _ => inv_nonneg.mpr (R.q_pos k).le))
  · intro N
    exact div_le_div_of_nonneg_right
      (hsR.sum_le_tsum _ (fun k _ => R.referenceCorrection_nonneg 0 k))
      (Finset.sum_nonneg (fun k _ => inv_nonneg.mpr (R.q_pos k).le))

/-- H.A's finite-value branch: any finite limiting objective value must be zero.
No convergence or boundedness of the points, steps, lengths, or matrices is assumed. -/
theorem homogeneous_finite_value_limit_zero (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) : L = 0 := by
  by_contra hL
  have habs : 0 < |L| := abs_pos.mpr hL
  have hev : ∀ᶠ k in atTop, |L| / 2 ≤ |F (R.x k)| :=
    (hlim.abs.eventually (lt_mem_nhds (by linarith : |L| / 2 < |L|))).mono (fun _ h => h.le)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hev
  let Q := R.shift J
  have hlimQ : Tendsto (fun k => F (Q.x k)) atTop (𝓝 L) := by
    simpa only [Q, shift, Nat.add_comm] using hlim.comp (tendsto_add_atTop_nat J)
  obtain ⟨G, hG, hg⟩ := Q.homogeneous_global_gradient_bound hF
  have hgrowth := objectiveGrowth_of_value_limit Q G L hG hg hlimQ
  have hS := EnergyBudget.tendsto_atTop_of_superquadratic hgrowth.2.2.2
  have hzero : Tendsto (fun _k : ℕ => |L| / 2) atTop (𝓝 0) := by
    apply EnergyBudget.energy_gap_tendsto_zero (Q.referenceEnergy_nonneg 0) Q.q_pos
      (fun _ => (half_pos habs).le) antitone_const
      (fun k => hJ (J + k) (Nat.le_add_right J k))
      (fun k => by simpa only [sq_abs] using Q.homogeneous_energy_identity hF k)
      hS (Q.homogeneous_correction_ratio_zero hF hgrowth.1 hS)
  have heq : |L| / 2 = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  linarith

/-- Module H.A: unconditional objective-value dichotomy in arbitrary dimension. -/
theorem homogeneous_value_dichotomy (hF : Homogeneous.PositiveDegreeOne F) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∨
      Tendsto (fun k => F (R.x k)) atTop atBot := by
  by_cases hb : BddBelow (Set.range (fun k => F (R.x k)))
  · have hlim := tendsto_atTop_ciInf R.objective_antitone hb
    have hzero := R.homogeneous_finite_value_limit_zero hF _ hlim
    left
    simpa only [hzero] using hlim
  · right
    apply tendsto_atBot.2
    intro b
    have hex : ∃ k, F (R.x k) < b := by
      by_contra hn
      push_neg at hn
      apply hb
      exact ⟨b, by rintro y ⟨k, rfl⟩; exact hn k⟩
    obtain ⟨k, hk⟩ := hex
    exact eventually_atTop.2 ⟨k, fun i hi => (R.objective_antitone hi).trans hk.le⟩

/-- A lower bound only along the accepted run selects the zero-value branch. -/
theorem homogeneous_value_zero_of_lower_bound (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hLower : ∀ k, L ≤ F (R.x k)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) := by
  have hb : BddBelow (Set.range (fun k => F (R.x k))) :=
    ⟨L, by rintro y ⟨k, rfl⟩; exact hLower k⟩
  have hlim := tendsto_atTop_ciInf R.objective_antitone hb
  have hzero := R.homogeneous_finite_value_limit_zero hF _ hlim
  simpa only [hzero] using hlim

/-- Every value on the finite branch is strictly positive. -/
theorem homogeneous_finite_branch_positive (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) (k : ℕ) :
    0 < F (R.x k) := by
  have hzero := R.homogeneous_finite_value_limit_zero hF L hlim
  have hnext := R.objective_antitone.le_of_tendsto hlim (k + 1)
  rw [hzero] at hnext
  exact hnext.trans_lt (R.objective_strict_decrease k)

/-- A nonpositive accepted objective value selects escape to minus infinity. -/
theorem homogeneous_nonpositive_forces_escape (hF : Homogeneous.PositiveDegreeOne F)
    (k : ℕ) (hk : F (R.x k) ≤ 0) : Tendsto (fun j => F (R.x j)) atTop atBot := by
  rcases R.homogeneous_value_dichotomy hF with hzero | hescape
  · exact False.elim ((not_lt_of_ge hk) (R.homogeneous_finite_branch_positive hF 0 hzero k))
  · exact hescape

end BfgsVerification.AdmissibleBFGSRun
