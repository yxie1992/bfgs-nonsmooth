import BfgsVerification.ObjectiveEndToEnd
import BfgsVerification.HessianUpdate
import BfgsVerification.EnergyIdentities
import BfgsVerification.EnergyBudget

/-! Fixed-reference and moving-frame energies of the actual full-BFGS run.
The convergence criteria keep the correction-budget assumption explicit. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

def hessian (k : ℕ) : Mat n := (R.H k)⁻¹
def displacement (k : ℕ) : Vec n := bfgsStep (R.H k) (R.g k) (R.α k)
def gradientChange (k : ℕ) : Vec n := R.g (k + 1) - R.g k
def curvature (k : ℕ) : ℝ := dot (R.gradientChange k) (R.displacement k)
def referenceEnergy (xstar : Vec n) (k : ℕ) : ℝ :=
  metricEnergy (R.hessian k) (R.x k - xstar)
def referencePairing (xstar : Vec n) (k : ℕ) : ℝ := dot (R.g k) (R.x k - xstar)
def referenceCorrection (xstar : Vec n) (k : ℕ) : ℝ :=
  (dot (R.gradientChange k) (R.x (k + 1) - xstar)) ^ 2 / R.curvature k

theorem hessian_posDef (k : ℕ) : (R.hessian k).PosDef := (R.positive_definite k).inv

theorem hessian_update (k : ℕ) :
    R.hessian (k + 1) = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
      (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) := by
  unfold hessian
  rw [R.update k]
  exact hessianUpdate (R.positive_definite k) (R.gradient_nonzero k) _
    (R.alpha_pos k) (R.curvature_pos k)

theorem annihilated_hessian_posSemidef (k : ℕ) :
    (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)).PosSemidef :=
  annihilatedMatrix_posSemidef (R.positive_definite k) (R.gradient_nonzero k)

theorem annihilated_hessian_mul_displacement (k : ℕ) :
    (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)).mulVec (R.displacement k) = 0 :=
  annihilatedMatrix_mul_step (R.positive_definite k) (R.gradient_nonzero k) _

theorem annihilated_hessian_isSymm (k : ℕ) :
    (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)).IsSymm := by
  simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (R.annihilated_hessian_posSemidef k).isHermitian

theorem referenceEnergy_nonneg (xstar : Vec n) (k : ℕ) :
    0 ≤ R.referenceEnergy xstar k := by
  simpa only [referenceEnergy, metricEnergy, dot, dotProduct, star_trivial] using
    (R.hessian_posDef k).posSemidef.2 (R.x k - xstar)

theorem referenceCorrection_nonneg (xstar : Vec n) (k : ℕ) :
    0 ≤ R.referenceCorrection xstar k :=
  div_nonneg (sq_nonneg _) (R.curvature_pos k).le

/-- Source M:fixedenergy for the actual inverse of each full-BFGS matrix. -/
theorem fixed_reference_energy (xstar : Vec n) (k : ℕ) :
    R.referenceEnergy xstar (k + 1) = R.referenceEnergy xstar k -
      (R.referencePairing xstar k) ^ 2 / R.q k + R.referenceCorrection xstar k := by
  have hx : R.x (k + 1) - xstar = (R.x k - xstar) + R.displacement k := by
    rw [R.step k]
    change R.x k + R.displacement k - xstar = _
    abel
  unfold referenceEnergy referencePairing referenceCorrection
  rw [R.hessian_update k, hx]
  exact EnergyIdentities.fixed_reference _ _ _ _ _ _ _
    (R.annihilated_hessian_isSymm k) (R.annihilated_hessian_mul_displacement k)

theorem gap_le_referencePairing (xstar : Vec n) (k : ℕ) :
    F (R.x k) - F xstar ≤ R.referencePairing xstar k := by
  have h := convex_supporting_inequality R.convex (R.hasGradient k) xstar
  have hx : xstar - R.x k = -(R.x k - xstar) := by abel
  rw [hx] at h
  change dot (R.g k) (-(R.x k - xstar)) ≤ _ at h
  have hn : dot (R.g k) (-(R.x k - xstar)) = -R.referencePairing xstar k := by
    change (R.g k) ⬝ᵥ (-(R.x k - xstar)) = -((R.g k) ⬝ᵥ (R.x k - xstar))
    exact dotProduct_neg _ _
  rw [hn] at h
  linarith

theorem gap_antitone (xstar : Vec n) : Antitone (fun k => F (R.x k) - F xstar) := by
  intro i j hij
  exact sub_le_sub_right (R.objective_antitone hij) _

/-- Source M:energybound, including the actual cumulative correction. -/
theorem fixed_reference_energy_bound (xstar : Vec n)
    (hmin : ∀ z, F xstar ≤ F z) (N : ℕ) :
    (F (R.x N) - F xstar) ^ 2 * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      R.referenceEnergy xstar 0 + ∑ k ∈ Finset.range N, R.referenceCorrection xstar k :=
  EnergyBudget.gap_sq_mul_reciprocal_sum_le (R.referenceEnergy_nonneg xstar) R.q_pos
    (fun k => sub_nonneg.mpr (hmin (R.x k))) (R.gap_antitone xstar)
    (R.gap_le_referencePairing xstar) (R.fixed_reference_energy xstar) N

/-- The actual moving-frame identity allows rectangular, rank-deficient frames
and singular transport matrices. -/
theorem moving_frame_energy {r : ℕ} (k : ℕ)
    (V W : Matrix (Fin n) (Fin r) ℝ) (T : Mat r) (b : Vec r)
    (hW : W = V * T + EnergyIdentities.rectOuter (R.displacement k) b) :
    metricGram (R.hessian (k + 1)) W =
      Tᵀ * (metricGram (R.hessian k) V -
        (R.q k)⁻¹ • outer (Vᵀ.mulVec (R.g k)) (Vᵀ.mulVec (R.g k))) * T +
      (R.curvature k)⁻¹ • outer (Wᵀ.mulVec (R.gradientChange k))
        (Wᵀ.mulVec (R.gradientChange k)) := by
  rw [R.hessian_update k]
  exact EnergyIdentities.moving_frame _ _ _ _ _ _ (R.annihilated_hessian_isSymm k)
    (R.annihilated_hessian_mul_displacement k) V W T b hW

/-- A proved trajectory criterion: the correction ratio remains an explicit
hypothesis, rather than being inferred from finite convexity. -/
theorem objective_tendsto_min_of_negligible_corrections (xstar : Vec n)
    (hmin : ∀ z, F xstar ≤ F z) (G : ℝ) (hG : 0 < G)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hcor : Tendsto (fun N => (∑ k ∈ Finset.range N, R.referenceCorrection xstar k) /
      (∑ k ∈ Finset.range N, (R.q k)⁻¹)) atTop (𝓝 0)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
  have hsuper := (objectiveLowerBoundGrowth n F R G (F xstar) hG hg
    (fun k => hmin (R.x k))).2.2.2
  have hgap := EnergyBudget.energy_gap_tendsto_zero (R.referenceEnergy_nonneg xstar)
    R.q_pos (fun k => sub_nonneg.mpr (hmin (R.x k))) (R.gap_antitone xstar)
    (R.gap_le_referencePairing xstar) (R.fixed_reference_energy xstar)
    (EnergyBudget.tendsto_atTop_of_superquadratic hsuper) hcor
  simpa only [sub_add_cancel, zero_add] using hgap.add_const (F xstar)

/-- Source M's O(N²) cumulative-correction criterion, using the verified actual
matrix superquadratic theorem and the actual Hessian energy identity. -/
theorem objective_tendsto_min_of_quadratic_corrections (xstar : Vec n)
    (hmin : ∀ z, F xstar ≤ F z) (G : ℝ) (hG : 0 < G)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (C : ℝ)
    (hcor : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, R.referenceCorrection xstar k) ≤ C * (N : ℝ) ^ 2) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
  have hsuper := (objectiveLowerBoundGrowth n F R G (F xstar) hG hg
    (fun k => hmin (R.x k))).2.2.2
  have hgap := EnergyBudget.energy_gap_tendsto_zero_of_quadratic_corrections
    (R.referenceEnergy_nonneg xstar) R.q_pos
    (fun k => sub_nonneg.mpr (hmin (R.x k))) (R.gap_antitone xstar)
    (R.gap_le_referencePairing xstar) (R.fixed_reference_energy xstar) hsuper hcor
  simpa only [sub_add_cancel, zero_add] using hgap.add_const (F xstar)

theorem compact_objective_tendsto_min_of_quadratic_corrections (xstar : Vec n)
    (hmin : ∀ z, F xstar ≤ F z) (hK : IsCompact R.initialSublevel) (C : ℝ)
    (hcor : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, R.referenceCorrection xstar k) ≤ C * (N : ℝ) ^ 2) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  exact R.objective_tendsto_min_of_quadratic_corrections xstar hmin G hG hg C hcor

end BfgsVerification.AdmissibleBFGSRun
