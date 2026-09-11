import BfgsVerification.ParabolicEnvelopeScale

noncomputable section
open scoped Topology
open Set BfgsVerification

/- Q.7/Q.16: every original family has actual constants; no envelope witness,
retained-index premise, branch nonredundancy, or nonzero normal slopes are assumed. -/
example {m : ℕ} (P : Parabolic.Family m) :
    ∃ k : Fin m → ℝ, ∃ C : ℝ, 0 < C ∧
      (∀ (i j : Fin m) (x : Vec 2), P.Active i x → P.Active j x → 0 < P.objective x →
        P.a i * (x 0)^2 / (2 * P.objective x) + k i =
          P.a j * (x 0)^2 / (2 * P.objective x) + k j) ∧
      (∀ (i j : Fin m) (z : Vec 2), P.Active j z → 0 < P.objective z →
        |(P.a j - P.a i) * (z 0)^2 / (2 * P.objective z) + k j - k i| ≤
          C * (P.objective z - P.branch i z) / P.objective z) := by
  obtain ⟨C, hC, hb⟩ := P.exists_calibration_deficit_bound
  refine ⟨P.calibration, C, hC, ?_, ?_⟩
  · intro i j x hi hj hx
    exact P.calibration_active_eq hi hj hx
  · exact hb

/- Q.8: the same original family has one positive bounded continuous field
with exactly the displayed formula at every positive-level active branch. -/
example {m : ℕ} (P : Parabolic.Family m) :
    ∃ θ : Vec 2 → ℝ, ∃ k : Fin m → ℝ, ∃ θmin θmax : ℝ,
      0 < θmin ∧ 0 < θmax ∧
      ContinuousOn θ {x | 0 < P.objective x} ∧
      (∀ x, 0 < P.objective x → θmin ≤ θ x ∧ θ x ≤ θmax) ∧
      ∀ (i : Fin m) (x : Vec 2), P.Active i x → 0 < P.objective x →
        θ x = Real.exp (P.a i * (x 0)^2 / (2 * P.objective x) + k i) := by
  obtain ⟨θmin, θmax, hmin, hmax, hb⟩ := P.calibratedScale_uniform_bounds
  exact ⟨P.calibratedScale, P.calibration, θmin, θmax, hmin, hmax,
    P.calibratedScale_continuousOn, hb, fun _ _ hi hx => P.calibratedScale_eq_active hi hx⟩

#check @Parabolic.Family.calibration_interface_identity
#check @Parabolic.Family.active_retained_representative
#check @Parabolic.Family.exists_calibration_deficit_bound
#check @Parabolic.Family.calibratedScale_uniform_bounds
