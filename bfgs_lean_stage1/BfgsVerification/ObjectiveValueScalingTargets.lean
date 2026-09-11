import BfgsVerification.ObjectiveValueScaling

noncomputable section
namespace BfgsVerification

/-- Positive changes of objective units and additive constants preserve actual
unmodified full BFGS, including both line-search constants and the full matrices. -/
def ObjectiveValueScalingTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (a b : ℝ), 0 < a →
    ∀ R : AdmissibleBFGSRun n F,
    ∃ S : AdmissibleBFGSRun n (fun x => a * F x + b),
      S.c₁ = R.c₁ ∧ S.c₂ = R.c₂ ∧
      ∀ k : ℕ, S.x k = R.x k ∧ S.H k = a⁻¹ • R.H k ∧
        S.g k = a • R.g k ∧ S.α k = R.α k ∧
        S.d k = a * R.d k ∧ S.curvature k = a * R.curvature k

theorem objectiveValueScaling : ObjectiveValueScalingTarget := by
  intro n F a b ha R
  refine ⟨ObjectiveValueScale.run a b ha R, rfl, rfl, ?_⟩
  intro k
  exact ⟨rfl, rfl, rfl, rfl, ObjectiveValueScale.run_d a b ha R k,
    ObjectiveValueScale.run_curvature a b ha R k⟩

end BfgsVerification
