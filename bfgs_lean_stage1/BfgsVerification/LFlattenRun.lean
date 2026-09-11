import BfgsVerification.LFlatten

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LFlatten.Data
open SeedOrbit SeedCycle LNormalizedReturn LNormalizedOracle DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {μ c₁ c₂ : ℝ}

theorem alpha_step (D : Data μ c₁ c₂) (k : ℕ) :
    bfgsStep (D.H k) (D.g k) (D.alpha k)=D.alpha k • bfgsStep (D.H k) (D.g k) 1 := by
  simpa only [mul_one] using bfgsStep_scale_alpha (D.H k) (D.g k) 1 (D.alpha k)

theorem trial_endpoint (D : Data μ c₁ c₂) (k : ℕ) :
    D.x (k+1)=D.x k+D.alpha k • bfgsStep (D.H k) (D.g k) 1 := by
  rw [D.point_step,D.alpha_step]

theorem accepted_search_conditions (D : Data μ c₁ c₂) (k : ℕ) :
    Armijo (LQuadraticSeed.objective μ) (D.x k) (bfgsStep (D.H k) (D.g k) 1) (D.g k) c₁ (D.alpha k) ∧
    Wolfe (LQuadraticSeed.objective μ) (D.x k) (bfgsStep (D.H k) (D.g k) 1) (D.g k) c₂ (D.alpha k) := by
  have hs := acceptedQuery_spec (phase k)
  have ha := (D.conditions (period k)).physical_accept (D.scale_pos (period k)) (acceptedQuery (phase k)) hs.2.2.2
  rw [hs.1,hs.2.1] at ha
  rw [D.gradient_eq]
  exact ha

theorem strict_accept (D : Data μ c₁ c₂) (k : ℕ) :
    LQuadraticSeed.objective μ (D.x (k+1)) < LQuadraticSeed.objective μ (D.x k)+
      c₁*dot (D.g k) (bfgsStep (D.H k) (D.g k) (D.alpha k)) ∧
    c₂*dot (D.g k) (bfgsStep (D.H k) (D.g k) (D.alpha k)) <
      dot (D.g (k+1)) (bfgsStep (D.H k) (D.g k) (D.alpha k)) := by
  obtain ⟨ha,hw⟩ := D.accepted_search_conditions k
  unfold Armijo at ha
  unfold Wolfe at hw
  rw [← D.trial_endpoint] at ha hw
  rw [D.alpha_step]
  constructor
  · simpa only [dot_smul_right,mul_assoc] using ha
  · have hh := mul_lt_mul_of_pos_left hw (source_length_pos (phase k))
    change D.alpha k*(c₂*dot (D.g k) (bfgsStep (D.H k) (D.g k) 1)) <
      D.alpha k*dot (D.g (k+1)) (bfgsStep (D.H k) (D.g k) 1) at hh
    rw [dot_smul_right,dot_smul_right]
    nlinarith [hh]

def run (D : Data μ c₁ c₂) (hμ : 0≤μ) (hc₁ : 0<c₁) (hc : c₁<c₂) (hc₂ : c₂<1) :
    AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ) where
  convex := LQuadraticSeed.objective_convex hμ
  x := D.x
  H := D.H
  g := D.g
  α := D.alpha
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := D.positive_metric 0
  alpha_pos k := source_length_pos (phase k)
  gradient_nonzero := D.gradient_nonzero hμ
  hasGradient := D.hasGradient
  step := D.point_step
  update := D.metric_update
  armijo k := (D.strict_accept k).1.le
  weak_wolfe k := (D.strict_accept k).2.le

theorem actual_search (D : Data μ c₁ c₂) (k : ℕ) :
    fromMetric (LQuadraticSeed.objective μ) (D.x k) (D.H k) c₁ c₂ 5=
      (some (D.alpha k),trialHistory (phase k)) :=
  (D.conditions (period k)).fromMetric_search (D.scale_pos (period k)) (phase k)

theorem all_trial_derivatives (D : Data μ c₁ c₂) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    HasFDerivAt (LQuadraticSeed.objective μ)
      (gradientFunctional (trialGradient μ (D.state (period k)) (phase k) (trialLength q) (trialActive q)))
      (D.x k+trialLength q • bfgsStep (D.H k) (D.g k) 1) := by
  rw [D.gradient_eq]
  change HasFDerivAt _ _ (physicalPoint μ (D.state (period k)) (phase k)+
    trialLength q • bfgsStep (physicalMetric μ (D.state (period k)) (phase k))
      (phaseGradient μ (D.state (period k)) (phase k)) 1)
  rw [physical_trial]
  simpa only [hq] using (D.conditions (period k)).trial_hasGradient (D.scale_pos (period k)) q

theorem all_trial_values_positive (D : Data μ c₁ c₂) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    0<LQuadraticSeed.objective μ (D.x k+trialLength q • bfgsStep (D.H k) (D.g k) 1) := by
  rw [D.gradient_eq]
  change 0<LQuadraticSeed.objective μ (physicalPoint μ (D.state (period k)) (phase k)+
    trialLength q • bfgsStep (physicalMetric μ (D.state (period k)) (phase k))
      (phaseGradient μ (D.state (period k)) (phase k)) 1)
  rw [physical_trial]
  simpa only [hq] using (D.conditions (period k)).physical_trial_positive (D.scale_pos (period k)) q

end BfgsVerification.LFlatten.Data
