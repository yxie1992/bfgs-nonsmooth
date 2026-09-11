import BfgsVerification.LNormalizedOracle
import BfgsVerification.ObjectiveRun

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LFlatten
open SeedOrbit SeedCycle LNormalizedReturn LNormalizedOracle DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Conditional finite-step interface, discharged by the actual normalized
orbit. No convergence or abstract gradient-oracle field is included. -/
structure Data (μ c₁ c₂ : ℝ) where
  state : ℕ → State
  scale_pos : ∀ m, 0<scale (state m)
  conditions : ∀ m, Conditions μ c₁ c₂ (state m)
  next : ∀ m, state (m+1)=returnMap μ (state m)

namespace Data
variable {μ c₁ c₂ : ℝ}

def x (D : Data μ c₁ c₂) (k : ℕ) : Vec 2 := physicalPoint μ (D.state (period k)) (phase k)
def H (D : Data μ c₁ c₂) (k : ℕ) : Mat 2 := physicalMetric μ (D.state (period k)) (phase k)
def g (D : Data μ c₁ c₂) (k : ℕ) : Vec 2 := coordinateGradient (LQuadraticSeed.objective μ) (D.x k)
def alpha (_D : Data μ c₁ c₂) (k : ℕ) : ℝ := length (phase k)

theorem next_point (D : Data μ c₁ c₂) (k : ℕ) :
    D.x (k+1)=scale (D.state (period k)) •
      (internal μ (D.state (period k)) ((phase k).val+1)).1 := by
  rcases phase_period_cases k with ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩
  · simp only [x,h1,hp,h0]; rfl
  · simp only [x,h1,hp,h0]; rfl
  · simp only [x,h1,hp,h0,D.next]
    exact normalization_preserves_point μ (D.state (period k)) (D.conditions (period k)).regular.2.1.ne'

theorem next_metric (D : Data μ c₁ c₂) (k : ℕ) :
    D.H (k+1)=scale (D.state (period k)) •
      (internal μ (D.state (period k)) ((phase k).val+1)).2 := by
  rcases phase_period_cases k with ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩
  · simp only [H,h1,hp,h0]; rfl
  · simp only [H,h1,hp,h0]; rfl
  · simp only [H,h1,hp,h0,D.next]
    exact normalization_preserves_metric μ (D.state (period k)) (D.conditions (period k)).regular.2.1.ne'

theorem gradient_eq (D : Data μ c₁ c₂) (k : ℕ) :
    D.g k=phaseGradient μ (D.state (period k)) (phase k) :=
  actual_coordinateGradient ((D.conditions (period k)).phase_hasGradient (D.scale_pos (period k)) (phase k))

theorem hasGradient (D : Data μ c₁ c₂) (k : ℕ) :
    HasFDerivAt (LQuadraticSeed.objective μ) (gradientFunctional (D.g k)) (D.x k) := by
  rw [D.gradient_eq]
  exact (D.conditions (period k)).phase_hasGradient (D.scale_pos (period k)) (phase k)

theorem positive_metric (D : Data μ c₁ c₂) (k : ℕ) : (D.H k).PosDef :=
  (D.conditions (period k)).physicalMetric_posDef (D.scale_pos (period k)) (phase k)

theorem value_positive (D : Data μ c₁ c₂) (k : ℕ) : 0<LQuadraticSeed.objective μ (D.x k) :=
  (D.conditions (period k)).physical_phase_positive (D.scale_pos (period k)) (phase k)

theorem gradient_nonzero (D : Data μ c₁ c₂) (hμ : 0≤μ) (k : ℕ) : D.g k≠0 := by
  intro hz
  have hh := convex_supporting_inequality (LQuadraticSeed.objective_convex hμ) (D.hasGradient k) 0
  rw [hz,LQuadraticSeed.objective_zero] at hh
  have hp := D.value_positive k
  norm_num [dot] at hh
  linarith

theorem point_step (D : Data μ c₁ c₂) (k : ℕ) :
    D.x (k+1)=D.x k+bfgsStep (D.H k) (D.g k) (D.alpha k) := by
  rw [D.next_point]
  exact (D.conditions (period k)).actual_point_update (D.scale_pos (period k)) (phase k)

theorem metric_update (D : Data μ c₁ c₂) (k : ℕ) :
    D.H (k+1)=inverseBFGS (D.H k) (bfgsStep (D.H k) (D.g k) (D.alpha k)) (D.g (k+1)-D.g k) := by
  have hm := (D.conditions (period k)).actual_matrix_update (D.scale_pos (period k)) (phase k)
  rw [← D.next_point,← D.next_metric] at hm
  change inverseBFGS (D.H k) (D.x (k+1)-D.x k) (D.g (k+1)-D.g k)=D.H (k+1) at hm
  have hs : D.x (k+1)-D.x k=bfgsStep (D.H k) (D.g k) (D.alpha k) := by
    rw [D.point_step,add_sub_cancel_left]
  rw [hs] at hm
  exact hm.symm

end Data
end BfgsVerification.LFlatten
