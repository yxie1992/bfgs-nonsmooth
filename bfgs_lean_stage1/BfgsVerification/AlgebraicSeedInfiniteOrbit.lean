import BfgsVerification.AlgebraicSeedFiniteCycle
import BfgsVerification.ObjectiveRun
noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace BfgsVerification.SeedOrbit
open AlgebraicSeed SeedCycle

def orbitScale (k : ℕ) : ℝ := seedRatio^(period k)
def orbitPoint (k : ℕ) : Vec 2 := orbitScale k • point seedC seedD seedRatio (phase k)
def orbitMetric (k : ℕ) : Mat 2 := orbitScale k • metric seedC seedD (phase k)
def orbitGradient (k : ℕ) : Vec 2 := gradient seedC seedD (phase k)
def orbitLength (k : ℕ) : ℝ := length (phase k)

theorem orbitScale_pos (k : ℕ) : 0 < orbitScale k := pow_pos source_ratio_pos_lt_one.1 _
theorem orbitScale_le_one (k : ℕ) : orbitScale k ≤ 1 :=
  pow_le_one₀ source_ratio_pos_lt_one.1.le source_ratio_pos_lt_one.2.le

theorem orbit_next_phase (k : ℕ) : phase (k+1)=nextPhase (phase k) := by
  rcases phase_period_cases k with ⟨h0,h1,_⟩ | ⟨h0,h1,_⟩ | ⟨h0,h1,_⟩
  all_goals rw [h0,h1]; rfl

theorem orbit_step (k : ℕ) :
    orbitPoint (k+1)=orbitPoint k+bfgsStep (orbitMetric k) (orbitGradient k) (orbitLength k) := by
  rcases phase_period_cases k with ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩
  · simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,h0,h1,bfgsStep_scale_matrix,
      source_direction,← smul_add]
    change orbitScale (k+1) • point seedC seedD seedRatio 1=orbitScale k • trial seedC seedD seedRatio 0 (length 0)
    rw [phase_zero_step]
    simp only [orbitScale,hp]
  · simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,h0,h1,bfgsStep_scale_matrix,
      source_direction,← smul_add]
    change orbitScale (k+1) • point seedC seedD seedRatio 2=orbitScale k • trial seedC seedD seedRatio 1 (length 1)
    rw [phase_one_step]
    simp only [orbitScale,hp]
  · simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,h0,h1,bfgsStep_scale_matrix,
      source_direction,← smul_add]
    change orbitScale (k+1) • point seedC seedD seedRatio 0=orbitScale k • trial seedC seedD seedRatio 2 (length 2)
    rw [source_phase_two_step]
    simp only [orbitScale,hp,pow_succ,smul_smul]

theorem orbit_trial_step (k : ℕ) :
    orbitPoint (k+1)=orbitScale k • trial seedC seedD seedRatio (phase k) (length (phase k)) := by
  rw [orbit_step]
  simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,bfgsStep_scale_matrix,source_direction,← smul_add]
  rfl

theorem orbit_update (k : ℕ) :
    orbitMetric (k+1)=inverseBFGS (orbitMetric k)
      (bfgsStep (orbitMetric k) (orbitGradient k) (orbitLength k)) (orbitGradient (k+1)-orbitGradient k) := by
  have ht := (orbitScale_pos k).ne'
  rcases phase_period_cases k with ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩ | ⟨h0,h1,hp⟩
  · simp only [orbitMetric,orbitGradient,orbitLength,h0,h1,bfgsStep_scale_matrix,inverseBFGS_scale _ _ _ ht]
    change orbitScale (k+1) • metric seedC seedD 1=orbitScale k • update (metric seedC seedD 0) (gradient seedC seedD 0) (gradient seedC seedD 1) (length 0)
    rw [source_metric_zero_update]
    simp only [orbitScale,hp]
  · simp only [orbitMetric,orbitGradient,orbitLength,h0,h1,bfgsStep_scale_matrix,inverseBFGS_scale _ _ _ ht]
    change orbitScale (k+1) • metric seedC seedD 2=orbitScale k • update (metric seedC seedD 1) (gradient seedC seedD 1) (gradient seedC seedD 2) (length 1)
    rw [source_metric_one_update]
    simp only [orbitScale,hp]
  · simp only [orbitMetric,orbitGradient,orbitLength,h0,h1,bfgsStep_scale_matrix,inverseBFGS_scale _ _ _ ht]
    change orbitScale (k+1) • metric seedC seedD 0=orbitScale k • update (metric seedC seedD 2) (gradient seedC seedD 2) (gradient seedC seedD 0) (length 2)
    rw [source_metric_two_update]
    simp only [orbitScale,hp,pow_succ,smul_smul]

theorem orbit_hasGradient (k : ℕ) :
    HasFDerivAt (objective seedC seedD) (gradientFunctional (orbitGradient k)) (orbitPoint k) :=
  hasGradient_of_active ((source_base_certificate (phase k)).active.scale (orbitScale_pos k))

theorem orbit_strict_accept {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) :
    objective seedC seedD (orbitPoint (k+1)) < objective seedC seedD (orbitPoint k)+
      c₁*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) (orbitLength k)) ∧
    c₂*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) (orbitLength k)) <
      dot (orbitGradient (k+1)) (bfgsStep (orbitMetric k) (orbitGradient k) (orbitLength k)) := by
  obtain ⟨ha,hw⟩ := source_accepted_inequalities hc₁ hc₁' hc₂ (phase k)
  have ht := orbitScale_pos k
  constructor
  · rw [orbit_trial_step]
    rw [objective_scale_at_active (source_accepted_certificate (phase k)).active ht]
    rw [orbitPoint,objective_scale_at_active (source_base_certificate (phase k)).active ht]
    simp only [orbitGradient,orbitMetric,orbitLength,bfgsStep_scale_matrix,dot_smul_right]
    convert mul_lt_mul_of_pos_left ha ht using 1 <;> ring
  · simp only [orbitGradient,orbitMetric,orbitLength,bfgsStep_scale_matrix,dot_smul_right,orbit_next_phase]
    convert mul_lt_mul_of_pos_left hw ht using 1 <;> ring

def run (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    AdmissibleBFGSRun 2 (objective seedC seedD) where
  convex := (family seedC seedD).objective_convex
  x := orbitPoint
  H := orbitMetric
  g := orbitGradient
  α := orbitLength
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := by
    change ((1:ℝ) • (1:Mat 2)).PosDef
    simpa using (Matrix.PosDef.one : (1:Mat 2).PosDef)
  alpha_pos k := source_length_pos (phase k)
  gradient_nonzero k := source_gradient_nonzero (phase k)
  hasGradient := orbit_hasGradient
  step := orbit_step
  update := orbit_update
  armijo k := (orbit_strict_accept hc₁ hc₁' (hc₁.trans hc) k).1.le
  weak_wolfe k := (orbit_strict_accept hc₁ hc₁' (hc₁.trans hc) k).2.le

end BfgsVerification.SeedOrbit
