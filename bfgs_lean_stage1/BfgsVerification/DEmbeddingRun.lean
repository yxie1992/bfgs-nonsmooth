import BfgsVerification.DEmbeddingOracle
import BfgsVerification.SeedEmbeddingSearch

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric DeterministicLineSearch

def run {n : ℕ} (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) : AdmissibleBFGSRun 2 objective :=
  SeedEmbedding.run (actualData hn) (sq_pos_of_pos (scale_pos n)) c₁ c₂ hc₁ hc₁' hc hc₂

theorem center_value (n : ℕ) : objective (center n)=(scale n)^3 := by
  have he := local_cone n (h := 0) (fun j => by simpa [dot] using (half_pos (scale_pos n)).le)
  have hz : SeedOrbit.objective seedC seedD 0=0 := by
    unfold SeedOrbit.objective MaxAffine.Family.objective
    simp [family, MaxAffine.Family.branch, dot]
  simpa only [add_zero, hz, mul_zero] using he

theorem center_positive (n : ℕ) : 0<objective (center n) := by
  rw [center_value]
  exact pow_pos (scale_pos n) 3

theorem center_ne_zero (n : ℕ) : center n≠0 := by
  intro he
  have hp := center_positive n
  rw [he, objective_zero] at hp
  exact (lt_irrefl 0) hp

theorem center_nonstationary (n : ℕ) :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential objective (center n) := by
  intro hs
  have hh := hs 0
  rw [objective_zero] at hh
  norm_num [dot] at hh
  linarith [center_positive n]

theorem run_initial_matrix {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) : (run hn c₁ c₂ hc₁ hc₁' hc hc₂).H 0=1 := by
  change (1 : ℝ) • (1 : Mat 2)=1
  simp

theorem run_point_tendsto {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    Tendsto (run hn c₁ c₂ hc₁ hc₁' hc hc₂).x atTop (𝓝 (center n)) :=
  SeedEmbedding.point_tendsto (center n) ((scale n)^2)

theorem run_value_tendsto {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    Tendsto (fun k => objective ((run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)) atTop (𝓝 (objective (center n))) := by
  rw [center_value]
  exact SeedEmbedding.values_tendsto (actualData hn)

theorem run_value_above_center {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) :
    objective (center n)<objective ((run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k) := by
  change objective (center n)<objective (SeedEmbedding.point (center n) ((scale n)^2) k)
  rw [(actualData hn).values, center_value]
  exact lt_add_of_pos_right _ (mul_pos (sq_pos_of_pos (sq_pos_of_pos (scale_pos n))) (orbit_value_pos k))

theorem run_value_strict_decrease {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) :
    objective ((run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (k+1))<objective ((run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k) := by
  let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
  have he := R.armijo_decrease k
  have hp := mul_pos R.c₁_pos (R.d_pos k)
  dsimp only [R] at he hp
  linarith

theorem run_search {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) :
    let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
    fromMetric objective (R.x k) (R.H k) c₁ c₂ 5=(some (R.α k),trialHistory (phase k)) :=
  SeedEmbedding.fromMetric_exact (actualOracleData hn) (sq_pos_of_pos (scale_pos n))
    hc₁ hc₁' (hc₁.trans hc) k

theorem run_all_trials_differentiable {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
    HasFDerivAt objective (gradientFunctional ((scale n)^2 • SeedOrbit.gradient seedC seedD (trialActive q)))
      (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) := by
  change HasFDerivAt objective _ (SeedEmbedding.point (center n) ((scale n)^2) k+
    trialLength q • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale n)^2) k) 1)
  rw [SeedEmbedding.translated_trial]
  exact (actualOracleData hn).trial_derivatives k q hq

theorem run_phase_parameters {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (m : ℕ) (j : Fin 3) :
    let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
    R.x (3*m+j.val)=center n+(scale n)^2 • (seedRatio^m • SeedOrbit.point seedC seedD seedRatio j) ∧
      R.H (3*m+j.val)=seedRatio^m • metric seedC seedD j ∧
      R.g (3*m+j.val)=(scale n)^2 • SeedOrbit.gradient seedC seedD j ∧
      R.α (3*m+j.val)=length j := by
  obtain ⟨hx,hH,hg,ha⟩ := orbit_phase_parameters m j
  change center n+(scale n)^2 • orbitPoint (3*m+j.val)=_ ∧
    orbitMetric (3*m+j.val)=_ ∧ (scale n)^2 • orbitGradient (3*m+j.val)=_ ∧ orbitLength (3*m+j.val)=_
  simp only [hx, hH, hg, ha, and_self]

end BfgsVerification.DEmbedding
