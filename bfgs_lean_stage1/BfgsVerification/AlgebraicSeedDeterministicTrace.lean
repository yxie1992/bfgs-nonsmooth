import BfgsVerification.AlgebraicSeedDeterministicTests
import BfgsVerification.AlgebraicSeedFailure
noncomputable section
open scoped Topology
namespace BfgsVerification.SeedOrbit
open SeedCycle DeterministicLineSearch

def trialHistory : Fin 3 → List ℝ := ![[1],[1,1/2,1/4],[1,1/2,1/4,1/8,1/16]]

theorem scaled_search_zero {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    search (objective seedC seedD) (t • point seedC seedD seedRatio 0)
      (t • direction seedC seedD seedRatio 0) (gradient seedC seedD 0) c₁ c₂ 5 0 none 1 =
        (some 1,[1]) := by
  obtain ⟨ha,hw⟩ := source_scaled_accept ht hc₁ hc₁' hc₂ 0 rfl
  exact search_accept 4 ha hw

theorem scaled_search_one {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    search (objective seedC seedD) (t • point seedC seedD seedRatio 1)
      (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ c₂ 5 0 none 1 =
        (some (1/4),[1,1/2,1/4]) := by
  have h1 := source_scaled_reject ht hc₁ 1 rfl
  have h2 := source_scaled_reject ht hc₁ 2 rfl
  obtain ⟨ha,hw⟩ := source_scaled_accept ht hc₁ hc₁' hc₂ 3 rfl
  change ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ (1) at h1
  change ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ (1/2) at h2
  change Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ (1/4) at ha
  change Wolfe (objective seedC seedD) (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₂ (1/4) at hw
  rw [search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_accept 2 ha hw]
  exact ⟨rfl,rfl⟩

theorem scaled_search_two {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    search (objective seedC seedD) (t • point seedC seedD seedRatio 2)
      (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ c₂ 5 0 none 1 =
        (some (1/16),[1,1/2,1/4,1/8,1/16]) := by
  have h1 := source_scaled_reject ht hc₁ 4 rfl
  have h2 := source_scaled_reject ht hc₁ 5 rfl
  have h3 := source_scaled_reject ht hc₁ 6 rfl
  have h4 := source_scaled_reject ht hc₁ 7 rfl
  obtain ⟨ha,hw⟩ := source_scaled_accept ht hc₁ hc₁' hc₂ 8 rfl
  change ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1) at h1
  change ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/2) at h2
  change ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/4) at h3
  change ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/8) at h4
  change Armijo (objective seedC seedD) (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/16) at ha
  change Wolfe (objective seedC seedD) (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₂ (1/16) at hw
  rw [search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_armijo_reject 2 h3]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_armijo_reject 1 h4]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_accept 0 ha hw]
  exact ⟨rfl,rfl⟩

theorem scaled_search {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (j : Fin 3) :
    search (objective seedC seedD) (t • point seedC seedD seedRatio j)
      (t • direction seedC seedD seedRatio j) (gradient seedC seedD j) c₁ c₂ 5 0 none 1 =
        (some (length j),trialHistory j) := by
  fin_cases j
  · exact scaled_search_zero ht hc₁ hc₁' hc₂
  · exact scaled_search_one ht hc₁ hc₁' hc₂
  · exact scaled_search_two ht hc₁ hc₁' hc₂

theorem orbit_search {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) :
    fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      (some (orbitLength k),trialHistory (phase k)) := by
  unfold fromMetric
  rw [actual_coordinateGradient (orbit_hasGradient k)]
  simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,bfgsStep_scale_matrix,source_direction,one_smul]
  exact scaled_search (orbitScale_pos k) hc₁ hc₁' hc₂ (phase k)

theorem orbit_all_trials_differentiable (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    DifferentiableAt ℝ (objective seedC seedD)
      (orbitPoint k+trialLength q • bfgsStep (orbitMetric k) (orbitGradient k) 1) := by
  simp only [orbitPoint,orbitMetric,orbitGradient,bfgsStep_scale_matrix,source_direction,one_smul,scaled_trial]
  rw [← hq]
  exact (hasGradient_of_active ((source_trial_certificate q).active.scale (orbitScale_pos k))).differentiableAt

theorem orbit_trial_point_certificate (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    PointCertificate seedC seedD
      (orbitPoint k+trialLength q • bfgsStep (orbitMetric k) (orbitGradient k) 1) (trialActive q) := by
  simp only [orbitPoint,orbitMetric,orbitGradient,bfgsStep_scale_matrix,source_direction,one_smul,scaled_trial]
  rw [← hq]
  exact (source_trial_certificate q).toPointCertificate.scale (orbitScale_pos k) (orbitScale_le_one k)

theorem orbit_phase_parameters (m : ℕ) (j : Fin 3) :
    orbitPoint (3*m+j.val)=seedRatio^m • point seedC seedD seedRatio j ∧
      orbitMetric (3*m+j.val)=seedRatio^m • metric seedC seedD j ∧
      orbitGradient (3*m+j.val)=gradient seedC seedD j ∧
      orbitLength (3*m+j.val)=length j := by
  have hj := j.isLt
  have hp : period (3*m+j.val)=m := by dsimp [period]; omega
  have hf : phase (3*m+j.val)=j := by
    apply Fin.ext
    change (3*m+j.val)%3=j.val
    omega
  simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,orbitScale,hp,hf,and_self]

theorem trialHistory_length_le (j : Fin 3) : (trialHistory j).length ≤ 5 := by
  fin_cases j <;> norm_num [trialHistory]

theorem actual_deterministic_seed_failure {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let R := run c₁ c₂ hc₁ hc₁' hc hc₂
    R.H 0=1 ∧ Filter.Tendsto R.x Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun k => objective seedC seedD (R.x k)) Filter.atTop (𝓝 0) ∧
      (∀ k, 0 < objective seedC seedD (R.x k)) ∧
      (∀ k, objective seedC seedD (R.x (k+1)) < objective seedC seedD (R.x k)) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 ∧
      (∀ k, fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5 =
        (some (R.α k),trialHistory (phase k))) := by
  obtain ⟨h0,hx,hF,hpos,hdec,hns⟩ := actual_run_failure hc₁ hc₁' hc hc₂
  exact ⟨h0,hx,hF,hpos,hdec,hns,orbit_search hc₁ hc₁' (hc₁.trans hc)⟩

end BfgsVerification.SeedOrbit
