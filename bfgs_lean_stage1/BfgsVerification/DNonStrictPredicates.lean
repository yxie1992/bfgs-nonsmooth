import BfgsVerification.NonStrictLineSearch
import BfgsVerification.SeedEmbeddingSearch
noncomputable section
namespace BfgsVerification.SeedEmbedding.NonStrict
open SeedOrbit NonStrictLineSearch
set_option maxHeartbeats 1000000

theorem trial_accept {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂)
    (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) (ha : trialAccept q=true) :
    Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (trialLength q) ∧
    Wolfe F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₂ (trialLength q) := by
  obtain ⟨ha,hw⟩ := SeedEmbedding.trial_accept h ht hc₁ hc₁' hc₂ k q hq ha
  exact ⟨ha.le,hw.le⟩

theorem trial_reject {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) (ha : trialAccept q=false) :
    ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (trialLength q) := by
  have hh := SeedEmbedding.trial_reject h ht (half_pos hc₁) k q hq ha
  have hqpos := source_trial_length_pos q
  let R := SeedEmbedding.run h.toData ht (1/4) (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have he : 0 < metricEnergy (orbitMetric k) (gradient t k) := R.q_pos k
  have hd : dot (gradient t k) (bfgsStep (orbitMetric k) (gradient t k) 1) < 0 := by
    rw [dot_bfgsStep,one_mul]
    exact neg_neg_of_pos he
  have hp := mul_neg_of_pos_of_neg (mul_pos hc₁ hqpos) hd
  unfold DeterministicLineSearch.Armijo at hh
  unfold Armijo
  have hn := le_of_not_gt hh
  intro hle
  nlinarith [hn,hle,hp]

end BfgsVerification.SeedEmbedding.NonStrict
