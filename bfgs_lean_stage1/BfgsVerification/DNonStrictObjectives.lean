import BfgsVerification.DNonStrictSearch
import BfgsVerification.DLiteralIdentities
import BfgsVerification.DEmbeddingTarget

noncomputable section
namespace BfgsVerification.DNonStrictObjectives
open SeedOrbit SeedCycle
set_option maxHeartbeats 1000000

def seedOracleData : SeedEmbedding.OracleData (objective seedC seedD) 0 1 0 where
  convex := (family seedC seedD).objective_convex
  values k := by simp only [SeedEmbedding.point,one_smul,zero_add,one_pow,one_mul]
  derivatives k := by
    simpa only [SeedEmbedding.point,SeedEmbedding.gradient,one_smul,zero_add] using orbit_hasGradient k
  trial_values k q hq := by simp only [one_smul,zero_add,one_pow,one_mul]
  trial_derivatives k q hq := by
    simpa only [one_smul,zero_add] using
      hasGradient_of_active (orbit_trial_point_certificate k q hq).active

def coerciveOracleData : SeedEmbedding.OracleData coerciveObjective 0 1 0 where
  convex := coerciveFamily.objective_convex
  values k := by
    simpa only [SeedEmbedding.point,one_smul,zero_add,one_pow,one_mul] using coercive_orbit_value k
  derivatives k := by
    simpa only [SeedEmbedding.point,SeedEmbedding.gradient,one_smul,zero_add] using coercive_orbit_hasGradient k
  trial_values k q hq := by
    simpa only [one_smul,zero_add,one_pow,one_mul] using
      coercive_value_eq (orbit_trial_point_certificate k q hq)
  trial_derivatives k q hq := by
    simpa only [one_smul,zero_add] using
      coercive_hasGradient (orbit_trial_point_certificate k q hq)

theorem seed_fromMetric {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂)
    (k : ℕ) : NonStrictLineSearch.fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      (some (orbitLength k),trialHistory (phase k)) := by
  simpa only [SeedEmbedding.point,one_smul,zero_add] using
    SeedEmbedding.NonStrict.fromMetric_exact seedOracleData (by norm_num) hc₁ hc₁' hc₂ k

theorem coercive_fromMetric {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂)
    (k : ℕ) : NonStrictLineSearch.fromMetric coerciveObjective (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      (some (orbitLength k),trialHistory (phase k)) := by
  simpa only [SeedEmbedding.point,one_smul,zero_add] using
    SeedEmbedding.NonStrict.fromMetric_exact coerciveOracleData (by norm_num) hc₁ hc₁' hc₂ k

theorem embedding_fromMetric {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) :
    let R := DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂
    NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) :=
  SeedEmbedding.NonStrict.fromMetric_exact (DEmbedding.actualOracleData hn)
    (sq_pos_of_pos (DScalarGeometric.scale_pos n)) hc₁ hc₁' (hc₁.trans hc) k

theorem embedding_same_search {n : ℕ} (hn : 1 ≤ n) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) :
    let R := DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂
    NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 :=
  (embedding_fromMetric hn hc₁ hc₁' hc hc₂ k).trans (DEmbedding.run_search hn hc₁ hc₁' hc hc₂ k).symm

end BfgsVerification.DNonStrictObjectives
