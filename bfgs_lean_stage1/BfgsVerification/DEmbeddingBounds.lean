import BfgsVerification.DEmbeddingTarget

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric

theorem slab_horizontal (n : ℕ) {h : Vec 2}
    (hh : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    |h 0| ≤ scale n/2 := by
  simpa [SeedOrbit.gradient, SeedCycle.g0, dot, Fin.sum_univ_two] using hh 0

theorem branch_plateau_lower_bound (n : ℕ) (i : Fin 3) {h : Vec 2}
    (hh : |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    (scale n)^3/2 ≤ branch i.castSucc (center n+h) := by
  rw [branch_plateau n i hh]
  have he := mul_le_mul_of_nonneg_left (abs_le.mp hh).1 (sq_nonneg (scale n))
  nlinarith

theorem center_active_branches (n : ℕ) :
    (∀ i : Fin 3, branch i.castSucc (center n)=objective (center n)) ∧
    branch 3 (center n)<objective (center n) := by
  constructor
  · intro i
    have he := branch_plateau n i (h := 0) (by simpa [dot] using (half_pos (scale_pos n)).le)
    simpa [center_value, dot] using he
  · have he := last_branch_negative n (h := 0) (fun j => by simpa [dot] using (half_pos (scale_pos n)).le)
    simpa only [add_zero] using he.trans (center_positive n)

theorem all_actual_trial_values {n : ℕ} (hn : 1≤n) {c₁ c₂ : ℝ} (hc₁ : 0<c₁) (hc₁' : c₁≤1/3)
    (hc : c₁<c₂) (hc₂ : c₂<1) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
    objective (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1)=
      (scale n)^3+(scale n)^4*SeedOrbit.objective seedC seedD (SeedEmbedding.trialPoint k q) := by
  change objective (SeedEmbedding.point (center n) ((scale n)^2) k+
    trialLength q • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale n)^2) k) 1)=_
  rw [SeedEmbedding.translated_trial, (actualOracleData hn).trial_values k q hq]
  ring

end BfgsVerification.DEmbedding
