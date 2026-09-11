import BfgsVerification.DNonStrictPredicates

noncomputable section
open scoped Topology
namespace BfgsVerification.SeedEmbedding.NonStrict
open SeedOrbit NonStrictLineSearch

theorem search_zero {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) (hphase : phase k=0) :
    search F (point p t k)
      (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ c₂ 5 0 none 1 =
        (some 1,[1]) := by
  obtain ⟨ha,hw⟩ := trial_accept h ht hc₁ hc₁' hc₂ k 0 (by change (0 : Fin 3)=phase k; exact hphase.symm) rfl
  exact search_accept 4 ha hw


theorem search_one {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) (hphase : phase k=1) :
    search F (point p t k)
      (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ c₂ 5 0 none 1 =
        (some (1/4),[1,1/2,1/4]) := by
  have h1 := trial_reject h ht hc₁ k 1 (by change (1 : Fin 3)=phase k; exact hphase.symm) rfl
  have h2 := trial_reject h ht hc₁ k 2 (by change (1 : Fin 3)=phase k; exact hphase.symm) rfl
  obtain ⟨ha,hw⟩ := trial_accept h ht hc₁ hc₁' hc₂ k 3 (by change (1 : Fin 3)=phase k; exact hphase.symm) rfl
  change ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1) at h1
  change ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1/2) at h2
  change Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1/4) at ha
  change Wolfe F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₂ (1/4) at hw
  rw [search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_accept 2 ha hw]
  exact ⟨rfl,rfl⟩


theorem search_two {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) (hphase : phase k=2) :
    search F (point p t k)
      (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ c₂ 5 0 none 1 =
        (some (1/16),[1,1/2,1/4,1/8,1/16]) := by
  have h1 := trial_reject h ht hc₁ k 4 (by change (2 : Fin 3)=phase k; exact hphase.symm) rfl
  have h2 := trial_reject h ht hc₁ k 5 (by change (2 : Fin 3)=phase k; exact hphase.symm) rfl
  have h3 := trial_reject h ht hc₁ k 6 (by change (2 : Fin 3)=phase k; exact hphase.symm) rfl
  have h4 := trial_reject h ht hc₁ k 7 (by change (2 : Fin 3)=phase k; exact hphase.symm) rfl
  obtain ⟨ha,hw⟩ := trial_accept h ht hc₁ hc₁' hc₂ k 8 (by change (2 : Fin 3)=phase k; exact hphase.symm) rfl
  change ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1) at h1
  change ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1/2) at h2
  change ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1/4) at h3
  change ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1/8) at h4
  change Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (1/16) at ha
  change Wolfe F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₂ (1/16) at hw
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


theorem search_all_phases {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) :
    search F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1)
      (gradient t k) c₁ c₂ 5 0 none 1 = (some (orbitLength k),trialHistory (phase k)) := by
  have hcases : phase k=0 ∨ phase k=1 ∨ phase k=2 := by
    generalize phase k=j
    fin_cases j <;> simp
  rcases hcases with hphase | hphase | hphase
  · rw [orbitLength, hphase]
    exact search_zero h ht hc₁ hc₁' hc₂ k hphase
  · rw [orbitLength, hphase]
    exact search_one h ht hc₁ hc₁' hc₂ k hphase
  · rw [orbitLength, hphase]
    exact search_two h ht hc₁ hc₁' hc₂ k hphase

theorem fromMetric_exact {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) :
    fromMetric F (point p t k) (orbitMetric k) c₁ c₂ 5 =
      (some (orbitLength k),trialHistory (phase k)) := by
  unfold fromMetric
  rw [DeterministicLineSearch.actual_coordinateGradient (h.derivatives k)]
  exact search_all_phases h ht hc₁ hc₁' hc₂ k

end BfgsVerification.SeedEmbedding.NonStrict
