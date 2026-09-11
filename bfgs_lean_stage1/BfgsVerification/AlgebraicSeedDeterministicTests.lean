import BfgsVerification.AlgebraicSeedInfiniteOrbit
import BfgsVerification.DeterministicLineSearch
noncomputable section
open scoped Topology
namespace BfgsVerification.SeedOrbit
open AlgebraicSeed SeedCycle DeterministicLineSearch

theorem scaled_trial {n : ℕ} (x p : Vec n) (a t : ℝ) :
    t • x+a • (t • p)=t • (x+a • p) := by
  rw [smul_add,smul_comm a t p]

theorem TrialCertificate.scaled_accept {c d r : ℝ} {j i : Fin 3} {a t c₁ c₂ : ℝ}
    (hbase : StrictActive c d (point c d r j) j)
    (h : TrialCertificate c d r j a i true)
    (ha : 0 < a) (ht : 0 < t) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    Armijo (objective c d) (t • point c d r j) (t • direction c d r j) (gradient c d j) c₁ a ∧
    Wolfe (objective c d) (t • point c d r j) (t • direction c d r j) (gradient c d j) c₂ a := by
  obtain ⟨hArmijo,hWolfe⟩ := h.actual_accept hbase hc₁ hc₁' hc₂
  have hgrad : coordinateGradient (objective c d) (t • trial c d r j a)=gradient c d i :=
    actual_coordinateGradient (hasGradient_of_active (h.active.scale ht))
  constructor
  · unfold Armijo
    rw [scaled_trial]
    change objective c d (t • trial c d r j a) < _
    rw [objective_scale_at_active h.active ht,objective_scale_at_active hbase ht,dot_smul_right]
    rw [dot_smul_right] at hArmijo
    convert mul_lt_mul_of_pos_left hArmijo ht using 1 <;> ring
  · unfold Wolfe
    rw [scaled_trial]
    change c₂*dot (gradient c d j) (t • direction c d r j) <
      dot (coordinateGradient (objective c d) (t • trial c d r j a)) (t • direction c d r j)
    rw [hgrad,dot_smul_right,dot_smul_right]
    have hw : c₂*dot (gradient c d j) (direction c d r j) < dot (gradient c d i) (direction c d r j) := by
      rw [dot_smul_right,dot_smul_right] at hWolfe
      apply (mul_lt_mul_left ha).mp
      convert hWolfe using 1 <;> ring
    convert mul_lt_mul_of_pos_left hw ht using 1 <;> ring

theorem TrialCertificate.scaled_reject {c d r : ℝ} {j i : Fin 3} {a t c₁ : ℝ}
    (hbase : StrictActive c d (point c d r j) j)
    (h : TrialCertificate c d r j a i false) (ht : 0 < t) (hc₁ : 0 < c₁) :
    ¬ Armijo (objective c d) (t • point c d r j) (t • direction c d r j) (gradient c d j) c₁ a := by
  have hh := h.actual_reject hbase hc₁
  have hrev : objective c d (t • point c d r j)+c₁*a*dot (gradient c d j) (t • direction c d r j) <
      objective c d (t • point c d r j+a • (t • direction c d r j)) := by
    rw [scaled_trial]
    change _ < objective c d (t • trial c d r j a)
    rw [objective_scale_at_active h.active ht,objective_scale_at_active hbase ht,dot_smul_right]
    rw [dot_smul_right] at hh
    convert mul_lt_mul_of_pos_left hh ht using 1 <;> ring
  exact not_lt_of_gt hrev

theorem source_scaled_accept {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (q : Fin 9) (hq : trialAccept q=true) :
    Armijo (objective seedC seedD) (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ∧
    Wolfe (objective seedC seedD) (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₂ (trialLength q) := by
  have h := source_trial_certificate q
  rw [hq] at h
  exact h.scaled_accept (source_base_certificate (trialPhase q)).active (source_trial_length_pos q) ht hc₁ hc₁' hc₂

theorem source_scaled_reject {t c₁ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁)
    (q : Fin 9) (hq : trialAccept q=false) :
    ¬ Armijo (objective seedC seedD) (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₁ (trialLength q) := by
  have h := source_trial_certificate q
  rw [hq] at h
  exact h.scaled_reject (source_base_certificate (trialPhase q)).active ht hc₁

end BfgsVerification.SeedOrbit
