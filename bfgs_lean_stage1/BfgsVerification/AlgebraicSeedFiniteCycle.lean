import BfgsVerification.AlgebraicSeedOracleBridges
import BfgsVerification.AlgebraicSeedOrbitHomogeneity
noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace BfgsVerification.SeedOrbit
open AlgebraicSeed SeedCycle

abbrev seedC : ℝ := root 0
abbrev seedD : ℝ := root 1
abbrev seedRatio : ℝ := ratio seedC seedD

def trialPhase : Fin 9 → Fin 3 := ![0,1,1,1,2,2,2,2,2]
def trialLength : Fin 9 → ℝ := ![1,1,1/2,1/4,1,1/2,1/4,1/8,1/16]
def trialActive : Fin 9 → Fin 3 := ![1,0,0,2,0,0,0,0,0]
def trialAccept : Fin 9 → Bool := ![true,false,false,true,false,false,false,false,true]
def nextPhase : Fin 3 → Fin 3 := ![1,2,0]

theorem source_base_certificate (j : Fin 3) : PointCertificate seedC seedD (point seedC seedD seedRatio j) j := by
  have hc := root_tight_box.1
  have hd := root_tight_box.2
  have hr := tight_ratio hc hd
  fin_cases j
  · exact base_0_certificate hc hd hr
  · exact base_1_certificate hc hd hr
  · exact base_2_certificate hc hd hr

theorem source_trial_certificate (q : Fin 9) :
    TrialCertificate seedC seedD seedRatio (trialPhase q) (trialLength q) (trialActive q) (trialAccept q) := by
  have hc := root_tight_box.1
  have hd := root_tight_box.2
  have hr := tight_ratio hc hd
  fin_cases q
  · exact trial_0_certificate hc hd hr
  · exact trial_1_certificate hc hd hr
  · exact trial_2_certificate hc hd hr
  · exact trial_3_certificate hc hd hr
  · exact trial_4_certificate hc hd hr
  · exact trial_5_certificate hc hd hr
  · exact trial_6_certificate hc hd hr
  · exact trial_7_certificate hc hd hr
  · exact trial_8_certificate hc hd hr

theorem source_accepted_certificate (j : Fin 3) :
    TrialCertificate seedC seedD seedRatio j (length j) (nextPhase j) true := by
  fin_cases j
  · exact source_trial_certificate 0
  · exact source_trial_certificate 3
  · exact source_trial_certificate 8

theorem source_length_pos (j : Fin 3) : 0 < length j := by
  fin_cases j <;> norm_num [length]

theorem source_trial_length_pos (q : Fin 9) : 0 < trialLength q := by
  fin_cases q <;> norm_num [trialLength]

theorem source_gradient_nonzero (j : Fin 3) : gradient seedC seedD j ≠ 0 := by
  intro h
  have he := congrArg (fun x : Vec 2 => x 0) h
  have hc := root_tight_box.1.1
  fin_cases j <;> norm_num [gradient,g0,g1,g2] at he
  linarith

theorem source_ratio_pos_lt_one : 0 < seedRatio ∧ seedRatio < 1 := by
  have h := tight_ratio root_tight_box.1 root_tight_box.2
  exact ⟨by linarith [h.1],by linarith [h.2]⟩

theorem source_base_hasGradient (j : Fin 3) :
    HasFDerivAt (objective seedC seedD) (gradientFunctional (gradient seedC seedD j))
      (point seedC seedD seedRatio j) := hasGradient_of_active (source_base_certificate j).active

theorem source_trial_hasGradient (q : Fin 9) :
    HasFDerivAt (objective seedC seedD) (gradientFunctional (gradient seedC seedD (trialActive q)))
      (trial seedC seedD seedRatio (trialPhase q) (trialLength q)) :=
  hasGradient_of_active (source_trial_certificate q).active

theorem source_accepted_inequalities {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc₂ : 0 < c₂) (j : Fin 3) :
    objective seedC seedD (trial seedC seedD seedRatio j (length j)) <
      objective seedC seedD (point seedC seedD seedRatio j)+
        c₁*dot (gradient seedC seedD j) (bfgsStep (metric seedC seedD j) (gradient seedC seedD j) (length j)) ∧
    c₂*dot (gradient seedC seedD j) (bfgsStep (metric seedC seedD j) (gradient seedC seedD j) (length j)) <
      dot (gradient seedC seedD (nextPhase j)) (bfgsStep (metric seedC seedD j) (gradient seedC seedD j) (length j)) := by
  rw [source_direction]
  exact (source_accepted_certificate j).actual_accept (source_base_certificate j).active hc₁ hc₁' hc₂

end BfgsVerification.SeedOrbit
