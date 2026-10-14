import BfgsVerification.NonStrictLineSearch
import BfgsVerification.LGlobalFailure

/-!
# Lower-curvature global failure for the non-strict line search

The article's deterministic search (Section `art:failure`) accepts with the
non-strict tests `F(x+ap) ≤ F(x)+c₁ a gᵀp` and `gᵀ_+ p ≥ c₂ gᵀp`. The library
proves the lower-curvature construction for the strict search
`DeterministicLineSearch`. Every decision there has a strict margin, so the
non-strict search `NonStrictLineSearch` takes the same decisions. This file
proves that for the normalized oracle neighbourhood and the actual runs, and
restates `LGlobalFailure.actual_global_failure` with both traces.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification.LNormalizedOracle
open SeedCycle SeedOrbit LNormalizedReturn
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Conditions.nonstrict_physical_accept {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) (hq : trialAccept q=true) :
    NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))
      (bfgsStep (physicalMetric μ w (trialPhase q)) (phaseGradient μ w (trialPhase q)) 1)
      (phaseGradient μ w (trialPhase q)) c₁ (trialLength q) ∧
    NonStrictLineSearch.Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))
      (bfgsStep (physicalMetric μ w (trialPhase q)) (phaseGradient μ w (trialPhase q)) 1)
      (phaseGradient μ w (trialPhase q)) c₂ (trialLength q) := by
  obtain ⟨ha,hW⟩ := hw.physical_accept hτ q hq
  exact ⟨ha.le,hW.le⟩

/-- A rejected trial fails the non-strict Armijo test as well: its normalized
Armijo margin is strictly negative. -/
theorem Conditions.nonstrict_physical_reject {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) (hq : trialAccept q=false) :
    ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))
      (bfgsStep (physicalMetric μ w (trialPhase q)) (phaseGradient μ w (trialPhase q)) 1)
      (phaseGradient μ w (trialPhase q)) c₁ (trialLength q) := by
  have hm : phaseValue μ w (trialPhase q)+
      c₁*trialLength q*dot (phaseGradient μ w (trialPhase q)) (direction μ w (trialPhase q)) <
      trialValue μ w (trialPhase q) (trialLength q) := sub_neg.mp (hw.rejects q hq)
  dsimp only [phaseValue,trialValue] at hm
  apply not_le.mpr
  rw [physical_trial,physical_direction,physicalPoint,
    physical_value_of_active μ hτ (hw.trial_active q),physical_value_of_active μ hτ (hw.base_active (trialPhase q)),dot_smul_right]
  convert mul_lt_mul_of_pos_left hm hτ using 1
  ring

theorem Conditions.nonstrict_search_zero {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) :
    NonStrictLineSearch.search (LQuadraticSeed.objective μ) (physicalPoint μ w 0) (bfgsStep (physicalMetric μ w 0) (phaseGradient μ w 0) 1) (phaseGradient μ w 0) c₁ c₂ 5 0 none 1 =
      (some (1),[1]) := by
  obtain ⟨ha,hW⟩ := hw.nonstrict_physical_accept hτ 0 rfl
  change NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 0) (bfgsStep (physicalMetric μ w 0) (phaseGradient μ w 0) 1) (phaseGradient μ w 0) c₁ (1) at ha
  change NonStrictLineSearch.Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w 0) (bfgsStep (physicalMetric μ w 0) (phaseGradient μ w 0) 1) (phaseGradient μ w 0) c₂ (1) at hW
  exact NonStrictLineSearch.search_accept 4 ha hW

theorem Conditions.nonstrict_search_one {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) :
    NonStrictLineSearch.search (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ c₂ 5 0 none 1 =
      (some (1/4),[1,1/2,1/4]) := by
  have h1 := hw.nonstrict_physical_reject hτ 1 rfl
  have h2 := hw.nonstrict_physical_reject hτ 2 rfl
  obtain ⟨ha,hW⟩ := hw.nonstrict_physical_accept hτ 3 rfl
  change ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ (1) at h1
  change ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ (1/2) at h2
  change NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ (1/4) at ha
  change NonStrictLineSearch.Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₂ (1/4) at hW
  rw [NonStrictLineSearch.search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [NonStrictLineSearch.search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [NonStrictLineSearch.search_accept 2 ha hW]
  exact ⟨rfl,rfl⟩

theorem Conditions.nonstrict_search_two {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) :
    NonStrictLineSearch.search (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ c₂ 5 0 none 1 =
      (some (1/16),[1,1/2,1/4,1/8,1/16]) := by
  have h1 := hw.nonstrict_physical_reject hτ 4 rfl
  have h2 := hw.nonstrict_physical_reject hτ 5 rfl
  have h3 := hw.nonstrict_physical_reject hτ 6 rfl
  have h4 := hw.nonstrict_physical_reject hτ 7 rfl
  obtain ⟨ha,hW⟩ := hw.nonstrict_physical_accept hτ 8 rfl
  change ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1) at h1
  change ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/2) at h2
  change ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/4) at h3
  change ¬ NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/8) at h4
  change NonStrictLineSearch.Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/16) at ha
  change NonStrictLineSearch.Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₂ (1/16) at hW
  rw [NonStrictLineSearch.search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [NonStrictLineSearch.search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [NonStrictLineSearch.search_armijo_reject 2 h3]
  norm_num only [zero_add,div_div]
  norm_num
  rw [NonStrictLineSearch.search_armijo_reject 1 h4]
  norm_num only [zero_add,div_div]
  norm_num
  rw [NonStrictLineSearch.search_accept 0 ha hW]
  exact ⟨rfl,rfl⟩

theorem Conditions.nonstrict_fromMetric_search {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) :
    NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (physicalPoint μ w j) (physicalMetric μ w j) c₁ c₂ 5 =
      (some (length j),trialHistory j) := by
  unfold NonStrictLineSearch.fromMetric
  rw [DeterministicLineSearch.actual_coordinateGradient (hw.phase_hasGradient hτ j)]
  fin_cases j
  · exact hw.nonstrict_search_zero hτ
  · exact hw.nonstrict_search_one hτ
  · exact hw.nonstrict_search_two hτ

end BfgsVerification.LNormalizedOracle

namespace BfgsVerification.LFlatten.Data
open SeedOrbit SeedCycle LNormalizedReturn LNormalizedOracle
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {μ c₁ c₂ : ℝ}

theorem nonstrict_actual_search (D : Data μ c₁ c₂) (k : ℕ) :
    NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (D.x k) (D.H k) c₁ c₂ 5=
      (some (D.alpha k),trialHistory (phase k)) :=
  (D.conditions (period k)).nonstrict_fromMetric_search (D.scale_pos (period k)) (phase k)

end BfgsVerification.LFlatten.Data

namespace BfgsVerification.LGlobalFailure
open SeedOrbit SeedCycle LNormalizedReturn
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- `actual_global_failure` for the article's non-strict deterministic search:
the same actual infinite full-BFGS run has the same complete trace under the
non-strict tests (`NonStrictLineSearch`) and the strict tests
(`DeterministicLineSearch`), for every `μ>0`, `0<c₁≤1/3` and `c₁<c₂<1`. -/
theorem nonstrict_actual_global_failure {μ c₁ c₂ : ℝ} (hμ : 0<μ)
    (hc₁ : 0<c₁) (hc₁' : c₁≤1/3) (hc : c₁<c₂) (hc₂ : c₂<1)
    (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
      R.c₁=c₁ ∧ R.c₂=c₂ ∧
      Tendsto R.x atTop (𝓝 0) ∧ Tendsto R.H atTop (𝓝 0) ∧
      Tendsto (fun k => LQuadraticSeed.objective μ (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, R.α k=length (phase k)) ∧
      (∀ k, NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) c₁ c₂ 5=
        (some (R.α k),trialHistory (phase k))) ∧
      (∀ k, DeterministicLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) c₁ c₂ 5=
        (some (R.α k),trialHistory (phase k))) ∧
      (∀ k, R.x k∈U) ∧
      (∀ k q, trialPhase q=phase k →
        DifferentiableAt ℝ (LQuadraticSeed.objective μ)
          (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
        0<LQuadraticSeed.objective μ (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
        R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1∈U) ∧
      (∀ q : ℕ → Fin 9, (∀ k, trialPhase (q k)=phase k) →
        Tendsto (fun k => R.x k+trialLength (q k) • bfgsStep (R.H k) (R.g k) 1) atTop (𝓝 0)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)+
          c₁*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ∧
        c₂*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k))<
          dot (R.g (k+1)) (bfgsStep (R.H k) (R.g k) (R.α k))) ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 := by
  obtain ⟨D,ht,hp,hq⟩ := actual_orbit_data μ c₁ c₂ hc₁ hc₁' (hc₁.trans hc) U hU
  obtain ⟨hx,hH,hv,hpos,hdec,hsearch,hdiff,hqt,hnon⟩ := D.failure_contract hμ.le hc₁ hc hc₂ ht
  refine ⟨D.run hμ.le hc₁ hc hc₂,rfl,rfl,hx,hH,hv,hpos,hdec,fun _ => rfl,
    D.nonstrict_actual_search,hsearch,hp,?_,hqt,D.strict_accept,hnon⟩
  intro k q hphase
  exact ⟨hdiff k q hphase,D.all_trial_values_positive k q hphase,hq k q hphase⟩

/-- The literal source parameters `c₁=10⁻⁴`, `c₂=1/2` of `nonstrict_actual_global_failure`. -/
theorem nonstrict_source_global_failure {μ : ℝ} (hμ : 0<μ) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
      R.c₁=1/10000 ∧ R.c₂=1/2 ∧
      Tendsto R.x atTop (𝓝 0) ∧ Tendsto R.H atTop (𝓝 0) ∧
      Tendsto (fun k => LQuadraticSeed.objective μ (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, R.α k=length (phase k)) ∧
      (∀ k, NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) (1/10000) (1/2) 5=
        (some (R.α k),trialHistory (phase k))) ∧
      (∀ k, DeterministicLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) (1/10000) (1/2) 5=
        (some (R.α k),trialHistory (phase k))) ∧
      (∀ k, R.x k∈U) ∧
      (∀ k q, trialPhase q=phase k →
        DifferentiableAt ℝ (LQuadraticSeed.objective μ)
          (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
        0<LQuadraticSeed.objective μ (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
        R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1∈U) ∧
      (∀ q : ℕ → Fin 9, (∀ k, trialPhase (q k)=phase k) →
        Tendsto (fun k => R.x k+trialLength (q k) • bfgsStep (R.H k) (R.g k) 1) atTop (𝓝 0)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)+
          (1/10000)*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ∧
        (1/2)*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k))<
          dot (R.g (k+1)) (bfgsStep (R.H k) (R.g k) (R.α k))) ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 :=
  nonstrict_actual_global_failure hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) U hU

end BfgsVerification.LGlobalFailure
