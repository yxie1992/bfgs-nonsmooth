import BfgsVerification.LNormalizedReturn
import BfgsVerification.AlgebraicSeedDeterministicTrace

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LNormalizedOracle
open SeedCycle SeedOrbit LNormalizedReturn DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def phasePoint (μ : ℝ) (w : State) (j : Fin 3) : Vec 2 := (internal μ w j.val).1
def phaseMetric (μ : ℝ) (w : State) (j : Fin 3) : Mat 2 := (internal μ w j.val).2
def phaseGradient (μ : ℝ) (w : State) (j : Fin 3) : Vec 2 :=
  currentGradient μ (scale w) j (internal μ w j.val)
def direction (μ : ℝ) (w : State) (j : Fin 3) : Vec 2 :=
  bfgsStep (phaseMetric μ w j) (phaseGradient μ w j) 1
def trialPoint (μ : ℝ) (w : State) (j : Fin 3) (a : ℝ) : Vec 2 :=
  phasePoint μ w j+a • direction μ w j
def trialGradient (μ : ℝ) (w : State) (j : Fin 3) (a : ℝ) (i : Fin 3) : Vec 2 :=
  SeedOrbit.gradient seedC seedD i+(μ*scale w) • trialPoint μ w j a
def normalizedValue (μ τ : ℝ) (z : Vec 2) : ℝ :=
  SeedOrbit.objective seedC seedD z+(μ*τ/2)*sqNorm z
def phaseValue (μ : ℝ) (w : State) (j : Fin 3) : ℝ :=
  normalizedValue μ (scale w) (phasePoint μ w j)
def trialValue (μ : ℝ) (w : State) (j : Fin 3) (a : ℝ) : ℝ :=
  normalizedValue μ (scale w) (trialPoint μ w j a)
def armijoMargin (μ c₁ : ℝ) (w : State) (j : Fin 3) (a : ℝ) : ℝ :=
  phaseValue μ w j+c₁*a*dot (phaseGradient μ w j) (direction μ w j)-trialValue μ w j a
def wolfeMargin (μ c₂ : ℝ) (w : State) (j : Fin 3) (a : ℝ) (i : Fin 3) : ℝ :=
  dot (trialGradient μ w j a i) (direction μ w j)-c₂*dot (phaseGradient μ w j) (direction μ w j)

theorem objective_hasGradient_of_active (μ : ℝ) {z : Vec 2} {i : Fin 3}
    (hi : StrictActive seedC seedD z i) :
    HasFDerivAt (LQuadraticSeed.objective μ) (gradientFunctional (LQuadraticSeed.branchGradient μ z i)) z := by
  convert (LQuadraticSeed.quadratic_hasGradient μ z).add (SeedOrbit.hasGradient_of_active hi) using 1
  ext v
  simp only [LQuadraticSeed.branchGradient,gradientFunctional_apply,ContinuousLinearMap.add_apply,
    dot,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem physical_value_of_active (μ : ℝ) {τ : ℝ} (hτ : 0 < τ) {z : Vec 2} {i : Fin 3}
    (hi : StrictActive seedC seedD z i) :
    LQuadraticSeed.objective μ (τ • z)=τ*normalizedValue μ τ z := by
  rw [LQuadraticSeed.objective,SeedOrbit.objective_scale_at_active hi hτ]
  simp only [LQuadraticSeed.quadratic,RadialPower.sqNorm_smul,normalizedValue]
  ring

theorem phasePoint_seed (μ : ℝ) (j : Fin 3) :
    phasePoint μ seed j=SeedOrbit.point seedC seedD seedRatio j := by
  simp only [phasePoint,internal_seed_phase]
theorem phaseMetric_seed (μ : ℝ) (j : Fin 3) :
    phaseMetric μ seed j=metric seedC seedD j := by simp only [phaseMetric,internal_seed_phase]
theorem phaseGradient_seed (μ : ℝ) (j : Fin 3) :
    phaseGradient μ seed j=SeedOrbit.gradient seedC seedD j := by
  simp only [phaseGradient,seed_scale,currentGradient_zero]
theorem direction_seed (μ : ℝ) (j : Fin 3) :
    direction μ seed j=SeedOrbit.direction seedC seedD seedRatio j := by
  simp only [direction,phaseMetric_seed,phaseGradient_seed,source_direction,one_smul]
theorem trialPoint_seed (μ : ℝ) (j : Fin 3) (a : ℝ) :
    trialPoint μ seed j a=trial seedC seedD seedRatio j a := by
  simp only [trialPoint,phasePoint_seed,direction_seed,trial]
theorem trialGradient_seed (μ : ℝ) (j i : Fin 3) (a : ℝ) :
    trialGradient μ seed j a i=SeedOrbit.gradient seedC seedD i := by
  simp [trialGradient,seed_scale]
theorem phaseValue_seed (μ : ℝ) (j : Fin 3) :
    phaseValue μ seed j=SeedOrbit.objective seedC seedD (SeedOrbit.point seedC seedD seedRatio j) := by
  simp [phaseValue,normalizedValue,phasePoint_seed]
theorem trialValue_seed (μ : ℝ) (j : Fin 3) (a : ℝ) :
    trialValue μ seed j a=SeedOrbit.objective seedC seedD (trial seedC seedD seedRatio j a) := by
  simp [trialValue,normalizedValue,trialPoint_seed]

theorem analytic_phasePoint_seed (μ : ℝ) (j : Fin 3) :
    AnalyticAt ℝ (fun w => phasePoint μ w j) seed :=
  analyticAt_fst.comp (analytic_internal_seed μ j.val (by omega))
theorem analytic_phaseMetric_seed (μ : ℝ) (j : Fin 3) :
    AnalyticAt ℝ (fun w => phaseMetric μ w j) seed :=
  analyticAt_snd.comp (analytic_internal_seed μ j.val (by omega))
theorem analytic_phaseGradient_seed (μ : ℝ) (j : Fin 3) :
    AnalyticAt ℝ (fun w => phaseGradient μ w j) seed :=
  analytic_currentGradient μ j (analytic_scale seed) (analytic_internal_seed μ j.val (by omega))
theorem analytic_direction_seed (μ : ℝ) (j : Fin 3) :
    AnalyticAt ℝ (fun w => direction μ w j) seed :=
  (analytic_mulVec (analytic_phaseMetric_seed μ j) (analytic_phaseGradient_seed μ j)).const_smul (c := (-1 : ℝ))
theorem analytic_trialPoint_seed (μ : ℝ) (j : Fin 3) (a : ℝ) :
    AnalyticAt ℝ (fun w => trialPoint μ w j a) seed :=
  (analytic_phasePoint_seed μ j).add ((analytic_direction_seed μ j).const_smul (c := a))
theorem analytic_trialGradient_seed (μ : ℝ) (j i : Fin 3) (a : ℝ) :
    AnalyticAt ℝ (fun w => trialGradient μ w j a i) seed :=
  analyticAt_const.add ((analyticAt_const.mul (analytic_scale seed)).smul (analytic_trialPoint_seed μ j a))

theorem continuous_normalizedValue (μ : ℝ) {f : State → Vec 2}
    (hf : ContinuousAt f seed) :
    ContinuousAt (fun w => normalizedValue μ (scale w) (f w)) seed := by
  have hG : Continuous (SeedOrbit.objective seedC seedD) :=
    convex_continuous (SeedOrbit.family seedC seedD).objective_convex
  have hs := (analytic_scale seed).continuousAt
  exact (hG.continuousAt.comp hf).add
    ((((continuousAt_const.mul hs).div_const 2)).mul (continuous_sqNorm.continuousAt.comp hf))
theorem continuous_phaseValue_seed (μ : ℝ) (j : Fin 3) :
    ContinuousAt (fun w => phaseValue μ w j) seed :=
  continuous_normalizedValue μ (analytic_phasePoint_seed μ j).continuousAt
theorem continuous_trialValue_seed (μ : ℝ) (j : Fin 3) (a : ℝ) :
    ContinuousAt (fun w => trialValue μ w j a) seed :=
  continuous_normalizedValue μ (analytic_trialPoint_seed μ j a).continuousAt
theorem continuous_armijoMargin_seed (μ c₁ : ℝ) (j : Fin 3) (a : ℝ) :
    ContinuousAt (fun w => armijoMargin μ c₁ w j a) seed :=
  ((continuous_phaseValue_seed μ j).add
    (continuousAt_const.mul (analytic_dot (analytic_phaseGradient_seed μ j)
      (analytic_direction_seed μ j)).continuousAt)).sub (continuous_trialValue_seed μ j a)
theorem continuous_wolfeMargin_seed (μ c₂ : ℝ) (j i : Fin 3) (a : ℝ) :
    ContinuousAt (fun w => wolfeMargin μ c₂ w j a i) seed :=
  (analytic_dot (analytic_trialGradient_seed μ j i a) (analytic_direction_seed μ j)).continuousAt.sub
    (continuousAt_const.mul (analytic_dot (analytic_phaseGradient_seed μ j) (analytic_direction_seed μ j)).continuousAt)

theorem seed_accept_margins (μ : ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc₂ : 0 < c₂) (q : Fin 9) (hq : trialAccept q=true) :
    0 < armijoMargin μ c₁ seed (trialPhase q) (trialLength q) ∧
    0 < wolfeMargin μ c₂ seed (trialPhase q) (trialLength q) (trialActive q) := by
  have h := source_trial_certificate q
  rw [hq] at h
  obtain ⟨ha,hw⟩ := h.actual_accept (source_base_certificate (trialPhase q)).active hc₁ hc₁' hc₂
  rw [dot_smul_right] at ha
  have hw' : c₂*dot (SeedOrbit.gradient seedC seedD (trialPhase q))
      (SeedOrbit.direction seedC seedD seedRatio (trialPhase q)) <
      dot (SeedOrbit.gradient seedC seedD (trialActive q)) (SeedOrbit.direction seedC seedD seedRatio (trialPhase q)) := by
    apply (mul_lt_mul_left (source_trial_length_pos q)).mp
    rw [dot_smul_right,dot_smul_right] at hw
    convert hw using 1 <;> ring
  constructor
  · simp only [armijoMargin,phaseValue_seed,trialValue_seed,phaseGradient_seed,direction_seed]
    nlinarith
  · simp only [wolfeMargin,trialGradient_seed,phaseGradient_seed,direction_seed]
    linarith

theorem seed_reject_margin (μ : ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (q : Fin 9) (hq : trialAccept q=false) :
    armijoMargin μ c₁ seed (trialPhase q) (trialLength q) < 0 := by
  have h := source_trial_certificate q
  rw [hq] at h
  have hh := h.actual_reject (source_base_certificate (trialPhase q)).active hc₁
  rw [dot_smul_right] at hh
  simp only [armijoMargin,phaseValue_seed,trialValue_seed,phaseGradient_seed,direction_seed]
  nlinarith

theorem strictActive_eventually {f : State → Vec 2} (hf : ContinuousAt f seed) {i : Fin 3}
    (hi : StrictActive seedC seedD (f seed) i) :
    ∀ᶠ w in 𝓝 seed, StrictActive seedC seedD (f w) i := by
  apply eventually_all.mpr
  intro j
  by_cases hj : j=i
  · exact Eventually.of_forall (fun _ h => (h hj).elim)
  have hc (k : Fin 3) : ContinuousAt (fun w => dot (SeedOrbit.gradient seedC seedD k) (f w)) seed := by
    simpa only [gradientFunctional_apply,Function.comp_def] using
      (gradientFunctional (SeedOrbit.gradient seedC seedD k)).continuous.continuousAt.comp hf
  exact ((hc j).eventually_lt (hc i) (hi j hj)).mono (fun _ h _ => h)

structure Conditions (μ c₁ c₂ : ℝ) (w : State) : Prop where
  regular : Regular μ w
  base_active : ∀ j, StrictActive seedC seedD (phasePoint μ w j) j
  trial_active : ∀ q, StrictActive seedC seedD
    (trialPoint μ w (trialPhase q) (trialLength q)) (trialActive q)
  base_positive : ∀ j, 0 < phaseValue μ w j
  trial_positive : ∀ q, 0 < trialValue μ w (trialPhase q) (trialLength q)
  accepts : ∀ q, trialAccept q=true →
    0 < armijoMargin μ c₁ w (trialPhase q) (trialLength q) ∧
    0 < wolfeMargin μ c₂ w (trialPhase q) (trialLength q) (trialActive q)
  rejects : ∀ q, trialAccept q=false → armijoMargin μ c₁ w (trialPhase q) (trialLength q) < 0

theorem conditions_eventually (μ : ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc₂ : 0 < c₂) : ∀ᶠ w in 𝓝 seed, Conditions μ c₁ c₂ w := by
  obtain ⟨U,hUopen,hseed,hUreg,_⟩ := regular_analytic_neighborhood μ
  have hr : ∀ᶠ w in 𝓝 seed, Regular μ w :=
    Filter.Eventually.mono (hUopen.mem_nhds hseed) (fun w hw => hUreg w hw)
  have hb : ∀ᶠ w in 𝓝 seed, ∀ j, StrictActive seedC seedD (phasePoint μ w j) j := by
    apply eventually_all.mpr
    intro j
    apply strictActive_eventually (analytic_phasePoint_seed μ j).continuousAt
    rw [phasePoint_seed]
    exact (source_base_certificate j).active
  have ht : ∀ᶠ w in 𝓝 seed, ∀ q, StrictActive seedC seedD
      (trialPoint μ w (trialPhase q) (trialLength q)) (trialActive q) := by
    apply eventually_all.mpr
    intro q
    apply strictActive_eventually (analytic_trialPoint_seed μ (trialPhase q) (trialLength q)).continuousAt
    rw [trialPoint_seed]
    exact (source_trial_certificate q).active
  have hbp : ∀ᶠ w in 𝓝 seed, ∀ j, 0 < phaseValue μ w j := by
    apply eventually_all.mpr
    intro j
    apply (continuous_phaseValue_seed μ j).eventually
    apply eventually_gt_nhds
    change 0 < phaseValue μ seed j
    rw [phaseValue_seed,SeedOrbit.objective_of_active (source_base_certificate j).active]
    exact (source_base_certificate j).value_pos
  have htp : ∀ᶠ w in 𝓝 seed, ∀ q, 0 < trialValue μ w (trialPhase q) (trialLength q) := by
    apply eventually_all.mpr
    intro q
    apply (continuous_trialValue_seed μ (trialPhase q) (trialLength q)).eventually
    apply eventually_gt_nhds
    change 0 < trialValue μ seed (trialPhase q) (trialLength q)
    rw [trialValue_seed,SeedOrbit.objective_of_active (source_trial_certificate q).active]
    exact (source_trial_certificate q).value_pos
  have ha : ∀ᶠ w in 𝓝 seed, ∀ q, trialAccept q=true →
      0 < armijoMargin μ c₁ w (trialPhase q) (trialLength q) ∧
      0 < wolfeMargin μ c₂ w (trialPhase q) (trialLength q) (trialActive q) := by
    apply eventually_all.mpr
    intro q
    by_cases hq : trialAccept q=true
    · have hs := seed_accept_margins μ hc₁ hc₁' hc₂ q hq
      have h1 := (continuous_armijoMargin_seed μ c₁ (trialPhase q) (trialLength q)).eventually (eventually_gt_nhds hs.1)
      have h2 := (continuous_wolfeMargin_seed μ c₂ (trialPhase q) (trialActive q) (trialLength q)).eventually (eventually_gt_nhds hs.2)
      exact (h1.and h2).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  have hj : ∀ᶠ w in 𝓝 seed, ∀ q, trialAccept q=false →
      armijoMargin μ c₁ w (trialPhase q) (trialLength q) < 0 := by
    apply eventually_all.mpr
    intro q
    by_cases hq : trialAccept q=false
    · exact ((continuous_armijoMargin_seed μ c₁ (trialPhase q) (trialLength q)).eventually
        (eventually_lt_nhds (seed_reject_margin μ hc₁ q hq))).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [hr,hb,ht,hbp,htp,ha,hj] with w hr hb ht hbp htp ha hj
  exact ⟨hr,hb,ht,hbp,htp,ha,hj⟩

theorem oracle_neighborhood (μ : ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc₂ : 0 < c₂) :
    ∃ U : Set State, IsOpen U ∧ seed ∈ U ∧ (∀ w ∈ U, Conditions μ c₁ c₂ w) ∧
      AnalyticOnNhd ℝ (returnMap μ) U := by
  have he := (conditions_eventually μ hc₁ hc₁' hc₂).and (analytic_returnMap_seed μ).eventually_analyticAt
  obtain ⟨U,hU,hUopen,hseed⟩ := mem_nhds_iff.mp he
  exact ⟨U,hUopen,hseed,fun w hw => (hU hw).1,fun w hw => (hU hw).2⟩

def physicalPoint (μ : ℝ) (w : State) (j : Fin 3) : Vec 2 := scale w • phasePoint μ w j
def physicalMetric (μ : ℝ) (w : State) (j : Fin 3) : Mat 2 := scale w • phaseMetric μ w j

theorem physical_direction (μ : ℝ) (w : State) (j : Fin 3) :
    bfgsStep (physicalMetric μ w j) (phaseGradient μ w j) 1=scale w • direction μ w j :=
  bfgsStep_scale_matrix _ _ _ _

theorem physical_trial (μ : ℝ) (w : State) (j : Fin 3) (a : ℝ) :
    physicalPoint μ w j+a • bfgsStep (physicalMetric μ w j) (phaseGradient μ w j) 1=
      scale w • trialPoint μ w j a := by
  rw [physical_direction]
  exact SeedOrbit.scaled_trial _ _ _ _

theorem Conditions.phase_hasGradient {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) :
    HasFDerivAt (LQuadraticSeed.objective μ) (gradientFunctional (phaseGradient μ w j))
      (physicalPoint μ w j) := by
  have hh := objective_hasGradient_of_active μ ((hw.base_active j).scale hτ)
  rw [show LQuadraticSeed.branchGradient μ (scale w • phasePoint μ w j) j=phaseGradient μ w j from
    LNormalizedReturn.physical_branch_gradient μ (scale w) j (internal μ w j.val)] at hh
  exact hh

theorem Conditions.trial_hasGradient {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) :
    HasFDerivAt (LQuadraticSeed.objective μ)
      (gradientFunctional (trialGradient μ w (trialPhase q) (trialLength q) (trialActive q)))
      (scale w • trialPoint μ w (trialPhase q) (trialLength q)) := by
  have hh := objective_hasGradient_of_active μ ((hw.trial_active q).scale hτ)
  simpa only [LQuadraticSeed.branchGradient,trialGradient,smul_smul,add_comm] using hh

theorem Conditions.physical_accept {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) (hq : trialAccept q=true) :
    Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))
      (bfgsStep (physicalMetric μ w (trialPhase q)) (phaseGradient μ w (trialPhase q)) 1)
      (phaseGradient μ w (trialPhase q)) c₁ (trialLength q) ∧
    Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))
      (bfgsStep (physicalMetric μ w (trialPhase q)) (phaseGradient μ w (trialPhase q)) 1)
      (phaseGradient μ w (trialPhase q)) c₂ (trialLength q) := by
  obtain ⟨ha,hwf⟩ := hw.accepts q hq
  have ham : trialValue μ w (trialPhase q) (trialLength q) <
      phaseValue μ w (trialPhase q)+c₁*trialLength q*dot (phaseGradient μ w (trialPhase q)) (direction μ w (trialPhase q)) := by
    exact sub_pos.mp ha
  have hwm : c₂*dot (phaseGradient μ w (trialPhase q)) (direction μ w (trialPhase q)) <
      dot (trialGradient μ w (trialPhase q) (trialLength q) (trialActive q)) (direction μ w (trialPhase q)) := sub_pos.mp hwf
  have hg := actual_coordinateGradient (hw.trial_hasGradient hτ q)
  dsimp only [phaseValue,trialValue] at ham
  constructor
  · unfold Armijo
    rw [physical_trial,physical_direction,physicalPoint,
      physical_value_of_active μ hτ (hw.trial_active q),physical_value_of_active μ hτ (hw.base_active (trialPhase q)),dot_smul_right]
    convert mul_lt_mul_of_pos_left ham hτ using 1 <;> ring
  · unfold Wolfe
    rw [physical_trial,hg,physical_direction,dot_smul_right,dot_smul_right]
    convert mul_lt_mul_of_pos_left hwm hτ using 1 <;> ring

theorem Conditions.physical_reject {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) (hq : trialAccept q=false) :
    ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))
      (bfgsStep (physicalMetric μ w (trialPhase q)) (phaseGradient μ w (trialPhase q)) 1)
      (phaseGradient μ w (trialPhase q)) c₁ (trialLength q) := by
  have hm : phaseValue μ w (trialPhase q)+
      c₁*trialLength q*dot (phaseGradient μ w (trialPhase q)) (direction μ w (trialPhase q)) <
      trialValue μ w (trialPhase q) (trialLength q) := sub_neg.mp (hw.rejects q hq)
  dsimp only [phaseValue,trialValue] at hm
  apply not_lt_of_gt
  rw [physical_trial,physical_direction,physicalPoint,
    physical_value_of_active μ hτ (hw.trial_active q),physical_value_of_active μ hτ (hw.base_active (trialPhase q)),dot_smul_right]
  convert mul_lt_mul_of_pos_left hm hτ using 1 <;> ring


theorem Conditions.search_zero {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) :
    search (LQuadraticSeed.objective μ) (physicalPoint μ w 0) (bfgsStep (physicalMetric μ w 0) (phaseGradient μ w 0) 1) (phaseGradient μ w 0) c₁ c₂ 5 0 none 1 =
      (some (1),[1]) := by
  obtain ⟨ha,hW⟩ := hw.physical_accept hτ 0 rfl
  change Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 0) (bfgsStep (physicalMetric μ w 0) (phaseGradient μ w 0) 1) (phaseGradient μ w 0) c₁ (1) at ha
  change Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w 0) (bfgsStep (physicalMetric μ w 0) (phaseGradient μ w 0) 1) (phaseGradient μ w 0) c₂ (1) at hW
  exact search_accept 4 ha hW

theorem Conditions.search_one {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) :
    search (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ c₂ 5 0 none 1 =
      (some (1/4),[1,1/2,1/4]) := by
  have h1 := hw.physical_reject hτ 1 rfl
  have h2 := hw.physical_reject hτ 2 rfl
  obtain ⟨ha,hW⟩ := hw.physical_accept hτ 3 rfl
  change ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ (1) at h1
  change ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ (1/2) at h2
  change Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₁ (1/4) at ha
  change Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w 1) (bfgsStep (physicalMetric μ w 1) (phaseGradient μ w 1) 1) (phaseGradient μ w 1) c₂ (1/4) at hW
  rw [search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_accept 2 ha hW]
  exact ⟨rfl,rfl⟩

theorem Conditions.search_two {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) :
    search (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ c₂ 5 0 none 1 =
      (some (1/16),[1,1/2,1/4,1/8,1/16]) := by
  have h1 := hw.physical_reject hτ 4 rfl
  have h2 := hw.physical_reject hτ 5 rfl
  have h3 := hw.physical_reject hτ 6 rfl
  have h4 := hw.physical_reject hτ 7 rfl
  obtain ⟨ha,hW⟩ := hw.physical_accept hτ 8 rfl
  change ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1) at h1
  change ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/2) at h2
  change ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/4) at h3
  change ¬ Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/8) at h4
  change Armijo (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₁ (1/16) at ha
  change Wolfe (LQuadraticSeed.objective μ) (physicalPoint μ w 2) (bfgsStep (physicalMetric μ w 2) (phaseGradient μ w 2) 1) (phaseGradient μ w 2) c₂ (1/16) at hW
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
  rw [search_accept 0 ha hW]
  exact ⟨rfl,rfl⟩

theorem Conditions.fromMetric_search {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) :
    fromMetric (LQuadraticSeed.objective μ) (physicalPoint μ w j) (physicalMetric μ w j) c₁ c₂ 5 =
      (some (length j),trialHistory j) := by
  unfold fromMetric
  rw [actual_coordinateGradient (hw.phase_hasGradient hτ j)]
  fin_cases j
  · exact hw.search_zero hτ
  · exact hw.search_one hτ
  · exact hw.search_two hτ

theorem Conditions.all_trials_differentiable {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) :
    DifferentiableAt ℝ (LQuadraticSeed.objective μ)
      (physicalPoint μ w (trialPhase q)+trialLength q •
        bfgsStep (physicalMetric μ w (trialPhase q))
          (coordinateGradient (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))) 1) := by
  rw [actual_coordinateGradient (hw.phase_hasGradient hτ (trialPhase q)),physical_trial]
  exact (hw.trial_hasGradient hτ q).differentiableAt

def acceptedQuery (j : Fin 3) : Fin 9 := ![0,3,8] j

theorem acceptedQuery_spec (j : Fin 3) :
    trialPhase (acceptedQuery j)=j ∧ trialLength (acceptedQuery j)=length j ∧
      trialActive (acceptedQuery j)=nextPhase j ∧ trialAccept (acceptedQuery j)=true := by
  fin_cases j <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem internal_next (μ : ℝ) (w : State) (j : Fin 3) :
    internal μ w (j.val+1)=substep μ (scale w) j (internal μ w j.val) := by
  rw [internal]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

theorem accepted_trialPoint (μ : ℝ) (w : State) (j : Fin 3) :
    trialPoint μ w j (length j)=(internal μ w (j.val+1)).1 := by
  rw [internal_next]
  change _+length j • bfgsStep _ _ 1=_+bfgsStep _ _ (length j)
  congr 1
  simpa only [mul_one] using (bfgsStep_scale_alpha (phaseMetric μ w j) (phaseGradient μ w j) 1 (length j)).symm

theorem Conditions.accepted_hasGradient {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) :
    HasFDerivAt (LQuadraticSeed.objective μ)
      (gradientFunctional (LQuadraticSeed.branchGradient μ
        (scale w • (internal μ w (j.val+1)).1) (nextPhase j)))
      (scale w • (internal μ w (j.val+1)).1) := by
  have ha := hw.trial_active (acceptedQuery j)
  rw [(acceptedQuery_spec j).1,(acceptedQuery_spec j).2.1,(acceptedQuery_spec j).2.2.1,
    accepted_trialPoint] at ha
  exact objective_hasGradient_of_active μ (ha.scale hτ)

theorem accepted_displacement (μ : ℝ) (w : State) (j : Fin 3) :
    scale w • (internal μ w (j.val+1)).1-physicalPoint μ w j=
      scale w • step μ (scale w) j (internal μ w j.val) := by
  rw [internal_next]
  dsimp only [substep,physicalPoint,phasePoint]
  rw [smul_add,add_sub_cancel_left]

theorem Conditions.actual_point_update {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) :
    scale w • (internal μ w (j.val+1)).1=physicalPoint μ w j+
      bfgsStep (physicalMetric μ w j)
        (coordinateGradient (LQuadraticSeed.objective μ) (physicalPoint μ w j)) (length j) := by
  rw [actual_coordinateGradient (hw.phase_hasGradient hτ j)]
  change _=scale w • (internal μ w j.val).1+
    bfgsStep (scale w • (internal μ w j.val).2)
      (currentGradient μ (scale w) j (internal μ w j.val)) (length j)
  rw [← physical_branch_gradient μ (scale w) j (internal μ w j.val),physical_step,internal_next]
  exact smul_add _ _ _

theorem Conditions.actual_matrix_update {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) :
    inverseBFGS (physicalMetric μ w j)
      (scale w • (internal μ w (j.val+1)).1-physicalPoint μ w j)
      (coordinateGradient (LQuadraticSeed.objective μ) (scale w • (internal μ w (j.val+1)).1)-
        coordinateGradient (LQuadraticSeed.objective μ) (physicalPoint μ w j))=
      scale w • (internal μ w (j.val+1)).2 := by
  rw [actual_coordinateGradient (hw.accepted_hasGradient hτ j),
    actual_coordinateGradient (hw.phase_hasGradient hτ j),accepted_displacement]
  change inverseBFGS (scale w • (internal μ w j.val).2) _
    (LQuadraticSeed.branchGradient μ _ (nextPhase j)-currentGradient μ (scale w) j (internal μ w j.val))=_
  rw [← physical_branch_gradient μ (scale w) j (internal μ w j.val),internal_next,physical_secant]
  exact physical_update μ hτ.ne' j (internal μ w j.val)

theorem positive_smul_posDef {n : ℕ} {H : Mat n} (hH : H.PosDef) {r : ℝ} (hr : 0 < r) :
    (r • H).PosDef := by
  constructor
  · change (r • H)ᴴ=r • H
    rw [Matrix.conjTranspose_smul,star_trivial,hH.1.eq]
  · intro v hv
    simpa only [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul,star_trivial] using
      mul_pos hr (hH.2 v hv)

theorem Conditions.physicalMetric_posDef {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) : (physicalMetric μ w j).PosDef :=
  positive_smul_posDef (internal_posDef_of_regular μ hw.regular j.val (by omega)) hτ

theorem Conditions.physical_phase_positive {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (j : Fin 3) : 0 < LQuadraticSeed.objective μ (physicalPoint μ w j) := by
  rw [physicalPoint,physical_value_of_active μ hτ (hw.base_active j)]
  exact mul_pos hτ (hw.base_positive j)

theorem Conditions.physical_trial_positive {μ c₁ c₂ : ℝ} {w : State} (hw : Conditions μ c₁ c₂ w)
    (hτ : 0 < scale w) (q : Fin 9) :
    0 < LQuadraticSeed.objective μ (scale w • trialPoint μ w (trialPhase q) (trialLength q)) := by
  rw [physical_value_of_active μ hτ (hw.trial_active q)]
  exact mul_pos hτ (hw.trial_positive q)

/-- Actual three-step deterministic full-BFGS agreement for the source quadratic
objective on an open neighborhood of the normalized boundary seed. This theorem
does not assert existence of a forward orbit remaining in that neighborhood. -/
theorem actual_implementation_neighborhood (μ c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    ∃ U : Set State, IsOpen U ∧ seed∈U ∧ AnalyticOnNhd ℝ (returnMap μ) U ∧
      ∀ w∈U, 0 < scale w →
        (∀ j, (physicalMetric μ w j).PosDef ∧
          HasFDerivAt (LQuadraticSeed.objective μ) (gradientFunctional (phaseGradient μ w j)) (physicalPoint μ w j) ∧
          0 < LQuadraticSeed.objective μ (physicalPoint μ w j) ∧
          fromMetric (LQuadraticSeed.objective μ) (physicalPoint μ w j) (physicalMetric μ w j) c₁ c₂ 5 =
            (some (length j),trialHistory j) ∧
          scale w • (internal μ w (j.val+1)).1=physicalPoint μ w j+
            bfgsStep (physicalMetric μ w j)
              (coordinateGradient (LQuadraticSeed.objective μ) (physicalPoint μ w j)) (length j) ∧
          inverseBFGS (physicalMetric μ w j)
            (scale w • (internal μ w (j.val+1)).1-physicalPoint μ w j)
            (coordinateGradient (LQuadraticSeed.objective μ) (scale w • (internal μ w (j.val+1)).1)-
              coordinateGradient (LQuadraticSeed.objective μ) (physicalPoint μ w j))=
            scale w • (internal μ w (j.val+1)).2) ∧
        (∀ q, DifferentiableAt ℝ (LQuadraticSeed.objective μ)
          (physicalPoint μ w (trialPhase q)+trialLength q •
            bfgsStep (physicalMetric μ w (trialPhase q))
              (coordinateGradient (LQuadraticSeed.objective μ) (physicalPoint μ w (trialPhase q))) 1)) ∧
        (∀ q, 0 < LQuadraticSeed.objective μ (scale w • trialPoint μ w (trialPhase q) (trialLength q))) ∧
        0 < returnFactor μ w ∧
        scale (returnMap μ w) • point (returnMap μ w)=scale w • (internal μ w 3).1 ∧
        scale (returnMap μ w) • shape (returnMap μ w)=scale w • (internal μ w 3).2 := by
  obtain ⟨U,hU,hs,hw,ha⟩ := oracle_neighborhood μ hc₁ hc₁' hc₂
  refine ⟨U,hU,hs,ha,?_⟩
  intro w huw hτ
  have h := hw w huw
  refine ⟨?_,h.all_trials_differentiable hτ,h.physical_trial_positive hτ,h.regular.2.1,
    normalization_preserves_point μ w h.regular.2.1.ne',normalization_preserves_metric μ w h.regular.2.1.ne'⟩
  intro j
  exact ⟨h.physicalMetric_posDef hτ j,h.phase_hasGradient hτ j,h.physical_phase_positive hτ j,
    h.fromMetric_search hτ j,h.actual_point_update hτ j,h.actual_matrix_update hτ j⟩

end BfgsVerification.LNormalizedOracle
