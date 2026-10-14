import BfgsArticle.LNonStrictGlobal
import BfgsVerification.LReturnStableOrbit
import BfgsVerification.LFlattenNeighborhood

/-!
# One lower-curvature orbit for every admissible line-search pair

`LGlobalFailure.actual_global_failure` and `nonstrict_actual_global_failure` choose
their orbit after the constants `0<c₁≤1/3`, `c₁<c₂<1`. Here one orbit is chosen
first and serves every such pair.

Every decision margin of `LNormalizedOracle.Conditions` is affine in its constant.
At the seed the certificate gives the margins at the corners: an accepted trial
passes Armijo with `c₁=1/3`, lowers the value (`c₁=0`) and has a positive new
directional derivative (`c₂=0`); a rejected trial raises the value. The corner
margins persist on one neighbourhood of the seed (`uniform_conditions_eventually`)
and imply `Conditions μ c₁ c₂` for all `0≤c₁≤1/3`, `0≤c₂≤1` at once
(`UniformConditions.conditions`). The stable-manifold orbit is then chosen inside
that neighbourhood (`uniform_oracle_orbit`).
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification.LNormalizedOracle
open SeedCycle SeedOrbit LNormalizedReturn
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- At the seed, an accepted trial lowers the value (Armijo margin at `c₁=0`) and has
positive new directional derivative (Wolfe margin at `c₂=0`). -/
theorem seed_accept_zero_margins (μ : ℝ) (q : Fin 9) (hq : trialAccept q=true) :
    0 < armijoMargin μ 0 seed (trialPhase q) (trialLength q) ∧
    0 < wolfeMargin μ 0 seed (trialPhase q) (trialLength q) (trialActive q) := by
  have h := source_trial_certificate q
  rw [hq] at h
  have hbase := (source_base_certificate (trialPhase q)).active
  have hd := h.descent
  have ha := h.decision
  have hw := h.wolfe rfl
  simp only [Bool.true_eq,ite_true] at ha
  rw [dot_smul_right] at hd hw ha
  have hl := source_trial_length_pos q
  constructor
  · simp only [armijoMargin,phaseValue_seed,trialValue_seed,phaseGradient_seed,direction_seed,
      zero_mul]
    rw [SeedOrbit.objective_of_active h.active,SeedOrbit.objective_of_active hbase]
    linarith
  · simp only [wolfeMargin,trialGradient_seed,phaseGradient_seed,direction_seed,zero_mul,sub_zero]
    nlinarith

/-- At the seed, a rejected trial raises the value (Armijo margin at `c₁=0`). -/
theorem seed_reject_zero_margin (μ : ℝ) (q : Fin 9) (hq : trialAccept q=false) :
    armijoMargin μ 0 seed (trialPhase q) (trialLength q) < 0 := by
  have h := source_trial_certificate q
  rw [hq] at h
  have ha := h.decision
  simp only [Bool.false_eq_true,ite_false] at ha
  simp only [armijoMargin,phaseValue_seed,trialValue_seed,phaseGradient_seed,direction_seed,
    zero_mul]
  rw [SeedOrbit.objective_of_active h.active,
    SeedOrbit.objective_of_active (source_base_certificate (trialPhase q)).active]
  linarith

/-- The decision margins at the corners `c₁∈{0,1/3}` and `c₂∈{0,1}`. -/
structure UniformConditions (μ : ℝ) (w : State) : Prop where
  corner : Conditions μ (1/3) 1 w
  accepts_zero : ∀ q, trialAccept q=true →
    0 < armijoMargin μ 0 w (trialPhase q) (trialLength q) ∧
    0 < wolfeMargin μ 0 w (trialPhase q) (trialLength q) (trialActive q)
  rejects_zero : ∀ q, trialAccept q=false → armijoMargin μ 0 w (trialPhase q) (trialLength q) < 0

theorem armijoMargin_interpolate (μ c₁ : ℝ) (w : State) (j : Fin 3) (a : ℝ) :
    armijoMargin μ c₁ w j a=(1-3*c₁)*armijoMargin μ 0 w j a+(3*c₁)*armijoMargin μ (1/3) w j a := by
  simp only [armijoMargin]
  ring

theorem wolfeMargin_interpolate (μ c₂ : ℝ) (w : State) (j : Fin 3) (a : ℝ) (i : Fin 3) :
    wolfeMargin μ c₂ w j a i=(1-c₂)*wolfeMargin μ 0 w j a i+c₂*wolfeMargin μ 1 w j a i := by
  simp only [wolfeMargin]
  ring

theorem interpolate_pos {s x y : ℝ} (hs : 0≤s) (hs' : s≤1) (hx : 0<x) (hy : 0<y) :
    0<(1-s)*x+s*y := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    simpa using hx
  · nlinarith [mul_pos h hy,mul_nonneg (sub_nonneg.mpr hs') hx.le]

theorem interpolate_neg {s x y : ℝ} (hs : 0≤s) (hs' : s≤1) (hx : x<0) (hy : y<0) :
    (1-s)*x+s*y<0 := by
  have h := interpolate_pos hs hs' (neg_pos.mpr hx) (neg_pos.mpr hy)
  have e : (1-s)*(-x)+s*(-y)=-((1-s)*x+s*y) := by ring
  linarith

/-- The corner margins give the full oracle conditions for every `0≤c₁≤1/3` and
`0≤c₂≤1`, with the same state. -/
theorem UniformConditions.conditions {μ : ℝ} {w : State} (hw : UniformConditions μ w)
    {c₁ c₂ : ℝ} (hc₁ : 0≤c₁) (hc₁' : c₁≤1/3) (hc₂ : 0≤c₂) (hc₂' : c₂≤1) :
    Conditions μ c₁ c₂ w where
  regular := hw.corner.regular
  base_active := hw.corner.base_active
  trial_active := hw.corner.trial_active
  base_positive := hw.corner.base_positive
  trial_positive := hw.corner.trial_positive
  accepts q hq := by
    obtain ⟨h0,hW0⟩ := hw.accepts_zero q hq
    obtain ⟨h3,hW1⟩ := hw.corner.accepts q hq
    refine ⟨?_,?_⟩
    · rw [armijoMargin_interpolate]
      exact interpolate_pos (by linarith) (by linarith) h0 h3
    · rw [wolfeMargin_interpolate]
      exact interpolate_pos hc₂ hc₂' hW0 hW1
  rejects q hq := by
    rw [armijoMargin_interpolate]
    exact interpolate_neg (by linarith) (by linarith) (hw.rejects_zero q hq) (hw.corner.rejects q hq)

theorem uniform_conditions_eventually (μ : ℝ) : ∀ᶠ w in 𝓝 seed, UniformConditions μ w := by
  have hc := conditions_eventually μ (c₁ := 1/3) (c₂ := 1) (by norm_num) (by norm_num) (by norm_num)
  have ha : ∀ᶠ w in 𝓝 seed, ∀ q, trialAccept q=true →
      0 < armijoMargin μ 0 w (trialPhase q) (trialLength q) ∧
      0 < wolfeMargin μ 0 w (trialPhase q) (trialLength q) (trialActive q) := by
    apply eventually_all.mpr
    intro q
    by_cases hq : trialAccept q=true
    · have hs := seed_accept_zero_margins μ q hq
      have h1 := (continuous_armijoMargin_seed μ 0 (trialPhase q) (trialLength q)).eventually
        (eventually_gt_nhds hs.1)
      have h2 := (continuous_wolfeMargin_seed μ 0 (trialPhase q) (trialActive q) (trialLength q)).eventually
        (eventually_gt_nhds hs.2)
      exact (h1.and h2).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  have hj : ∀ᶠ w in 𝓝 seed, ∀ q, trialAccept q=false →
      armijoMargin μ 0 w (trialPhase q) (trialLength q) < 0 := by
    apply eventually_all.mpr
    intro q
    by_cases hq : trialAccept q=false
    · exact ((continuous_armijoMargin_seed μ 0 (trialPhase q) (trialLength q)).eventually
        (eventually_lt_nhds (seed_reject_zero_margin μ q hq))).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [hc,ha,hj] with w hc ha hj
  exact ⟨hc,ha,hj⟩

/-- `LReturnStableOrbit.source_oracle_orbit` with the corner margins, so that the
orbit does not depend on the line-search constants. -/
theorem uniform_oracle_orbit (μ : ℝ) (V : Set State) (hV : V∈𝓝 seed) :
    ∃ w : ℕ → State, (∀ n, w n∈V) ∧ Tendsto w atTop (𝓝 seed) ∧
      (∀ n, 0<scale (w n)) ∧ (∀ n, UniformConditions μ (w n)) ∧
      ∀ n, w (n+1)=returnMap μ (w n) := by
  obtain ⟨w,hw,ht,h0,hrec⟩ := LReturnStableOrbit.source_positive_return_orbit μ
    (V∩{w | UniformConditions μ w}) (Filter.inter_mem hV (uniform_conditions_eventually μ))
  have hpos : ∀ n, 0<scale (w n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n hn =>
      rw [hrec,return_scale]
      exact mul_pos hn (hw n).2.corner.regular.2.1
  exact ⟨w,fun n => (hw n).1,ht,hpos,fun n => (hw n).2,hrec⟩

end BfgsVerification.LNormalizedOracle

namespace BfgsVerification.LUniform
open SeedOrbit SeedCycle LNormalizedReturn LNormalizedOracle
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The admissible line-search constants of Theorems `art:local-failure` and
`art:local-failure-lower`. -/
structure Admissible (c₁ c₂ : ℝ) : Prop where
  pos : 0<c₁
  le_third : c₁≤1/3
  lt : c₁<c₂
  lt_one : c₂<1

/-- A normalized return orbit along which every admissible pair makes the same decisions. -/
structure Orbit (μ : ℝ) where
  state : ℕ → State
  scale_pos : ∀ m, 0<scale (state m)
  conditions : ∀ m, UniformConditions μ (state m)
  next : ∀ m, state (m+1)=returnMap μ (state m)

namespace Orbit
variable {μ : ℝ}

/-- The finite-step data for one pair; only the conditions field depends on the pair. -/
def data (O : Orbit μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) : LFlatten.Data μ c₁ c₂ :=
  ⟨O.state,O.scale_pos,
    fun m => (O.conditions m).conditions h.pos.le h.le_third (h.pos.trans h.lt).le h.lt_one.le,O.next⟩

def x (O : Orbit μ) (k : ℕ) : Vec 2 := physicalPoint μ (O.state (period k)) (phase k)
def H (O : Orbit μ) (k : ℕ) : Mat 2 := physicalMetric μ (O.state (period k)) (phase k)
def g (O : Orbit μ) (k : ℕ) : Vec 2 := coordinateGradient (LQuadraticSeed.objective μ) (O.x k)

/-- The actual run for one admissible pair. -/
def run (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) :
    AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ) :=
  (O.data h).run hμ h.pos h.lt h.lt_one

theorem run_x (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) : (O.run hμ h).x=O.x := rfl
theorem run_H (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) : (O.run hμ h).H=O.H := rfl
theorem run_g (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) : (O.run hμ h).g=O.g := rfl
theorem run_alpha (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) (k : ℕ) :
    (O.run hμ h).α k=length (phase k) := rfl
theorem run_c₁ (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) : (O.run hμ h).c₁=c₁ := rfl
theorem run_c₂ (O : Orbit μ) (hμ : 0≤μ) {c₁ c₂ : ℝ} (h : Admissible c₁ c₂) : (O.run hμ h).c₂=c₂ := rfl

theorem initial_posDef (O : Orbit μ) : (O.H 0).PosDef :=
  (O.data (c₁ := 1/10000) (c₂ := 1/2) ⟨by norm_num,by norm_num,by norm_num,by norm_num⟩).positive_metric 0

end Orbit

/-- One orbit, chosen before the constants, whose accepted points and nine queries per
step all lie in a prescribed neighbourhood of the origin. -/
theorem orbit_exists (μ : ℝ) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ O : Orbit μ, Tendsto O.state atTop (𝓝 seed) ∧ (∀ k, O.x k∈U) ∧
      ∀ k q, trialPhase q=phase k → O.x k+trialLength q • bfgsStep (O.H k) (O.g k) 1∈U := by
  obtain ⟨V,hVo,hVs,hV⟩ := LFlatten.physical_neighborhood μ U hU
  obtain ⟨w,hw,ht,hp,hc,hn⟩ := uniform_oracle_orbit μ V (hVo.mem_nhds hVs)
  let O : Orbit μ := ⟨w,hp,hc,hn⟩
  obtain ⟨h1,h2⟩ := (O.data (c₁ := 1/10000) (c₂ := 1/2)
    ⟨by norm_num,by norm_num,by norm_num,by norm_num⟩).whole_run_in_neighborhood (U := U) hw hV
  exact ⟨O,ht,h1,h2⟩

/-- Proposition `art:quadratic_failure`, uniform in the line-search constants: one
trajectory `x`, `H` is an actual run of the article's deterministic search for every
`0<c₁≤1/3`, `c₁<c₂<1`, with the same complete non-strict and strict traces. -/
theorem uniform_global_failure {μ : ℝ} (hμ : 0<μ) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ x : ℕ → Vec 2, ∃ H : ℕ → Mat 2, (H 0).PosDef ∧
      ∀ c₁ c₂ : ℝ, 0<c₁ → c₁≤1/3 → c₁<c₂ → c₂<1 →
      ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
        R.x=x ∧ R.H=H ∧ R.c₁=c₁ ∧ R.c₂=c₂ ∧
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
  obtain ⟨O,ht,hp,hq⟩ := orbit_exists μ U hU
  refine ⟨O.x,O.H,O.initial_posDef,?_⟩
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  have h : Admissible c₁ c₂ := ⟨hc₁,hc₁',hc,hc₂⟩
  obtain ⟨hx,hH,hv,hpos,hdec,hsearch,hdiff,hqt,hnon⟩ := (O.data h).failure_contract hμ.le hc₁ hc hc₂ ht
  refine ⟨O.run hμ.le h,rfl,rfl,rfl,rfl,hx,hH,hv,hpos,hdec,fun _ => rfl,
    (O.data h).nonstrict_actual_search,hsearch,hp,?_,hqt,(O.data h).strict_accept,hnon⟩
  intro k q hphase
  exact ⟨hdiff k q hphase,(O.data h).all_trial_values_positive k q hphase,hq k q hphase⟩

end BfgsVerification.LUniform
