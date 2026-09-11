import BfgsVerification.LQuadraticSeed
import BfgsVerification.AlgebraicSeedFiniteCycle
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.ChangeOrigin

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LNormalizedReturn
open SeedCycle SeedOrbit
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev State := Vec 5
abbrev PhaseState := Vec 2 × Mat 2

def point (w : State) : Vec 2 := ![w 0,w 1]
def shape (w : State) : Mat 2 := !![1,w 2;w 2,w 3]
def scale (w : State) : ℝ := w 4
def initial (w : State) : PhaseState := (point w,shape w)
def currentGradient (μ τ : ℝ) (j : Fin 3) (s : PhaseState) : Vec 2 :=
  SeedOrbit.gradient seedC seedD j+(μ*τ) • s.1
def step (μ τ : ℝ) (j : Fin 3) (s : PhaseState) : Vec 2 :=
  bfgsStep s.2 (currentGradient μ τ j s) (length j)
def secant (μ τ : ℝ) (j : Fin 3) (s : PhaseState) : Vec 2 :=
  SeedOrbit.gradient seedC seedD (nextPhase j)-SeedOrbit.gradient seedC seedD j+(μ*τ) • step μ τ j s
def curvature (μ τ : ℝ) (j : Fin 3) (s : PhaseState) : ℝ :=
  dot (secant μ τ j s) (step μ τ j s)
def substep (μ τ : ℝ) (j : Fin 3) (s : PhaseState) : PhaseState :=
  (s.1+step μ τ j s,inverseBFGS s.2 (step μ τ j s) (secant μ τ j s))

/-- The input scale is held fixed throughout these three substeps. -/
def internal (μ : ℝ) (w : State) : ℕ → PhaseState
  | 0 => initial w
  | k+1 => substep μ (scale w) (phase k) (internal μ w k)

def denominator (μ : ℝ) (w : State) (j : Fin 3) : ℝ :=
  curvature μ (scale w) j (internal μ w j.val)
def returnFactor (μ : ℝ) (w : State) : ℝ := (internal μ w 3).2 0 0
def returnMap (μ : ℝ) (w : State) : State :=
  ![(internal μ w 3).1 0/returnFactor μ w,
    (internal μ w 3).1 1/returnFactor μ w,
    (internal μ w 3).2 0 1/returnFactor μ w,
    (internal μ w 3).2 1 1/returnFactor μ w,
    scale w*returnFactor μ w]
def seed : State :=
  ![(SeedOrbit.point seedC seedD seedRatio 0) 0,(SeedOrbit.point seedC seedD seedRatio 0) 1,0,1,0]
def Regular (μ : ℝ) (w : State) : Prop :=
  (∀ j, 0 < denominator μ w j) ∧ 0 < returnFactor μ w ∧ (w 2)^2 < w 3

@[simp] theorem currentGradient_zero (μ : ℝ) (j : Fin 3) (s : PhaseState) :
    currentGradient μ 0 j s=SeedOrbit.gradient seedC seedD j := by
  simp [currentGradient]
@[simp] theorem step_zero (μ : ℝ) (j : Fin 3) (s : PhaseState) :
    step μ 0 j s=bfgsStep s.2 (SeedOrbit.gradient seedC seedD j) (length j) := by
  simp [step]
@[simp] theorem secant_zero (μ : ℝ) (j : Fin 3) (s : PhaseState) :
    secant μ 0 j s=SeedOrbit.gradient seedC seedD (nextPhase j)-SeedOrbit.gradient seedC seedD j := by
  simp [secant]

theorem substep_zero (μ : ℝ) (j : Fin 3) (s : PhaseState) :
    substep μ 0 j s=(s.1+bfgsStep s.2 (SeedOrbit.gradient seedC seedD j) (length j),
      SeedCycle.update s.2 (SeedOrbit.gradient seedC seedD j)
        (SeedOrbit.gradient seedC seedD (nextPhase j)) (length j)) := by
  simp only [substep,step_zero,secant_zero,SeedCycle.update]

@[simp] theorem seed_point : point seed=SeedOrbit.point seedC seedD seedRatio 0 := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem seed_shape : shape seed=(1 : Mat 2) := by
  change !![1,0;0,1]=(1 : Mat 2)
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
@[simp] theorem seed_scale : scale seed=0 := rfl

theorem internal_seed_zero (μ : ℝ) :
    internal μ seed 0=(SeedOrbit.point seedC seedD seedRatio 0,metric seedC seedD 0) := by
  simp [internal,initial,metric]

theorem internal_seed_one (μ : ℝ) :
    internal μ seed 1=(SeedOrbit.point seedC seedD seedRatio 1,metric seedC seedD 1) := by
  rw [internal,seed_scale,internal_seed_zero]
  change substep μ 0 0 (SeedOrbit.point seedC seedD seedRatio 0,metric seedC seedD 0)=_
  rw [substep_zero]
  apply Prod.ext
  · change SeedOrbit.point seedC seedD seedRatio 0+
      bfgsStep (metric seedC seedD 0) (SeedOrbit.gradient seedC seedD 0) (length 0)=_
    rw [source_direction]
    exact phase_zero_step seedC seedD seedRatio
  · exact source_metric_zero_update

theorem internal_seed_two (μ : ℝ) :
    internal μ seed 2=(SeedOrbit.point seedC seedD seedRatio 2,metric seedC seedD 2) := by
  rw [internal,seed_scale,internal_seed_one]
  change substep μ 0 1 (SeedOrbit.point seedC seedD seedRatio 1,metric seedC seedD 1)=_
  rw [substep_zero]
  apply Prod.ext
  · change SeedOrbit.point seedC seedD seedRatio 1+
      bfgsStep (metric seedC seedD 1) (SeedOrbit.gradient seedC seedD 1) (length 1)=_
    rw [source_direction]
    exact phase_one_step seedC seedD seedRatio
  · exact source_metric_one_update

theorem internal_seed_three (μ : ℝ) :
    internal μ seed 3=(seedRatio • SeedOrbit.point seedC seedD seedRatio 0,seedRatio • (1 : Mat 2)) := by
  rw [internal,seed_scale,internal_seed_two]
  change substep μ 0 2 (SeedOrbit.point seedC seedD seedRatio 2,metric seedC seedD 2)=_
  rw [substep_zero]
  apply Prod.ext
  · change SeedOrbit.point seedC seedD seedRatio 2+
      bfgsStep (metric seedC seedD 2) (SeedOrbit.gradient seedC seedD 2) (length 2)=_
    rw [source_direction]
    exact source_phase_two_step
  · exact source_metric_two_update

theorem internal_seed_phase (μ : ℝ) (j : Fin 3) :
    internal μ seed j.val=(SeedOrbit.point seedC seedD seedRatio j,metric seedC seedD j) := by
  fin_cases j
  · exact internal_seed_zero μ
  · exact internal_seed_one μ
  · exact internal_seed_two μ

theorem seed_curvature_positive (j : Fin 3) :
    0 < dot (SeedOrbit.gradient seedC seedD (nextPhase j)-SeedOrbit.gradient seedC seedD j)
      (bfgsStep (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) (length j)) := by
  have h := source_accepted_certificate j
  rw [source_direction]
  change 0 < dotProduct (SeedOrbit.gradient seedC seedD (nextPhase j)-SeedOrbit.gradient seedC seedD j)
    (length j • direction seedC seedD seedRatio j)
  rw [sub_dotProduct]
  change 0 < dot (SeedOrbit.gradient seedC seedD (nextPhase j)) (length j • direction seedC seedD seedRatio j)-
    dot (SeedOrbit.gradient seedC seedD j) (length j • direction seedC seedD seedRatio j)
  linarith [h.descent,h.wolfe rfl]

theorem seed_denominator_positive (μ : ℝ) (j : Fin 3) : 0 < denominator μ seed j := by
  simp only [denominator,seed_scale,internal_seed_phase,curvature,secant_zero,step_zero]
  exact seed_curvature_positive j

theorem seed_returnFactor (μ : ℝ) : returnFactor μ seed=seedRatio := by
  simp [returnFactor,internal_seed_three]

theorem seed_regular (μ : ℝ) : Regular μ seed := by
  refine ⟨seed_denominator_positive μ,?_,?_⟩
  · rw [seed_returnFactor]
    exact source_ratio_pos_lt_one.1
  · change (0 : ℝ)^2 < 1
    norm_num

theorem seed_fixed (μ : ℝ) : returnMap μ seed=seed := by
  rw [returnMap,internal_seed_three,seed_returnFactor,seed_scale]
  ext i
  fin_cases i <;> simp [seed,Matrix.cons_val_succ,
    source_ratio_pos_lt_one.1.ne']

theorem analytic_coordinate (w : State) (i : Fin 5) :
    AnalyticAt ℝ (fun z : State => z i) w :=
  (ContinuousLinearMap.proj i : State →L[ℝ] ℝ).analyticAt w

theorem analytic_point (w : State) : AnalyticAt ℝ point w := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analytic_coordinate w 0
  · exact analytic_coordinate w 1

theorem analytic_shape (w : State) : AnalyticAt ℝ shape w := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  fin_cases i <;> fin_cases j
  · exact analyticAt_const
  · exact analytic_coordinate w 2
  · exact analytic_coordinate w 2
  · exact analytic_coordinate w 3

theorem analytic_scale (w : State) : AnalyticAt ℝ scale w := analytic_coordinate w 4

theorem analytic_initial (w : State) : AnalyticAt ℝ initial w :=
  (analytic_point w).prod (analytic_shape w)

theorem analytic_vec_entry {f : State → Vec 2} {w : State} (hf : AnalyticAt ℝ f w) (i : Fin 2) :
    AnalyticAt ℝ (fun z => f z i) w := analyticAt_pi_iff.mp hf i

theorem analytic_matrix_entry {f : State → Mat 2} {w : State} (hf : AnalyticAt ℝ f w) (i j : Fin 2) :
    AnalyticAt ℝ (fun z => f z i j) w := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hf i) j

theorem analytic_dot {f g : State → Vec 2} {w : State}
    (hf : AnalyticAt ℝ f w) (hg : AnalyticAt ℝ g w) :
    AnalyticAt ℝ (fun z => dot (f z) (g z)) w := by
  unfold dot
  simp only [Fin.sum_univ_two]
  exact ((analytic_vec_entry hf 0).mul (analytic_vec_entry hg 0)).add
    ((analytic_vec_entry hf 1).mul (analytic_vec_entry hg 1))

theorem analytic_outer {f g : State → Vec 2} {w : State}
    (hf : AnalyticAt ℝ f w) (hg : AnalyticAt ℝ g w) :
    AnalyticAt ℝ (fun z => outer (f z) (g z)) w := by
  exact AnalyticAt.pi (fun i => AnalyticAt.pi (fun j => (analytic_vec_entry hf i).mul (analytic_vec_entry hg j)))

theorem analytic_matrix_mul {f g : State → Mat 2} {w : State}
    (hf : AnalyticAt ℝ f w) (hg : AnalyticAt ℝ g w) :
    AnalyticAt ℝ (fun z => f z*g z) w := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  exact ((analytic_matrix_entry hf i 0).mul (analytic_matrix_entry hg 0 j)).add
    ((analytic_matrix_entry hf i 1).mul (analytic_matrix_entry hg 1 j))

theorem analytic_mulVec {f : State → Mat 2} {g : State → Vec 2} {w : State}
    (hf : AnalyticAt ℝ f w) (hg : AnalyticAt ℝ g w) :
    AnalyticAt ℝ (fun z => (f z).mulVec (g z)) w := by
  apply AnalyticAt.pi
  intro i
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  exact ((analytic_matrix_entry hf i 0).mul (analytic_vec_entry hg 0)).add
    ((analytic_matrix_entry hf i 1).mul (analytic_vec_entry hg 1))

theorem analytic_inverseBFGS {H : State → Mat 2} {s y : State → Vec 2} {w : State}
    (hH : AnalyticAt ℝ H w) (hs : AnalyticAt ℝ s w) (hy : AnalyticAt ℝ y w)
    (ht : dot (y w) (s w) ≠ 0) :
    AnalyticAt ℝ (fun z => inverseBFGS (H z) (s z) (y z)) w := by
  have hi := (analytic_dot hy hs).inv ht
  have hL := (analyticAt_const (v := (1 : Mat 2))).sub (hi.smul (analytic_outer hs hy))
  have hR := (analyticAt_const (v := (1 : Mat 2))).sub (hi.smul (analytic_outer hy hs))
  exact (analytic_matrix_mul (analytic_matrix_mul hL hH) hR).add (hi.smul (analytic_outer hs hs))

theorem analytic_currentGradient (μ : ℝ) (j : Fin 3)
    {τ : State → ℝ} {s : State → PhaseState} {w : State}
    (hτ : AnalyticAt ℝ τ w) (hs : AnalyticAt ℝ s w) :
    AnalyticAt ℝ (fun z => currentGradient μ (τ z) j (s z)) w :=
  analyticAt_const.add ((analyticAt_const.mul hτ).smul (analyticAt_fst.comp hs))

theorem analytic_step (μ : ℝ) (j : Fin 3)
    {τ : State → ℝ} {s : State → PhaseState} {w : State}
    (hτ : AnalyticAt ℝ τ w) (hs : AnalyticAt ℝ s w) :
    AnalyticAt ℝ (fun z => step μ (τ z) j (s z)) w :=
  (analytic_mulVec (analyticAt_snd.comp hs) (analytic_currentGradient μ j hτ hs)).const_smul (c := -length j)

theorem analytic_secant (μ : ℝ) (j : Fin 3)
    {τ : State → ℝ} {s : State → PhaseState} {w : State}
    (hτ : AnalyticAt ℝ τ w) (hs : AnalyticAt ℝ s w) :
    AnalyticAt ℝ (fun z => secant μ (τ z) j (s z)) w :=
  analyticAt_const.add ((analyticAt_const.mul hτ).smul (analytic_step μ j hτ hs))

theorem analytic_curvature (μ : ℝ) (j : Fin 3)
    {τ : State → ℝ} {s : State → PhaseState} {w : State}
    (hτ : AnalyticAt ℝ τ w) (hs : AnalyticAt ℝ s w) :
    AnalyticAt ℝ (fun z => curvature μ (τ z) j (s z)) w :=
  analytic_dot (analytic_secant μ j hτ hs) (analytic_step μ j hτ hs)

theorem analytic_substep (μ : ℝ) (j : Fin 3)
    {τ : State → ℝ} {s : State → PhaseState} {w : State}
    (hτ : AnalyticAt ℝ τ w) (hs : AnalyticAt ℝ s w)
    (ht : curvature μ (τ w) j (s w) ≠ 0) :
    AnalyticAt ℝ (fun z => substep μ (τ z) j (s z)) w :=
  ((analyticAt_fst.comp hs).add (analytic_step μ j hτ hs)).prod
    (analytic_inverseBFGS (analyticAt_snd.comp hs) (analytic_step μ j hτ hs)
      (analytic_secant μ j hτ hs) ht)

theorem analytic_internal_seed (μ : ℝ) (k : ℕ) (hk : k ≤ 3) :
    AnalyticAt ℝ (fun w => internal μ w k) seed := by
  induction k with
  | zero => exact analytic_initial seed
  | succ k ih =>
    have hk' : k < 3 := by omega
    have hj : phase k=(⟨k,hk'⟩ : Fin 3) := Fin.ext (Nat.mod_eq_of_lt hk')
    apply analytic_substep μ (phase k) (analytic_scale seed) (ih (by omega))
    rw [hj]
    exact (seed_denominator_positive μ ⟨k,hk'⟩).ne'

theorem analytic_denominator_seed (μ : ℝ) (j : Fin 3) :
    AnalyticAt ℝ (fun w => denominator μ w j) seed :=
  analytic_curvature μ j (analytic_scale seed) (analytic_internal_seed μ j.val (by omega))

theorem analytic_returnFactor_seed (μ : ℝ) : AnalyticAt ℝ (returnFactor μ) seed :=
  analytic_matrix_entry (analyticAt_snd.comp (analytic_internal_seed μ 3 (le_refl 3))) 0 0

theorem analytic_returnMap_seed (μ : ℝ) : AnalyticAt ℝ (returnMap μ) seed := by
  have hr := analytic_returnFactor_seed μ
  have hr0 : returnFactor μ seed ≠ 0 := (seed_regular μ).2.1.ne'
  have hi := analytic_internal_seed μ 3 (le_refl 3)
  have hp := analyticAt_fst.comp hi
  have hM := analyticAt_snd.comp hi
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (analytic_vec_entry hp 0).div hr hr0
  · exact (analytic_vec_entry hp 1).div hr hr0
  · exact (analytic_matrix_entry hM 0 1).div hr hr0
  · exact (analytic_matrix_entry hM 1 1).div hr hr0
  · exact (analytic_scale seed).mul hr

theorem regular_analytic_neighborhood (μ : ℝ) :
    ∃ U : Set State, IsOpen U ∧ seed ∈ U ∧ (∀ w ∈ U, Regular μ w) ∧
      AnalyticOnNhd ℝ (returnMap μ) U := by
  have hd : ∀ᶠ w in 𝓝 seed, ∀ j, 0 < denominator μ w j := by
    apply eventually_all.mpr
    intro j
    exact (analytic_denominator_seed μ j).continuousAt.eventually
      (eventually_gt_nhds (seed_denominator_positive μ j))
  have hr : ∀ᶠ w in 𝓝 seed, 0 < returnFactor μ w :=
    (analytic_returnFactor_seed μ).continuousAt.eventually (eventually_gt_nhds (seed_regular μ).2.1)
  have hh : ∀ᶠ w in 𝓝 seed, (w 2)^2 < w 3 := by
    have hc : ContinuousAt (fun w : State => w 3-(w 2)^2) seed := by fun_prop
    have hp : 0 < seed 3-(seed 2)^2 := by change (0 : ℝ)<1-0^2; norm_num
    simpa only [sub_pos] using hc.eventually (eventually_gt_nhds hp)
  have he : ∀ᶠ w in 𝓝 seed, Regular μ w ∧ AnalyticAt ℝ (returnMap μ) w := by
    filter_upwards [hd,hr,hh,(analytic_returnMap_seed μ).eventually_analyticAt] with w hd hr hh ha
    exact ⟨⟨hd,hr,hh⟩,ha⟩
  obtain ⟨U,hU,hUopen,hseed⟩ := mem_nhds_iff.mp he
  exact ⟨U,hUopen,hseed,fun w hw => (hU hw).1,fun w hw => (hU hw).2⟩

theorem inverseBFGS_isSymm {H : Mat 2} (hH : H.IsSymm) (s y : Vec 2) :
    (inverseBFGS H s y).IsSymm := by
  change (inverseBFGS H s y)ᵀ=inverseBFGS H s y
  simp only [inverseBFGS,Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_sub,
    Matrix.transpose_one,Matrix.transpose_smul,outer_transpose,hH.eq,Matrix.mul_assoc]

theorem shape_isSymm (w : State) : (shape w).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem internal_isSymm (μ : ℝ) (w : State) (k : ℕ) : (internal μ w k).2.IsSymm := by
  induction k with
  | zero => exact shape_isSymm w
  | succ k ih => exact inverseBFGS_isSymm ih _ _

@[simp] theorem return_scale (μ : ℝ) (w : State) :
    scale (returnMap μ w)=scale w*returnFactor μ w := rfl

theorem return_point (μ : ℝ) (w : State) :
    point (returnMap μ w)=(returnFactor μ w)⁻¹ • (internal μ w 3).1 := by
  ext i
  fin_cases i <;> simp [point,returnMap,div_eq_mul_inv,mul_comm]

theorem return_shape (μ : ℝ) (w : State) (hr : returnFactor μ w ≠ 0) :
    shape (returnMap μ w)=(returnFactor μ w)⁻¹ • (internal μ w 3).2 := by
  have h10 : (internal μ w 3).2 1 0=(internal μ w 3).2 0 1 :=
    congrArg (fun M : Mat 2 => M 0 1) (internal_isSymm μ w 3).eq
  have h00 : (internal μ w 3).2 0 0=returnFactor μ w := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shape,returnMap,Matrix.cons_val_succ,Matrix.smul_apply,h10,h00,hr,div_eq_mul_inv,mul_comm]

theorem normalization_preserves_point (μ : ℝ) (w : State) (hr : returnFactor μ w ≠ 0) :
    scale (returnMap μ w) • point (returnMap μ w)=scale w • (internal μ w 3).1 := by
  rw [return_scale,return_point,smul_smul,mul_assoc,mul_inv_cancel₀ hr,mul_one]

theorem normalization_preserves_metric (μ : ℝ) (w : State) (hr : returnFactor μ w ≠ 0) :
    scale (returnMap μ w) • shape (returnMap μ w)=scale w • (internal μ w 3).2 := by
  rw [return_scale,return_shape μ w hr,smul_smul,mul_assoc,mul_inv_cancel₀ hr,mul_one]

theorem physical_branch_gradient (μ τ : ℝ) (j : Fin 3) (s : PhaseState) :
    LQuadraticSeed.branchGradient μ (τ • s.1) j=currentGradient μ τ j s := by
  simp only [LQuadraticSeed.branchGradient,currentGradient,smul_smul,add_comm]

theorem physical_step (μ τ : ℝ) (j : Fin 3) (s : PhaseState) :
    bfgsStep (τ • s.2) (LQuadraticSeed.branchGradient μ (τ • s.1) j) (length j)=τ • step μ τ j s := by
  rw [physical_branch_gradient,bfgsStep_scale_matrix]
  rfl

theorem physical_secant (μ τ : ℝ) (j : Fin 3) (s : PhaseState) :
    LQuadraticSeed.branchGradient μ (τ • (substep μ τ j s).1) (nextPhase j)-
      LQuadraticSeed.branchGradient μ (τ • s.1) j=secant μ τ j s := by
  ext i
  simp only [LQuadraticSeed.branchGradient,substep,secant,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem physical_update (μ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) (j : Fin 3) (s : PhaseState) :
    inverseBFGS (τ • s.2) (τ • step μ τ j s) (secant μ τ j s)=τ • (substep μ τ j s).2 :=
  inverseBFGS_scale _ _ _ hτ

theorem return_scale_hasFDerivAt_seed (μ : ℝ) :
    HasFDerivAt (fun w => scale (returnMap μ w))
      (seedRatio • (ContinuousLinearMap.proj (4 : Fin 5) : State →L[ℝ] ℝ)) seed := by
  have hs : HasFDerivAt scale (ContinuousLinearMap.proj (4 : Fin 5)) seed :=
    (ContinuousLinearMap.proj (4 : Fin 5) : State →L[ℝ] ℝ).hasFDerivAt
  have hr := (analytic_returnFactor_seed μ).differentiableAt.hasFDerivAt
  simpa only [seed_scale,seed_returnFactor,zero_smul,zero_add] using hs.mul hr

def shiftPoint (v : Vec 2) (w : State) : State := ![w 0+v 0,w 1+v 1,w 2,w 3,w 4]

@[simp] theorem point_shiftPoint (v : Vec 2) (w : State) : point (shiftPoint v w)=point w+v := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem shape_shiftPoint (v : Vec 2) (w : State) : shape (shiftPoint v w)=shape w := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem scale_shiftPoint (v : Vec 2) (w : State) : scale (shiftPoint v w)=scale w := rfl

theorem substep_zero_translate (μ : ℝ) (j : Fin 3) (s : PhaseState) (v : Vec 2) :
    substep μ 0 j (s.1+v,s.2)=((substep μ 0 j s).1+v,(substep μ 0 j s).2) := by
  simp only [substep_zero]
  congr 1
  abel

theorem internal_boundary_translate (μ : ℝ) {w : State} (hw : scale w=0) (v : Vec 2) (k : ℕ) :
    internal μ (shiftPoint v w) k=((internal μ w k).1+v,(internal μ w k).2) := by
  induction k with
  | zero => exact Prod.ext (point_shiftPoint v w) (shape_shiftPoint v w)
  | succ k ih =>
    rw [internal,internal,scale_shiftPoint,hw,ih,substep_zero_translate]

theorem returnFactor_boundary_translate (μ : ℝ) {w : State} (hw : scale w=0) (v : Vec 2) :
    returnFactor μ (shiftPoint v w)=returnFactor μ w := by
  simp only [returnFactor,internal_boundary_translate μ hw]

theorem returnMap_boundary_translate (μ : ℝ) {w : State} (hw : scale w=0) (v : Vec 2) :
    returnMap μ (shiftPoint v w)=shiftPoint ((returnFactor μ w)⁻¹ • v) (returnMap μ w) := by
  rw [returnMap,internal_boundary_translate μ hw,returnFactor_boundary_translate μ hw,scale_shiftPoint]
  ext i
  fin_cases i <;>
    simp [shiftPoint,returnMap,Matrix.cons_val_succ,add_div,div_eq_mul_inv,mul_comm,mul_add]

def pointLift : Vec 2 →L[ℝ] State :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,0,0,0]

theorem shiftPoint_add (v : Vec 2) (w : State) : shiftPoint v w=w+pointLift v := by
  ext i
  fin_cases i <;> simp [shiftPoint,pointLift,Matrix.cons_val_succ]

theorem return_restricted_point_hasFDerivAt_seed (μ : ℝ) :
    HasFDerivAt (fun v : Vec 2 => returnMap μ (shiftPoint v seed))
      (seedRatio⁻¹ • pointLift) 0 := by
  have he : (fun v : Vec 2 => returnMap μ (shiftPoint v seed))=
      fun v => seed+(seedRatio⁻¹ • pointLift) v := by
    funext v
    rw [returnMap_boundary_translate μ seed_scale,seed_returnFactor,seed_fixed,shiftPoint_add,map_smul]
    rfl
  rw [he]
  exact (seedRatio⁻¹ • pointLift).hasFDerivAt.const_add seed

theorem return_derivative_point_columns (μ : ℝ) (v : Vec 2) :
    fderiv ℝ (returnMap μ) seed (pointLift v)=seedRatio⁻¹ • pointLift v := by
  have hp : HasFDerivAt (fun z : Vec 2 => shiftPoint z seed) pointLift 0 := by
    simpa only [shiftPoint_add] using pointLift.hasFDerivAt.const_add seed
  have hm : HasFDerivAt (returnMap μ) (fderiv ℝ (returnMap μ) seed) (shiftPoint 0 seed) := by
    simpa [shiftPoint_add] using (analytic_returnMap_seed μ).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun z : Vec 2 => returnMap μ (shiftPoint z seed))
      ((fderiv ℝ (returnMap μ) seed).comp pointLift) 0 :=
    HasFDerivAt.comp (f := fun z : Vec 2 => shiftPoint z seed) (g := returnMap μ) 0 hm hp
  have he := hcomp.unique (return_restricted_point_hasFDerivAt_seed μ)
  exact congrArg (fun L : Vec 2 →L[ℝ] State => L v) he

theorem return_derivative_last_row (μ : ℝ) (v : State) :
    (fderiv ℝ (returnMap μ) seed v) 4=seedRatio*v 4 := by
  have hm := (analytic_returnMap_seed μ).differentiableAt.hasFDerivAt
  have hs : HasFDerivAt scale (ContinuousLinearMap.proj (4 : Fin 5)) (returnMap μ seed) :=
    (ContinuousLinearMap.proj (4 : Fin 5) : State →L[ℝ] ℝ).hasFDerivAt
  have he := (hs.comp seed hm).unique (return_scale_hasFDerivAt_seed μ)
  exact congrArg (fun L : State →L[ℝ] ℝ => L v) he

theorem shape_posDef {w : State} (hw : (w 2)^2 < w 3) : (shape w).PosDef := by
  constructor
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using (shape_isSymm w).eq
  · intro v hv
    change 0 < dot v ((shape w).mulVec v)
    have he : dot v ((shape w).mulVec v)=(v 0+w 2*v 1)^2+(w 3-(w 2)^2)*(v 1)^2 := by
      simp [dot,Matrix.mulVec,dotProduct,Fin.sum_univ_two,shape]
      ring
    rw [he]
    by_cases hv1 : v 1=0
    · have hv0 : v 0 ≠ 0 := by
        intro hz
        apply hv
        ext i
        fin_cases i
        · exact hz
        · exact hv1
      simpa [hv1] using sq_pos_of_ne_zero hv0
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sub_pos.mpr hw) (sq_pos_of_ne_zero hv1))

theorem internal_posDef_of_regular (μ : ℝ) {w : State} (hw : Regular μ w) (k : ℕ) (hk : k ≤ 3) :
    (internal μ w k).2.PosDef := by
  induction k with
  | zero => exact shape_posDef hw.2.2
  | succ k ih =>
    apply inverseBFGS_posDef (ih (by omega))
    have hk' : k < 3 := by omega
    have hj : phase k=(⟨k,hk'⟩ : Fin 3) := Fin.ext (Nat.mod_eq_of_lt hk')
    change 0 < curvature μ (scale w) (phase k) (internal μ w k)
    rw [hj]
    exact hw.1 ⟨k,hk'⟩

/-- The real-analytic five-dimensional extension is constructed from actual
inverse-BFGS operations. This is a local map theorem, not a stable-orbit premise. -/
theorem normalized_return_contract (μ : ℝ) :
    returnMap μ seed=seed ∧
    (∀ j, 0 < denominator μ seed j) ∧ returnFactor μ seed=seedRatio ∧
    (∃ U : Set State, IsOpen U ∧ seed ∈ U ∧ (∀ w ∈ U, Regular μ w) ∧
      AnalyticOnNhd ℝ (returnMap μ) U) ∧
    (∀ v, fderiv ℝ (returnMap μ) seed (pointLift v)=seedRatio⁻¹ • pointLift v) ∧
    (∀ v, (fderiv ℝ (returnMap μ) seed v) 4=seedRatio*v 4) ∧
    (∀ w, returnFactor μ w ≠ 0 →
      scale (returnMap μ w) • point (returnMap μ w)=scale w • (internal μ w 3).1 ∧
      scale (returnMap μ w) • shape (returnMap μ w)=scale w • (internal μ w 3).2) := by
  exact ⟨seed_fixed μ,seed_denominator_positive μ,seed_returnFactor μ,
    regular_analytic_neighborhood μ,return_derivative_point_columns μ,return_derivative_last_row μ,
    fun w hw => ⟨normalization_preserves_point μ w hw,normalization_preserves_metric μ w hw⟩⟩

end BfgsVerification.LNormalizedReturn
