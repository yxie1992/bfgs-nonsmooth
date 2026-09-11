import BfgsVerification.ScalarCounterexamples
import BfgsVerification.FivePieceObstruction

/-! Actual u²+|v| BFGS trajectory with arbitrary unexcited tangential metric. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.UnexcitedMetric

def objective (x : Vec 2) : ℝ := (x 0)^2+|x 1|

def point (σ r : ℝ) : Vec 2 := ![0,σ*r]
def gradient (σ : ℝ) : Vec 2 := ![0,σ]
def diagonal (A B : ℝ) : Mat 2 := !![A,0;0,B]

theorem objective_convex : ConvexOn ℝ univ objective := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have habs : |a*x 1+b*y 1| ≤ a*|x 1|+b*|y 1| := by
    calc
      _ ≤ |a*x 1|+|b*y 1| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
  have hsq : (a*x 0+b*y 0)^2 ≤ a*(x 0)^2+b*(y 0)^2 := by
    have he : (a*x 0+b*y 0)^2+a*b*(x 0-y 0)^2 =
        (a+b)*(a*(x 0)^2+b*(y 0)^2) := by ring
    rw [hab,one_mul] at he
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0-y 0))]
  simp only [objective,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith only [habs,hsq]

theorem actual_gradient {σ r : ℝ} (hσ : σ^2=1) (hr : 0 < r) :
    HasFDerivAt objective (gradientFunctional (gradient σ)) (point σ r) := by
  have hs : σ=1 ∨ σ=-1 := by
    rcases (sq_eq_one_iff).mp hσ with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := point σ r)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := point σ r)
  have hsq := ((hasDerivAt_id ((point σ r) 0)).pow 2).comp_hasFDerivAt (point σ r) h0
  rcases hs with rfl | rfl
  · have hh := hsq.add (h1.abs_of_pos (by simpa [point] using hr))
    convert hh using 1
    ext v
    simp [gradient,gradientFunctional_apply,dot,Fin.sum_univ_two,point]
  · have hh := hsq.add (h1.abs_of_neg (by simpa [point] using (neg_neg_of_pos hr)))
    convert hh using 1
    ext v
    simp [gradient,gradientFunctional_apply,dot,Fin.sum_univ_two,point]

theorem point_value {σ r : ℝ} (hσ : σ^2=1) (hr : 0 ≤ r) :
    objective (point σ r)=r := by
  have hs : |σ|=1 := by
    rcases (sq_eq_one_iff).mp hσ with rfl | rfl <;> norm_num
  simp [objective,point,abs_mul,hs,abs_of_nonneg hr]

theorem diagonal_posDef {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : (diagonal A B).PosDef := by
  have he : diagonal A B = Matrix.diagonal ![A,B] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> assumption

theorem vertical_update (A B s y : ℝ) (hs : s ≠ 0) (hy : y ≠ 0) :
    inverseBFGS (diagonal A B) ![0,s] ![0,y] = diagonal A (s/y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseBFGS,diagonal,dot,outer,Fin.sum_univ_two,Matrix.mul_apply]
  <;> field_simp
  <;> ring

def sign (k : ℕ) : ℝ := (-1)^k
def radius (ρ v₀ : ℝ) (k : ℕ) : ℝ := ρ^k*v₀

theorem sign_sq (k : ℕ) : (sign k)^2=1 := by
  rw [sign,← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

theorem sign_succ (k : ℕ) : sign (k+1) = -sign k := by
  simp [sign,pow_succ]

theorem radius_pos {ρ v₀ : ℝ} (hρ : 0 < ρ) (hv : 0 < v₀) (k : ℕ) :
    0 < radius ρ v₀ k := mul_pos (pow_pos hρ k) hv

theorem radius_succ (ρ v₀ : ℝ) (k : ℕ) : radius ρ v₀ (k+1)=ρ*radius ρ v₀ k := by
  simp only [radius,pow_succ]
  ring

theorem actual_step (A σ r ρ : ℝ) (hρ : ρ ≠ 0) :
    bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ) = ![0,-(1+ρ)*σ*r] := by
  ext i
  fin_cases i <;> simp [bfgsStep,diagonal,gradient,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  field_simp
  ring

theorem point_step (A σ r ρ : ℝ) (hρ : ρ ≠ 0) :
    point (-σ) (ρ*r) = point σ r+bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ) := by
  rw [actual_step A σ r ρ hρ]
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem gradient_change (σ : ℝ) : gradient (-σ)-gradient σ = ![0,-2*σ] := by
  ext i
  fin_cases i <;> simp [gradient] <;> ring

theorem actual_update (A : ℝ) {σ r ρ : ℝ} (hσ : σ^2=1) (hr : 0 < r) (hρ : 0 < ρ) :
    inverseBFGS (diagonal A ((1+ρ)/(2*ρ)*r))
      (bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ))
      (gradient (-σ)-gradient σ) = diagonal A ((1+ρ)/(2*ρ)*(ρ*r)) := by
  have hs : σ ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  rw [actual_step A σ r ρ hρ.ne',gradient_change,vertical_update]
  · apply congrArg (diagonal A)
    field_simp [hs,hρ.ne']
    <;> ring
  · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by linarith)) hs) hr.ne'
  · exact mul_ne_zero (by norm_num) hs

theorem accepted_pairings (A : ℝ) {σ r ρ : ℝ} (hσ : σ^2=1) (hρ : ρ ≠ 0) :
    dot (gradient σ) (bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ)) = -(1+ρ)*r ∧
    dot (gradient (-σ)) (bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ)) = (1+ρ)*r := by
  rw [actual_step A σ r ρ hρ]
  simp only [dot,Fin.sum_univ_two,gradient,Matrix.cons_val_zero,Matrix.cons_val_one,zero_mul,zero_add]
  constructor
  · calc
      σ*(-(1+ρ)*σ*r) = -(1+ρ)*r*σ^2 := by ring
      _ = _ := by rw [hσ,mul_one]
  · calc
      -σ*(-(1+ρ)*σ*r) = (1+ρ)*r*σ^2 := by ring
      _ = _ := by rw [hσ,mul_one]

theorem source_ratio {c₁ ρ : ℝ} (hc : 0 < c₁) (hρ : 0 < ρ)
    (hr : ρ < (1-c₁)/(1+c₁)) : ρ < 1 ∧ c₁*(1+ρ) < 1-ρ := by
  have hp : 0 < 1+c₁ := by linarith
  have hb := (lt_div_iff₀ hp).mp hr
  constructor <;> nlinarith

/-- A single actual infinite run, with no iterate or metric convergence premise. -/
def run (A v₀ ρ c₁ c₂ : ℝ) (hA : 0 < A) (hv : 0 < v₀)
    (hρ : 0 < ρ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (hr : ρ < (1-c₁)/(1+c₁)) : AdmissibleBFGSRun 2 objective where
  convex := objective_convex
  x k := point (sign k) (radius ρ v₀ k)
  H k := diagonal A ((1+ρ)/(2*ρ)*radius ρ v₀ k)
  g k := gradient (sign k)
  α _ := 2*ρ
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := by
    apply diagonal_posDef hA
    exact mul_pos (div_pos (by linarith) (by positivity)) (radius_pos hρ hv 0)
  alpha_pos _ := by positivity
  gradient_nonzero k := by
    intro he
    have hs := congrArg (fun v : Vec 2 => v 1) he
    change sign k = 0 at hs
    have hq := sign_sq k
    rw [hs] at hq
    norm_num at hq
  hasGradient k := actual_gradient (sign_sq k) (radius_pos hρ hv k)
  step k := by
    rw [sign_succ,radius_succ]
    exact point_step A (sign k) (radius ρ v₀ k) ρ hρ.ne'
  update k := by
    rw [sign_succ,radius_succ]
    exact (actual_update A (sign_sq k) (radius_pos hρ hv k) hρ).symm
  armijo k := by
    rw [point_value (sign_sq (k+1)) (radius_pos hρ hv (k+1)).le,
      point_value (sign_sq k) (radius_pos hρ hv k).le,
      (accepted_pairings A (sign_sq k) hρ.ne').1,radius_succ]
    have hp := (source_ratio hc₁ hρ hr).2
    have hmul := mul_le_mul_of_nonneg_right hp.le (radius_pos hρ hv k).le
    nlinarith only [hmul]
  weak_wolfe k := by
    rw [sign_succ,(accepted_pairings A (sign_sq k) hρ.ne').1,
      (accepted_pairings A (sign_sq k) hρ.ne').2]
    have hz : 0 ≤ (1+ρ)*radius ρ v₀ k :=
      mul_nonneg (by linarith) (radius_pos hρ hv k).le
    have hc0 : 0 ≤ c₂ := le_trans hc₁.le hc.le
    nlinarith [mul_nonneg hc0 hz]

theorem literal_point_formula (ρ v₀ : ℝ) (k : ℕ) :
    point (sign k) (radius ρ v₀ k) = ![0,(-ρ)^k*v₀] := by
  have hp : (-ρ)^k = (-1 : ℝ)^k*ρ^k := by
    rw [← mul_pow]
    congr 1
    ring
  ext i
  fin_cases i <;> simp [point,sign,radius,hp] <;> ring

theorem radius_tendsto {ρ v₀ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (radius ρ v₀) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).mul_const v₀
  simpa only [radius,zero_mul] using ht

theorem literal_matrix_limit (A : ℝ) {ρ v₀ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun k => diagonal A ((1+ρ)/(2*ρ)*radius ρ v₀ k)) atTop (𝓝 (diagonal A 0)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp only [diagonal,Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · simpa only [mul_zero] using (radius_tendsto hρ hρ1).const_mul ((1+ρ)/(2*ρ))

theorem literal_point_limit {ρ v₀ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun k => point (sign k) (radius ρ v₀ k)) atTop (𝓝 0) := by
  have hab : |(-ρ)| < 1 := by rwa [abs_neg,abs_of_nonneg hρ]
  have ht := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hab).mul_const v₀
  apply tendsto_pi_nhds.mpr
  intro i
  simp only [literal_point_formula]
  fin_cases i
  · exact tendsto_const_nhds
  · simpa only [Matrix.cons_val_one,Pi.zero_apply,zero_mul] using ht

theorem acceptance_ratios (A : ℝ) {σ r ρ : ℝ} (hσ : σ^2=1) (hr : 0 < r) (hρ : 0 < ρ) :
    (objective (point σ r)-objective (point (-σ) (ρ*r))) /
      (-dot (gradient σ) (bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ))) =
        (1-ρ)/(1+ρ) ∧
    dot (gradient (-σ)) (bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ)) /
      dot (gradient σ) (bfgsStep (diagonal A ((1+ρ)/(2*ρ)*r)) (gradient σ) (2*ρ)) = -1 := by
  have hneg : (-σ)^2=1 := by simpa only [neg_sq] using hσ
  rw [point_value hσ hr.le,point_value hneg (mul_pos hρ hr).le,
    (accepted_pairings A hσ hρ.ne').1,(accepted_pairings A hσ hρ.ne').2]
  have hp : 1+ρ ≠ 0 := by linarith
  rw [show -(-(1+ρ)*r) = (1+ρ)*r by ring]
  constructor
  · change (r-ρ*r)/((1+ρ)*r) = (1-ρ)/(1+ρ)
    apply (div_eq_div_iff (mul_ne_zero hp hr.ne') hp).mpr
    ring
  · apply (div_eq_iff (mul_ne_zero (neg_ne_zero.mpr hp) hr.ne')).mpr
    ring

/-- The literal report run converges to the optimizer while its actual inverse
matrices converge to diag(A,0), for every arbitrary positive tangential A. -/
theorem run_limits (A v₀ ρ c₁ c₂ : ℝ) (hA : 0 < A) (hv : 0 < v₀)
    (hρ : 0 < ρ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (hr : ρ < (1-c₁)/(1+c₁)) :
    let R := run A v₀ ρ c₁ c₂ hA hv hρ hc₁ hc hc₂ hr
    Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.H atTop (𝓝 (diagonal A 0)) ∧
      (∀ k, R.H k 0 0 = A) ∧
      (∀ k, R.x k = ![0,(-ρ)^k*v₀]) := by
  dsimp only [run]
  have hρ1 := (source_ratio hc₁ hρ hr).1
  refine ⟨literal_point_limit hρ.le hρ1,?_,literal_matrix_limit A hρ.le hρ1,?_,literal_point_formula ρ v₀⟩
  · simp_rw [point_value (sign_sq _) (radius_pos hρ hv _).le]
    exact radius_tendsto hρ.le hρ1
  · intro k
    rfl

theorem unique_minimum {x : Vec 2} (hx : objective x = objective 0) : x = 0 := by
  have hval : objective 0=0 := by simp [objective]
  rw [hval] at hx
  have h0 : x 0=0 := by
    have hs : (x 0)^2=0 := by dsimp only [objective] at hx; nlinarith [abs_nonneg (x 1),sq_nonneg (x 0)]
    exact pow_eq_zero hs
  have h1 : x 1=0 := by
    dsimp only [objective] at hx
    rw [h0,zero_pow (by norm_num : 2 ≠ 0),zero_add] at hx
    exact abs_eq_zero.mp hx
  ext i
  fin_cases i <;> assumption

theorem objective_nonneg (x : Vec 2) : 0 ≤ objective x := add_nonneg (sq_nonneg _) (abs_nonneg _)

theorem tangential_second_derivative (u : ℝ) :
    HasDerivAt (fun t : ℝ => objective ![t,0]) (2*u) u ∧
      HasDerivAt (fun t : ℝ => 2*t) 2 u := by
  constructor
  · simpa [objective] using (hasDerivAt_id u).pow 2
  · simpa using (hasDerivAt_id u).const_mul 2

end BfgsVerification.UnexcitedMetric
