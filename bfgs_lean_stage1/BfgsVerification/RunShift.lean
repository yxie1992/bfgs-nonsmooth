import BfgsVerification.ObjectiveEnergy

/-! A tail of the actual accepted run is another accepted run, with its initial
SPD property proved from the original run. This discharges tail conventions. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

def shift (J : ℕ) : AdmissibleBFGSRun n F where
  convex := R.convex
  x := fun k => R.x (J + k)
  H := fun k => R.H (J + k)
  g := fun k => R.g (J + k)
  α := fun k => R.α (J + k)
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := by simpa using R.positive_definite J
  alpha_pos := fun k => R.alpha_pos (J + k)
  gradient_nonzero := fun k => R.gradient_nonzero (J + k)
  hasGradient := fun k => R.hasGradient (J + k)
  step := fun k => R.step (J + k)
  update := fun k => R.update (J + k)
  armijo := fun k => R.armijo (J + k)
  weak_wolfe := fun k => R.weak_wolfe (J + k)

@[simp] theorem shift_q (J k : ℕ) : (R.shift J).q k = R.q (J + k) := rfl
@[simp] theorem shift_d (J k : ℕ) : (R.shift J).d k = R.d (J + k) := rfl
@[simp] theorem shift_hessian (J k : ℕ) : (R.shift J).hessian k = R.hessian (J + k) := rfl
@[simp] theorem shift_displacement (J k : ℕ) :
    (R.shift J).displacement k = R.displacement (J + k) := rfl
@[simp] theorem shift_gradientChange (J k : ℕ) :
    (R.shift J).gradientChange k = R.gradientChange (J + k) := rfl
@[simp] theorem shift_curvature (J k : ℕ) :
    (R.shift J).curvature k = R.curvature (J + k) := rfl

theorem shift_summable_d (hs : Summable R.d) (J : ℕ) : Summable (R.shift J).d := by
  change Summable (fun k => R.d (J + k))
  simpa only [Nat.add_comm] using (summable_nat_add_iff J).mpr hs

theorem shift_d_tendsto_zero (hd : Tendsto R.d atTop (𝓝 0)) (J : ℕ) :
    Tendsto (R.shift J).d atTop (𝓝 0) := by
  simpa only [shift, d, q, Nat.add_comm] using hd.comp (tendsto_add_atTop_nat J)

end BfgsVerification.AdmissibleBFGSRun
