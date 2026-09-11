import BfgsVerification.TwoPieceObjective
import BfgsVerification.TwoPieceRawBudget

noncomputable section
namespace BfgsVerification.TwoPieceBudget
variable (R : AdmissibleBFGSRun 2 objective)

theorem actual_next_matrix (k : ℕ) :
    R.H (k+1)=matrix (R.α k*B R k/2)
      (sigma R k*R.α k*(A R k-B R k)/2)
      (D R k*A R k/(B R k)^2+R.α k*(A R k-B R k)^2/(2*B R k)) := by
  rw [R.update,matrix_shape R k,gradient_shape R k,gradient_shape R (k+1),sigma_next R k]
  exact actual_update_matrix _ _ _ _ _ (sigma_sq R k) (R.alpha_pos k).ne' (B_pos R k).ne'

theorem aa_next (k : ℕ) : aa R (k+1)=R.α k*B R k/2 := by
  have h := congrArg (fun M : Mat 2 => M 0 0) (actual_next_matrix R k)
  simpa only [aa,matrix,Matrix.cons_val_zero] using h

theorem bb_next (k : ℕ) : bb R (k+1)=sigma R k*R.α k*(A R k-B R k)/2 := by
  have h := congrArg (fun M : Mat 2 => M 0 1) (actual_next_matrix R k)
  simpa only [bb,matrix,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem cc_next (k : ℕ) : cc R (k+1)=D R k*A R k/(B R k)^2+
    R.α k*(A R k-B R k)^2/(2*B R k) := by
  have h := congrArg (fun M : Mat 2 => M 1 1) (actual_next_matrix R k)
  simpa only [cc,matrix,Matrix.cons_val_one] using h

theorem scalar_recurrences (k : ℕ) :
    A R (k+1)=D R k*A R k/(B R k)^2+R.α k*(A R k-2*B R k)^2/(2*B R k) ∧
    B R (k+1)=R.α k*(B R k-A R k/2) ∧
    D R (k+1)=R.α k*A R k*D R k/(2*B R k) := by
  have h := scalar_update_identities (aa R k) (bb R k) (cc R k) (sigma R k)
    (R.α k) (sigma_sq R k) (B_pos R k).ne'
  change
    energy (aa R (k+1)) (bb R (k+1)) (cc R (k+1)) (sigma R (k+1)) = _ ∧
    cross (aa R (k+1)) (bb R (k+1)) (sigma R (k+1)) = _ ∧
    determinant (aa R (k+1)) (bb R (k+1)) (cc R (k+1)) = _
  rw [aa_next,bb_next,cc_next,sigma_next]
  exact h

theorem X_next (k : ℕ) : X R (k+1)=R.α k*B R k-X R k := by
  rw [X_eq R (k+1),sigma_next,R.step,matrix_shape R k,gradient_shape R k,
    step_formula _ _ _ _ _ (sigma_sq R k),X_eq R k]
  simp only [Pi.add_apply,Matrix.cons_val_zero]
  change -sigma R k*(R.x k 0+-R.α k*sigma R k*B R k)=_
  calc
    _ = R.α k*B R k*(sigma R k)^2-sigma R k*R.x k 0 := by ring
    _ = _ := by rw [sigma_sq]; ring

theorem last_coordinate_next (k : ℕ) :
    R.x (k+1) 1=R.x k 1-R.α k*(A R k-B R k) := by
  rw [R.step,matrix_shape R k,gradient_shape R k,
    step_formula _ _ _ _ _ (sigma_sq R k)]
  simp only [Pi.add_apply,Matrix.cons_val_one]
  change R.x k 1+-R.α k*(A R k-B R k)=_
  ring

theorem raw_armijo (k : ℕ) :
    R.α k*(2*B R k-(1-R.c₁)*A R k) ≤ 2*X R k := by
  have h := R.armijo k
  rw [dot_bfgsStep] at h
  change X R (k+1)+R.x (k+1) 1 ≤ X R k+R.x k 1+R.c₁*(-(R.α k*R.q k)) at h
  rw [X_next,last_coordinate_next,← A_eq_q] at h
  nlinarith [h]

/-- No infinite accepted differentiable-iterate ordinary full-BFGS run exists
for the literal two-piece objective. Positivity, switching, all recurrences and
the finite potential decrease are derived from the actual run. -/
theorem no_infinite_actual_run (R : AdmissibleBFGSRun 2 objective) : False :=
  raw_no_infinite_continuation R.c₁_pos (A R) (B R) (D R) (X R) R.α
    (A_pos R) (B_pos R) (D_pos R) (X_pos R) R.alpha_pos
    (fun k => (scalar_recurrences R k).1)
    (fun k => (scalar_recurrences R k).2.1)
    (fun k => (scalar_recurrences R k).2.2)
    (X_next R) (raw_armijo R)

end BfgsVerification.TwoPieceBudget
