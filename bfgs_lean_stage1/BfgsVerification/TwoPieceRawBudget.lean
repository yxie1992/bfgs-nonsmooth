import BfgsVerification.TwoPieceScalarBudget

noncomputable section
namespace BfgsVerification.TwoPieceBudget

theorem raw_uniform_drop {c A B D X α A' B' D' X' : ℝ}
    (hc : 0 < c) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hα : 0 < α)
    (hfuture : A' < 2*B')
    (hA' : A'=D*A/B^2+α*(A-2*B)^2/(2*B))
    (hB' : B'=α*(B-A/2)) (hD' : D'=α*A*D/(2*B)) (hX' : X'=α*B-X)
    (harmijo : α*(2*B-(1-c)*A) ≤ 2*X) : B'*X'/D'+c < B*X/D := by
  have hBc : B ≠ 0 := hB.ne'
  have hAc : A ≠ 0 := hA.ne'
  have hDc : D ≠ 0 := hD.ne'
  have hαc : α ≠ 0 := hα.ne'
  have hAe : A'*(2*B^2)=2*D*A+α*(A-2*B)^2*B := by
    rw [hA']
    field_simp
    ring
  have hf := mul_lt_mul_of_pos_right hfuture (by positivity : 0 < 2*B^2)
  rw [hAe,hB'] at hf
  have hm : 0 < A*(α*B*(2*B-A)-2*D) := by nlinarith [hf]
  have hm' : 0 < α*B*(2*B-A)-2*D := (mul_pos_iff_of_pos_left hA).mp hm
  have hDA : D < α*B^2 := by nlinarith [mul_pos (mul_pos hα hB) hA]
  have hdiff : B*X/D-B'*X'/D' = 2*B^2*(X-α*(B-A/2))/(A*D) := by
    rw [hB',hD',hX']
    field_simp
    ring
  have hstep : c*α*A ≤ 2*(X-α*(B-A/2)) := by nlinarith [harmijo]
  have hstep' := mul_le_mul_of_nonneg_left hstep (sq_nonneg B)
  have hstrict := mul_lt_mul_of_pos_left hDA (mul_pos hc hA)
  have hnum : c*(A*D) < 2*B^2*(X-α*(B-A/2)) := by nlinarith [hstep',hstrict]
  have hdrop : c < B*X/D-B'*X'/D' := by
    rw [hdiff]
    exact (lt_div_iff₀ (mul_pos hA hD)).mpr hnum
  linarith

/-- The actual raw two-piece recurrence admits no infinite positive continuation.
Its application must derive all five scalars from actual BFGS data. -/
theorem raw_no_infinite_continuation {c : ℝ} (hc : 0 < c)
    (A B D X α : ℕ → ℝ)
    (hA : ∀ k, 0 < A k) (hB : ∀ k, 0 < B k) (hD : ∀ k, 0 < D k)
    (hX : ∀ k, 0 < X k) (hα : ∀ k, 0 < α k)
    (hA' : ∀ k, A (k+1)=D k*A k/(B k)^2+α k*(A k-2*B k)^2/(2*B k))
    (hB' : ∀ k, B (k+1)=α k*(B k-A k/2))
    (hD' : ∀ k, D (k+1)=α k*A k*D k/(2*B k))
    (hX' : ∀ k, X (k+1)=α k*B k-X k)
    (harmijo : ∀ k, α k*(2*B k-(1-c)*A k) ≤ 2*X k) : False := by
  have hmargin (k : ℕ) : A k < 2*B k := by
    have hb := hB (k+1)
    rw [hB' k] at hb
    have ht : 0 < B k-A k/2 := (mul_pos_iff_of_pos_left (hα k)).mp hb
    linarith
  let ψ : ℕ → ℝ := fun k => B k*X k/D k
  have hp (k : ℕ) : 0 < ψ k := div_pos (mul_pos (hB k) (hX k)) (hD k)
  have hdrop (k : ℕ) : ψ (k+1)+c ≤ ψ k :=
    (raw_uniform_drop hc (hA k) (hB k) (hD k) (hα k) (hmargin (k+1))
      (hA' k) (hB' k) (hD' k) (hX' k) (harmijo k)).le
  obtain ⟨N,hN⟩ := exists_nat_gt (ψ 0/c)
  have hNc : ψ 0 < (N : ℝ)*c := (div_lt_iff₀ hc).mp hN
  have hb := finite_budget ψ N (fun k _ => hdrop k)
  linarith [hp N]

end BfgsVerification.TwoPieceBudget
