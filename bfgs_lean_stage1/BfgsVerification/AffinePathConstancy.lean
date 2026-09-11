import BfgsVerification.AffineSupportPath

/-! Continuous paths with finitely many derivative exceptions. This is the
calculus needed after a piecewise differentiable path has actually been supplied;
it does not assert existence of a semialgebraic decomposition. -/
noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification
namespace AffineSupportPath
open AffineCriticalObjective

theorem constant_on_Icc_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) : ∀ t ∈ Icc a b, f t = f a := by
  have hd' : ∀ t ∈ interior (Icc a b), HasDerivWithinAt f 0 (interior (Icc a b)) t := by
    intro t ht
    exact (hd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc hd'
    (fun _ _ => le_rfl)
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hc hd'
    (fun _ _ => le_rfl)
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  exact le_antisymm (ha (left_mem_Icc.mpr hab) ht ht.1)
    (hm (left_mem_Icc.mpr hab) ht ht.1)

/-- Finitely many corners do not affect constancy. The derivative is assumed
only on the open interval outside the finite exceptional set; endpoint and
corner derivatives are unnecessary. -/
theorem constant_on_Icc_of_hasDerivAt_zero_off_finset {f : ℝ → ℝ} (s : Finset ℝ)
    {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ s → HasDerivAt f 0 t) :
    ∀ t ∈ Icc a b, f t = f a := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty => exact constant_on_Icc_of_hasDerivAt_zero hc (fun t ht => hd t ht (by simp))
  | @insert c s hcs ih =>
    by_cases hcint : c ∈ Ioo a b
    · have hl : ∀ t ∈ Icc a c, f t = f a := ih
        (hc.mono (Icc_subset_Icc le_rfl hcint.2.le)) (by
          intro t ht hs
          exact hd t ⟨ht.1,ht.2.trans hcint.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ht.2.ne,hs⟩))
      have hr : ∀ t ∈ Icc c b, f t = f c := ih
        (hc.mono (Icc_subset_Icc hcint.1.le le_rfl)) (by
          intro t ht hs
          exact hd t ⟨hcint.1.trans ht.1,ht.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ht.1.ne',hs⟩))
      intro t ht
      by_cases htc : t ≤ c
      · exact hl t ⟨ht.1,htc⟩
      · exact (hr t ⟨(le_of_not_ge htc),ht.2⟩).trans
          (hl c (right_mem_Icc.mpr hcint.1.le))
    · apply ih hc
      intro t ht hs
      exact hd t ht (by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun he => hcint (he ▸ ht),hs⟩)

/-- The actual objective is constant on any continuous affine-critical path
whose path and objective composition are differentiable away from finitely many
times. Finite convexity supplies continuity of the objective composition. -/
theorem objective_constant_on_piecewise_differentiable_path {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {p : ℝ → Vec n} {a b : ℝ} (s : Finset ℝ)
    (hp : ContinuousOn p (Icc a b))
    (hac : ∀ t ∈ Ioo a b, IsAffineCritical F (p t))
    (hdp : ∀ t ∈ Ioo a b, t ∉ s → DifferentiableAt ℝ p t)
    (hdF : ∀ t ∈ Ioo a b, t ∉ s → DifferentiableAt ℝ (F ∘ p) t) :
    ∀ t ∈ Icc a b, F (p t) = F (p a) := by
  apply constant_on_Icc_of_hasDerivAt_zero_off_finset s
    ((convex_continuous hF).comp_continuousOn hp)
  intro t ht hs
  exact hasDerivAt_zero_of_affineCritical (hac t ht) (hdp t ht hs) (hdF t ht hs)

end AffineSupportPath
end BfgsVerification
