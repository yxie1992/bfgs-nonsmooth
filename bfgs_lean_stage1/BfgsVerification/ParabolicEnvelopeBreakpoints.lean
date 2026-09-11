import BfgsVerification.ParabolicEnvelopePrunedFamily

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

theorem strict_profile_point_before_active {i j : Fin m} {ξ ζ : ℝ}
    (hij : P.b i < P.b j) (hξ : P.profile j ξ < P.profile i ξ)
    (hζ : P.profile i ζ ≤ P.profile j ζ) : ξ < ζ := by
  by_contra hn
  have hh : ζ ≤ ξ := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hij.le) (sub_nonneg.mpr hh)
  dsimp [profile] at hξ hζ
  nlinarith

/-- All actual neighbor breakpoints, indexed in their original increasing
finite order. The index condition merely expresses existence of the successor. -/
def orderedBreakpoint (O : P.PrunedOrder)
    (i : {i : Fin O.count // i.val+1 < O.count}) : ℝ :=
  P.breakpoint (O.index i.val) (O.index ⟨i.val.val+1, i.property⟩)

theorem orderedBreakpoint_strictMono (O : P.PrunedOrder) : StrictMono (P.orderedBreakpoint O) := by
  intro i j hij
  let ni : Fin O.count := ⟨i.val.val+1, i.property⟩
  let nj : Fin O.count := ⟨j.val.val+1, j.property⟩
  have hai : P.Adjacent (O.index i.val) (O.index ni) := O.adjacent P rfl
  have haj : P.Adjacent (O.index j.val) (O.index nj) := O.adjacent P rfl
  obtain ⟨ξ, hξ⟩ := (O.essential ni).2
  have hi_ne : O.index i.val ≠ O.index ni := by
    intro he
    have h := hai.2.2.1
    rw [he] at h
    exact lt_irrefl _ h
  have hleft : P.breakpoint (O.index i.val) (O.index ni) < ξ :=
    P.strict_profile_right_of_breakpoint hai.2.2.1 (hξ _ (O.essential i.val).1 hi_ne)
  have hnn : ni < nj := by
    change i.val.val+1 < j.val.val+1
    change i.val.val < j.val.val at hij
    omega
  have hb : P.b (O.index ni) < P.b (O.index nj) := O.slopes_strictMono hnn
  have hj_ne : O.index nj ≠ O.index ni := by
    intro he
    rw [he] at hb
    exact lt_irrefl _ hb
  have hstrict : P.profile (O.index nj) ξ < P.profile (O.index ni) ξ :=
    hξ _ (O.essential nj).1 hj_ne
  have ha := (P.adjacent_breakpoint_active haj).2 (O.index ni)
  exact hleft.trans (P.strict_profile_point_before_active hb hstrict ha)

/-- The literal source ordered/pruned envelope exists for every original
family: exact objective preservation, strictly increasing slopes and strictly
increasing switching locations with positive envelope values, with Q.7 calibration at each one. -/
theorem ordered_pruning_specification :
    (∀ x, P.prunedFamily.objective x = P.objective x) ∧
      StrictMono P.prunedFamily.b ∧ StrictMono (P.orderedBreakpoint P.prunedOrder) ∧
      (∀ i : {i : Fin P.prunedOrder.count // i.val+1 < P.prunedOrder.count},
        let l := P.prunedOrder.index i.val
        let r := P.prunedOrder.index ⟨i.val.val+1, i.property⟩
        P.ProfileActive l (P.breakpoint l r) ∧ P.ProfileActive r (P.breakpoint l r) ∧
        0 < P.profile l (P.breakpoint l r) ∧
        P.calibration r-P.calibration l = -(P.a r-P.a l)/(2*P.profile l (P.breakpoint l r))) := by
  refine ⟨P.prunedFamily_objective, P.prunedFamily_slopes_strictMono,
    P.orderedBreakpoint_strictMono P.prunedOrder, ?_⟩
  intro i
  let l := P.prunedOrder.index i.val
  let r := P.prunedOrder.index ⟨i.val.val+1, i.property⟩
  have ha : P.Adjacent l r := P.prunedOrder.adjacent P rfl
  exact ⟨(P.adjacent_breakpoint_active ha).1, (P.adjacent_breakpoint_active ha).2,
    P.adjacent_breakpoint_value_pos ha, P.adjacent_calibration ha⟩

end Family
end Parabolic
end BfgsVerification
