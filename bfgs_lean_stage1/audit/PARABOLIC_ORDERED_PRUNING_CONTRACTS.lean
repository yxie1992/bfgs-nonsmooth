import BfgsVerification.ParabolicEnvelopeBreakpoints

noncomputable section
open Set BfgsVerification

/- The ordered/pruned finite family is derived for every original input. -/
example {m : ℕ} (P : Parabolic.Family m) :
    ∃ r : ℕ, ∃ Q : Parabolic.Family r, ∃ idx : Fin r → Fin m,
      StrictMono Q.b ∧ (∀ k, Q.a k = P.a (idx k) ∧ Q.b k = P.b (idx k) ∧ P.Essential (idx k)) ∧
      (∀ x, Q.objective x = P.objective x) := by
  exact ⟨P.prunedOrder.count, P.prunedFamily, P.prunedOrder.index,
    P.prunedFamily_slopes_strictMono, fun k => ⟨rfl, rfl, P.prunedOrder.essential k⟩,
    P.prunedFamily_objective⟩

/- Preserved actual differentiable gradients, including u=0 and all ties. -/
example {m : ℕ} (P : Parabolic.Family m) {x g : Vec 2}
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    HasFDerivAt P.prunedFamily.objective (gradientFunctional g) x ∧
      ∃ i ∈ P.essentialIndices, P.Active i x ∧ P.branchGradient i x = g :=
  ⟨P.prunedFamily_gradient hg, P.essential_active_gradient hg⟩

/- Full increasing order of the actual neighboring switching locations. -/
example {m : ℕ} (P : Parabolic.Family m) : StrictMono (P.orderedBreakpoint P.prunedOrder) :=
  P.orderedBreakpoint_strictMono P.prunedOrder

#check @Parabolic.Family.ordered_pruning_specification
#check @Parabolic.Family.essential_strict_interval
#check @Parabolic.Family.essential_same_slope_maximal
