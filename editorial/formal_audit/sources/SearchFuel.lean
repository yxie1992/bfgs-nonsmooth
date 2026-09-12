import BfgsVerification.DeterministicLineSearch

noncomputable section
namespace BfgsVerification.DeterministicLineSearch
/-- A successful fuel-bounded search is independent of any additional fuel.
Thus the `5` in the negative-example contracts is a proved termination bound,
not a truncation or replacement of any acceptance/rejection decision. -/
theorem review20SearchFuelExtension {n : ℕ} (F : Vec n → ℝ) (x p g : Vec n)
    (c₁ c₂ : ℝ) (fuel extra : ℕ) (l : ℝ) (h : Option ℝ) (a : ℝ)
    (hs : (search F x p g c₁ c₂ fuel l h a).1 ≠ none) :
    search F x p g c₁ c₂ (fuel+extra) l h a = search F x p g c₁ c₂ fuel l h a := by
  classical
  induction fuel generalizing l h a with
  | zero => simp [search] at hs
  | succ fuel ih =>
    rw [Nat.succ_add]
    by_cases ha : Armijo F x p g c₁ a
    · by_cases hw : Wolfe F x p g c₂ a
      · simp only [search,if_pos ha,if_pos hw]
      · simp only [search,if_pos ha,if_neg hw] at hs ⊢
        rw [ih _ _ _ hs]
    · simp only [search,if_neg ha] at hs ⊢
      rw [ih _ _ _ hs]
end BfgsVerification.DeterministicLineSearch

#check BfgsVerification.DeterministicLineSearch.review20SearchFuelExtension
#print axioms BfgsVerification.DeterministicLineSearch.review20SearchFuelExtension
run_cmd Lean.Elab.Command.liftTermElabM do
  let n := `BfgsVerification.DeterministicLineSearch.review20SearchFuelExtension
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels n
  let ty ← Lean.Meta.inferType actual
  let axioms ← Lean.collectAxioms n
  let j := Lean.Json.mkObj [("name",Lean.toJson n.toString),
    ("type",Lean.toJson (toString (← Lean.Meta.ppExpr ty))),
    ("axioms",Lean.toJson (axioms.toList.map Lean.Name.toString))]
  Lean.logInfo ("NEGATIVE_REPORT|" ++ j.compress)
  Lean.logInfo "NEGATIVE_FUEL_AUDIT_COMPLETE"
