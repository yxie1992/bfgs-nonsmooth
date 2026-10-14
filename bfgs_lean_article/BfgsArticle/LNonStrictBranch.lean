import BfgsArticle.LNonStrictLocal
import ArticleBranchRegularity

/-!
# Article endpoint for Theorem `art:local-failure-lower`

`ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction` (the
existing supplement) states the smooth local-failure contract with the strict
search. This is the same endpoint with the article's non-strict search trace.
-/

noncomputable section
namespace ArticleBranchRegularity
open BfgsVerification

theorem nonstrictSmoothLocalFailure_with_branch_obstruction :
    LWhitening.NonStrictSmoothLocalFailureTarget ∧
      ∀ i : Fin 3, ¬ DifferentiableAt ℝ
        (fderiv ℝ (LWhitening.smoothBranch i.castSucc)) (0 : Vec 2) :=
  ⟨LWhitening.nonstrictSmoothLocalFailure,whitened_branch_not_twice_differentiable_zero⟩

end ArticleBranchRegularity
