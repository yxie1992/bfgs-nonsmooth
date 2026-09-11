import BfgsVerification.ConstantRankTargets
import Lean
open scoped Topology ContDiff
open Set Filter
open BfgsVerification BfgsVerification.ConstantRankFields BfgsVerification.AffineCriticalObjective BfgsVerification.ConvexSubdifferential BfgsVerification.TransportedCertificate
#check BfgsVerification.ConstantRankFields.matrix_det_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.matrix_det_contDiffAt
#check BfgsVerification.ConstantRankFields.matrix_adjugate_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.matrix_adjugate_contDiffAt
#check BfgsVerification.ConstantRankFields.matrix_inverse_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.matrix_inverse_contDiffAt
#check BfgsVerification.ConstantRankFields.augmented_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.augmented_contDiffAt
#check BfgsVerification.ConstantRankFields.gram_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.gram_contDiffAt
#check BfgsVerification.ConstantRankFields.formulaPoint_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.formulaPoint_contDiffAt
#check BfgsVerification.ConstantRankFields.exists_affine_basis_indices
#print axioms BfgsVerification.ConstantRankFields.exists_affine_basis_indices
#check BfgsVerification.ConstantRankFields.fixed_basis_spans_near
#print axioms BfgsVerification.ConstantRankFields.fixed_basis_spans_near
#check BfgsVerification.ConstantRankFields.differenceMatrix
#print axioms BfgsVerification.ConstantRankFields.differenceMatrix
#check BfgsVerification.ConstantRankFields.differenceMatrix_rank
#print axioms BfgsVerification.ConstantRankFields.differenceMatrix_rank
#check BfgsVerification.ConstantRankFields.euclidean_affineSpan_eq
#print axioms BfgsVerification.ConstantRankFields.euclidean_affineSpan_eq
#check BfgsVerification.ConstantRankFields.closest_eq_of_affineSpan_eq
#print axioms BfgsVerification.ConstantRankFields.closest_eq_of_affineSpan_eq
#check BfgsVerification.ConstantRankFields.closest_contDiffAt_of_constant_rank
#print axioms BfgsVerification.ConstantRankFields.closest_contDiffAt_of_constant_rank
#check BfgsVerification.ConstantRankFields.commonRate
#print axioms BfgsVerification.ConstantRankFields.commonRate
#check BfgsVerification.ConstantRankFields.commonRate_pairing
#print axioms BfgsVerification.ConstantRankFields.commonRate_pairing
#check BfgsVerification.ConstantRankFields.commonRate_contDiffAt_of_constant_rank
#print axioms BfgsVerification.ConstantRankFields.commonRate_contDiffAt_of_constant_rank
#check BfgsVerification.ConstantRankFields.commonRate_chart
#print axioms BfgsVerification.ConstantRankFields.commonRate_chart
#check BfgsVerification.ConstantRankFields.commonRateVector
#print axioms BfgsVerification.ConstantRankFields.commonRateVector
#check BfgsVerification.ConstantRankFields.coordinateGradient_contDiffAt
#print axioms BfgsVerification.ConstantRankFields.coordinateGradient_contDiffAt
#check BfgsVerification.ConstantRankFields.commonRateVector_chart
#print axioms BfgsVerification.ConstantRankFields.commonRateVector_chart
#check BfgsVerification.ConstantRankFields.affine_zero_excluded_of_active_family
#print axioms BfgsVerification.ConstantRankFields.affine_zero_excluded_of_active_family
#check BfgsVerification.ConstantRankFields.active_family_objective_chart
#print axioms BfgsVerification.ConstantRankFields.active_family_objective_chart
#check BfgsVerification.ConstantRankFields.dot_constant_on_affineSpan
#print axioms BfgsVerification.ConstantRankFields.dot_constant_on_affineSpan
#check BfgsVerification.ConstantRankFields.support_pairing_of_branch_pairings
#print axioms BfgsVerification.ConstantRankFields.support_pairing_of_branch_pairings
#check BfgsVerification.ConstantRankFields.original_active_commonRate_chart
#print axioms BfgsVerification.ConstantRankFields.original_active_commonRate_chart
#check BfgsVerification.ConstantRankFields.exists_one_sided_constant_on_compact
#print axioms BfgsVerification.ConstantRankFields.exists_one_sided_constant_on_compact
#check BfgsVerification.ConstantRankFields.LocallyConstantActiveRank
#print axioms BfgsVerification.ConstantRankFields.LocallyConstantActiveRank
#check BfgsVerification.ConstantRankFields.locallyConstantActiveRank_all_bases
#print axioms BfgsVerification.ConstantRankFields.locallyConstantActiveRank_all_bases
#check BfgsVerification.ConstantRankFields.RateChart
#print axioms BfgsVerification.ConstantRankFields.RateChart
#check BfgsVerification.ConstantRankFields.nonempty_rateChart
#print axioms BfgsVerification.ConstantRankFields.nonempty_rateChart
#check BfgsVerification.ConstantRankFields.locallyC11_of_contDiffOn
#print axioms BfgsVerification.ConstantRankFields.locallyC11_of_contDiffOn
#check BfgsVerification.ConstantRankFields.RateChart.one_sided_bounds
#print axioms BfgsVerification.ConstantRankFields.RateChart.one_sided_bounds
#check BfgsVerification.ConstantRankFields.FiniteRatePatch
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch
#check BfgsVerification.ConstantRankFields.exists_finite_ratePatch
#print axioms BfgsVerification.ConstantRankFields.exists_finite_ratePatch
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.field
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.field
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.fieldC1
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.fieldC1
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.small_of_cutoff_ne_zero
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.small_of_cutoff_ne_zero
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.pairing_of_local
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.pairing_of_local
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.supportsPairing
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.supportsPairing
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.buffer_radius
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.buffer_radius
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.uniform_one_sided
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.uniform_one_sided
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.field_bound
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.field_bound
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.cross_pairing
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.cross_pairing
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.secant_bound
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.secant_bound
#check BfgsVerification.ConstantRankFields.source_common_rate_and_secant
#print axioms BfgsVerification.ConstantRankFields.source_common_rate_and_secant
#check BfgsVerification.ConstantRankFields.locally_constant_rank_of_affineIndependent
#print axioms BfgsVerification.ConstantRankFields.locally_constant_rank_of_affineIndependent
#check BfgsVerification.ConstantRankFields.active_affineIndependent_implies_locallyConstantActiveRank
#print axioms BfgsVerification.ConstantRankFields.active_affineIndependent_implies_locallyConstantActiveRank
#check BfgsVerification.ConstantRankFields.source_eligible_common_rate
#print axioms BfgsVerification.ConstantRankFields.source_eligible_common_rate
#check BfgsVerification.ConstantRankFields.SourceConstantRankTarget
#print axioms BfgsVerification.ConstantRankFields.SourceConstantRankTarget
#check BfgsVerification.ConstantRankFields.sourceConstantRank
#print axioms BfgsVerification.ConstantRankFields.sourceConstantRank
#check BfgsVerification.ConstantRankFields.SourceConstantRankEligibleTarget
#print axioms BfgsVerification.ConstantRankFields.SourceConstantRankEligibleTarget
#check BfgsVerification.ConstantRankFields.sourceConstantRankEligible
#print axioms BfgsVerification.ConstantRankFields.sourceConstantRankEligible
#check BfgsVerification.ConstantRankFields.RateChart.mk
#print axioms BfgsVerification.ConstantRankFields.RateChart.mk
#check BfgsVerification.ConstantRankFields.RateChart.radius
#print axioms BfgsVerification.ConstantRankFields.RateChart.radius
#check BfgsVerification.ConstantRankFields.RateChart.radius_pos
#print axioms BfgsVerification.ConstantRankFields.RateChart.radius_pos
#check BfgsVerification.ConstantRankFields.RateChart.field
#print axioms BfgsVerification.ConstantRankFields.RateChart.field
#check BfgsVerification.ConstantRankFields.RateChart.fieldC1
#print axioms BfgsVerification.ConstantRankFields.RateChart.fieldC1
#check BfgsVerification.ConstantRankFields.RateChart.originalPairing
#print axioms BfgsVerification.ConstantRankFields.RateChart.originalPairing
#check BfgsVerification.ConstantRankFields.RateChart.supportsPairing
#print axioms BfgsVerification.ConstantRankFields.RateChart.supportsPairing
#check BfgsVerification.ConstantRankFields.RateChart.activeSubset
#print axioms BfgsVerification.ConstantRankFields.RateChart.activeSubset
#check BfgsVerification.ConstantRankFields.RateChart.representation
#print axioms BfgsVerification.ConstantRankFields.RateChart.representation
#check BfgsVerification.ConstantRankFields.RateChart.branchC2
#print axioms BfgsVerification.ConstantRankFields.RateChart.branchC2
#check BfgsVerification.ConstantRankFields.RateChart.branchConvex
#print axioms BfgsVerification.ConstantRankFields.RateChart.branchConvex
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.mk
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.mk
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.size
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.size
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.center
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.center
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.chart
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.chart
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.cutoff
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.cutoff
#check BfgsVerification.ConstantRankFields.FiniteRatePatch.subordinate
#print axioms BfgsVerification.ConstantRankFields.FiniteRatePatch.subordinate

private def ReviewedSourceStatement : Prop := ∀ {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) {K : Set (Vec n)}
    (hK : IsCompact K) (hrep : ∀p∈K,LocalFiniteMax F f p)
    (hC2 : ∀p∈K,∀j,ContDiffAt ℝ 2 (f j) p)
    (hconv : ∀p∈K,∃V : Set (Vec n),IsOpen V ∧ p∈V ∧ ∀j,ConvexOn ℝ V (f j))
    (hnc : ∀p∈K,¬IsAffineCritical F p)
    (hrank : ∀p∈K,LocallyConstantActiveRank F f p),
    ∃v : Vec n → Vec n,ContDiff ℝ 1 v ∧ ∃V Q : Set (Vec n),
      IsOpen V ∧ K⊆V ∧ closure V⊆Q ∧ IsCompact Q ∧
      ∃G δ C : ℝ,0<G ∧ 0<δ ∧ 0≤C ∧
      (∀x∈Q,sqNorm (v x)≤G^2) ∧
      (∀x∈Q,∀g∈subdifferential F x,dot g (v x)=1) ∧
      ∀x z g h : Vec n,x∈Q → z∈Q → ‖euclideanVector (z-x)‖<δ →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        0<pairCurvature x z g h → (dot (h-g) (v z))^2 / pairCurvature x z g h ≤ C
example : ReviewedSourceStatement := @source_common_rate_and_secant
example : ReviewedSourceStatement := sourceConstantRank
run_elab do
  let t := (← Lean.getConstInfo ``BfgsVerification.ConstantRankFields.sourceConstantRank).type
  let e ← Lean.Elab.Term.elabTerm (← `(ReviewedSourceStatement)) none
  unless ← Lean.Meta.isDefEq t e do throwError "source theorem changed"
  Lean.logInfo "INDEPENDENT_EXACT_SOURCE_OK"
