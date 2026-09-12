import BfgsVerification.ObjectiveEndToEnd
import BfgsVerification.PrincipalCombinatorialIdentity
import BfgsVerification.SharpPotentialTargets
import BfgsVerification.HessianUpdate

noncomputable section
open scoped BigOperators Topology
open Filter Matrix
namespace BfgsVerification.ClaimReview20M

/-- Review-local construction. Only the raw update and initial SPD are inputs. -/
def rawRun {n : ℕ} (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ)
    (c₂ : ℝ) (hH : (H 0).PosDef) (hg : ∀ k, g k ≠ 0)
    (hα : ∀ k, 0 < α k) (hc : c₂ < 1)
    (hw : ∀ k, c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)) ≤
      dot (g (k+1)) (bfgsStep (H k) (g k) (α k)))
    (hu : ∀ k, H (k+1) = inverseBFGS (H k)
      (bfgsStep (H k) (g k) (α k)) (g (k+1)-g k)) : FullBFGSRun n where
  H := H
  g := g
  α := α
  positive_definite := fun k => (fullBFGS_positive_invariants H g α c₂ hH hg hα hc hw hu k).1
  alpha_pos := hα
  energy_pos := fun k => (fullBFGS_positive_invariants H g α c₂ hH hg hα hc hw hu k).2.1
  curvature_pos := fun k => (fullBFGS_positive_invariants H g α c₂ hH hg hα hc hw hu k).2.2
  update := hu

variable {n : ℕ} (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ)
  (c₂ : ℝ) (hH : (H 0).PosDef) (hg : ∀ k, g k ≠ 0)
  (hα : ∀ k, 0 < α k) (hc : c₂ < 1)
  (hw : ∀ k, c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)) ≤
    dot (g (k+1)) (bfgsStep (H k) (g k) (α k)))
  (hu : ∀ k, H (k+1) = inverseBFGS (H k)
    (bfgsStep (H k) (g k) (α k)) (g (k+1)-g k))

include hH hg hα hc hw hu in
/-- M.2 with the positivity interface and reciprocal aliases removed from the conclusion. -/
theorem raw_reciprocal_means (G : ℝ) (hG : 0 < G)
    (hbound : ∀ k, sqNorm (g k) ≤ G^2)
    (hd : Tendsto (fun k => α k * metricEnergy (H k) (g k)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∏ k ∈ Finset.range N, (metricEnergy (H k) (g k))⁻¹) ^ ((N : ℝ)⁻¹)) atTop atTop ∧
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range N, (metricEnergy (H k) (g k))⁻¹) / (N : ℝ)) atTop atTop := by
  let R := rawRun H g α c₂ hH hg hα hc hw hu
  exact reciprocalGrowth n R G (1-c₂) hG (sub_pos.mpr hc) hbound
    (fun k => R.beta_ge_of_weakWolfe k c₂ (hw k)) hd

include hH hg hα hc hw hu in
/-- M.3 with only source raw hypotheses, without boundedness of any H_k. -/
theorem raw_superquadratic (G : ℝ) (hG : 0 < G)
    (hbound : ∀ k, sqNorm (g k) ≤ G^2)
    (hd : Summable (fun k => α k * metricEnergy (H k) (g k))) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range N, (metricEnergy (H k) (g k))⁻¹) / (N : ℝ)^2) atTop atTop := by
  let R := rawRun H g α c₂ hH hg hα hc hw hu
  exact superquadraticReciprocalGrowth n R G (1-c₂) hG (sub_pos.mpr hc) hbound
    (fun k => R.beta_ge_of_weakWolfe k c₂ (hw k)) hd

include hH hg hα hc hw hu in
/-- The literal source horizon m>=2, with the actual unnormalized tail D_J. -/
theorem raw_finite_horizon (G : ℝ) (hG : 0 < G)
    (hbound : ∀ k, sqNorm (g k) ≤ G^2)
    (hd : Summable (fun k => α k * metricEnergy (H k) (g k)))
    (J m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) :
    let c := 1-c₂
    let D := ∑' i : ℕ, α (J+i) * metricEnergy (H (J+i)) (g (J+i))
    let V := ∑ j ∈ Finset.range n, ((4*G^2/c^2)/η)^j * principalSum (H J) (j+1)
    (m : ℝ) * (G^2*V)^(-1/(m : ℝ)) *
      (η + D/(c*((m : ℝ)-1)))^(-((m : ℝ)-1)/(m : ℝ)) ≤
      ∑ i ∈ Finset.range m, (metricEnergy (H (J+i)) (g (J+i)))⁻¹ := by
  let R := rawRun H g α c₂ hH hg hα hc hw hu
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have hp : 0 < p := by omega
  have h := finiteHorizon R G (1-c₂) hG (sub_pos.mpr hc) hbound
    (fun k => R.beta_ge_of_weakWolfe k c₂ (hw k)) hd J p hp η hη
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    ScalarHierarchy.weightedPotential, FullBFGSRun.d, FullBFGSRun.q, R, rawRun] using h

include hH hg hα hc hw hu in
/-- Source fixed-tail liminf expressed by all strict eventual lower bounds. -/
theorem raw_fixed_tail_lower (G : ℝ) (hG : 0 < G)
    (hbound : ∀ k, sqNorm (g k) ≤ G^2)
    (hd : Summable (fun k => α k * metricEnergy (H k) (g k))) (J : ℕ) :
    let D := ∑' i : ℕ, α (J+i) * metricEnergy (H (J+i)) (g (J+i))
    0 < D ∧ ∀ a : ℝ, a < (1-c₂)/(2*D) →
      ∀ᶠ N : ℕ in atTop,
        a ≤ (∑ i ∈ Finset.range N, (metricEnergy (H i) (g i))⁻¹)/(N : ℝ)^2 := by
  let R := rawRun H g α c₂ hH hg hα hc hw hu
  let D := ∑' i : ℕ, R.d (J+i)
  have hc' : 0 < 1-c₂ := sub_pos.mpr hc
  have hs : Summable (fun i => R.d (J+i)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff J).2 hd
  have hD : 0 < D := hs.tsum_pos (fun i => (R.d_pos _).le) 0 (R.d_pos _)
  refine ⟨hD, ?_⟩
  intro a ha
  have hbudget (m : ℕ) : (∑ i ∈ Finset.range m, R.d (J+i)/(1-c₂)) ≤ D/(1-c₂) := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hs.sum_le_tsum _ (fun i _ => (R.d_pos _).le)) hc'.le
  have heq : (2*(D/(1-c₂)))⁻¹ = (1-c₂)/(2*D) := by
    field_simp
  have hi := QuantitativeGrowth.hierarchy_fixed_tail_lower_eventually
    (fullBFGS_normalizedHierarchy R G (1-c₂) hG hc' hbound
      (fun k => R.beta_ge_of_weakWolfe k c₂ (hw k)))
    (fun k => (div_pos (R.d_pos k) hc').le) J (D/(1-c₂))
      (div_pos hD hc') hbudget a (heq.symm ▸ ha)
  exact hi

include hH hg hα hc hw hu in
/-- The actual optimized potential root, with a fixed actual matrix H_J. -/
theorem raw_optimized_root (G : ℝ)
    (hd : Summable (fun k => α k * metricEnergy (H k) (g k))) (J : ℕ) :
    let D := ∑' i : ℕ, α (J+i) * metricEnergy (H (J+i)) (g (J+i))
    let c := 1-c₂
    Tendsto (fun m : ℕ =>
      (∑ j ∈ Finset.range n,
        ((4*G^2/c^2)/(D/(c*((m : ℝ)-1))))^j * principalSum (H J) (j+1)) ^
        (1/(m : ℝ))) atTop (𝓝 1) := by
  let R := rawRun H g α c₂ hH hg hα hc hw hu
  exact SharpPotentialDegree.run_optimized_root_tendsto R G (1-c₂) (sub_pos.mpr hc) hd J

/-- Identify the actual principal determinants with elementary eigenvalue products. -/
theorem actual_eigenvalue_principal_identity (H : Mat n) (hH : H.PosDef) :
    ∃ (U : Mat n) (lam : Vec n), Uᵀ*U=1 ∧ U*Uᵀ=1 ∧
      Uᵀ*H*U=Matrix.diagonal lam ∧ (∀ i, 0<lam i) ∧
      ∀ j : ℕ, principalSum H j =
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∏ i ∈ I, lam i := by
  obtain ⟨U,lam,hU,hUt,hdiag,hlam⟩ := posDef_orthogonal_diagonalization hH
  refine ⟨U,lam,hU,hUt,hdiag,hlam,?_⟩
  intro j
  rw [← PrincipalInvariance.principalSum_conjugate Uᵀ U H hU, hdiag,
    principalSum_diagonal]

/-- Source M.1 after expanding actual principal determinants and actual step. -/
theorem actual_principal_hierarchy (H : Mat n) (g y : Vec n) (α : ℝ)
    (hH : H.PosDef) (hα : 0<α) (hq : 0 < metricEnergy H g)
    (hβ : 0 < -dot y (H.mulVec g) / metricEnergy H g)
    (j : ℕ) (hj : 1≤j) (hjn : j≤n) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      ((inverseBFGS H (-α • H.mulVec g) y).submatrix
        (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det) ≤
    sqNorm y / ((-dot y (H.mulVec g) / metricEnergy H g)^2 * metricEnergy H g) *
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
        (H.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det) +
    α / (-dot y (H.mulVec g) / metricEnergy H g) *
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (H.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det) := by
  exact principalMinorHierarchy n H g y α hH hα hq hβ j hj hjn

end BfgsVerification.ClaimReview20M

namespace BfgsVerification.ClaimReview20M
/-- Independently transcribed literal Gram/eigenbasis display. -/
def ExpectedGram : Prop := ∀ {n : ℕ} (H : Mat n), H.PosDef →
  ∃ (U : Mat n) (lam : Vec n), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
    Uᵀ * H * U = Matrix.diagonal lam ∧ (∀ i, 0 < lam i) ∧
    ∀ (y : Vec n) (j : ℕ),
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
          (U * coordinateMatrix I))).det) =
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
        (∏ i ∈ J, lam i) * ∑ k ∈ J, (Uᵀ.mulVec y) k ^ 2

/-- Independently transcribed sharp degree, bound and fixed-tail root assertion. -/
def ExpectedSharp : Prop :=
  ∀ (n : ℕ) (R : FullBFGSRun n) (G c : ℝ), 0 < c → Summable R.d →
  ∀ J : ℕ,
    let D := ∑' i : ℕ, R.d (J+i)
    let K := 4*G^2/c^2
    ∃ p : Polynomial ℝ, p.natDegree ≤ n-1 ∧
      (∀ m : ℕ, 2 ≤ m →
        (∑ j ∈ Finset.range n, (K/(D/(c*((m : ℝ)-1))))^j * principalSum (R.H J) (j+1)) =
          p.eval ((m : ℝ)-1) ∧
        (∑ j ∈ Finset.range n, (K/(D/(c*((m : ℝ)-1))))^j * principalSum (R.H J) (j+1)) ≤
          (∑ j ∈ Finset.range n, (K/(D/c))^j * principalSum (R.H J) (j+1)) *
            ((m : ℝ)-1)^(n-1)) ∧
      Tendsto (fun m : ℕ =>
        (∑ j ∈ Finset.range n, (K/(D/(c*((m : ℝ)-1))))^j * principalSum (R.H J) (j+1)) ^
          (1/(m : ℝ))) atTop (𝓝 1)
end BfgsVerification.ClaimReview20M

open Lean Elab Command in
run_cmd do
  let checks := #[
    (``BfgsVerification.ClaimReview20M.actual_principal_hierarchy,
      ``BfgsVerification.PrincipalMinorHierarchyTarget, "M20_MATRIX_LITERAL"),
    (``BfgsVerification.principalGramSumIdentity,
      ``BfgsVerification.ClaimReview20M.ExpectedGram, "M20_GRAM_LITERAL"),
    (``BfgsVerification.sharpPrincipalPotential,
      ``BfgsVerification.ClaimReview20M.ExpectedSharp, "M20_SHARP_LITERAL")]
  for (name, expected, marker) in checks do
    let info ← getConstInfo name
    unless ← liftTermElabM (Meta.isDefEq info.type (mkConst expected)) do
      throwError "Expanded source contract mismatch: {name}"
    logInfo marker
  for name in #[``BfgsVerification.ClaimReview20M.raw_reciprocal_means,
      ``BfgsVerification.ClaimReview20M.raw_superquadratic,
      ``BfgsVerification.ClaimReview20M.raw_finite_horizon,
      ``BfgsVerification.ClaimReview20M.raw_fixed_tail_lower,
      ``BfgsVerification.ClaimReview20M.raw_optimized_root] do
    let info ← getConstInfo name
    for forbidden in #[``BfgsVerification.FullBFGSRun, ``BfgsVerification.ScalarHierarchy.NormalizedHierarchy] do
      if info.type.find? (fun e => e.isConstOf forbidden) |>.isSome then
        throwError "Unexpected assumed interface in raw contract: {name}"
    logInfo m!"M20_RAW_NO_ASSUMED_INTERFACE {name}"

#check BfgsVerification.ClaimReview20M.rawRun
#print BfgsVerification.ClaimReview20M.rawRun
#print axioms BfgsVerification.ClaimReview20M.rawRun
#check BfgsVerification.ClaimReview20M.raw_reciprocal_means
#print BfgsVerification.ClaimReview20M.raw_reciprocal_means
#print axioms BfgsVerification.ClaimReview20M.raw_reciprocal_means
#check BfgsVerification.ClaimReview20M.raw_superquadratic
#print BfgsVerification.ClaimReview20M.raw_superquadratic
#print axioms BfgsVerification.ClaimReview20M.raw_superquadratic
#check BfgsVerification.ClaimReview20M.raw_finite_horizon
#print BfgsVerification.ClaimReview20M.raw_finite_horizon
#print axioms BfgsVerification.ClaimReview20M.raw_finite_horizon
#check BfgsVerification.ClaimReview20M.raw_fixed_tail_lower
#print BfgsVerification.ClaimReview20M.raw_fixed_tail_lower
#print axioms BfgsVerification.ClaimReview20M.raw_fixed_tail_lower
#check BfgsVerification.ClaimReview20M.raw_optimized_root
#print BfgsVerification.ClaimReview20M.raw_optimized_root
#print axioms BfgsVerification.ClaimReview20M.raw_optimized_root
#check BfgsVerification.ClaimReview20M.actual_eigenvalue_principal_identity
#print BfgsVerification.ClaimReview20M.actual_eigenvalue_principal_identity
#print axioms BfgsVerification.ClaimReview20M.actual_eigenvalue_principal_identity
#check BfgsVerification.ClaimReview20M.actual_principal_hierarchy
#print BfgsVerification.ClaimReview20M.actual_principal_hierarchy
#print axioms BfgsVerification.ClaimReview20M.actual_principal_hierarchy
#check BfgsVerification.ClaimReview20M.ExpectedGram
#print BfgsVerification.ClaimReview20M.ExpectedGram
#print axioms BfgsVerification.ClaimReview20M.ExpectedGram
#check BfgsVerification.ClaimReview20M.ExpectedSharp
#print BfgsVerification.ClaimReview20M.ExpectedSharp
#print axioms BfgsVerification.ClaimReview20M.ExpectedSharp
#check BfgsVerification.principalMinorHierarchy
#print BfgsVerification.principalMinorHierarchy
#print axioms BfgsVerification.principalMinorHierarchy
#check BfgsVerification.fullBFGS_normalizedHierarchy
#print BfgsVerification.fullBFGS_normalizedHierarchy
#print axioms BfgsVerification.fullBFGS_normalizedHierarchy
#check BfgsVerification.reciprocalGrowth
#print BfgsVerification.reciprocalGrowth
#print axioms BfgsVerification.reciprocalGrowth
#check BfgsVerification.finiteHorizon
#print BfgsVerification.finiteHorizon
#print axioms BfgsVerification.finiteHorizon
#check BfgsVerification.superquadraticReciprocalGrowth
#print BfgsVerification.superquadraticReciprocalGrowth
#print axioms BfgsVerification.superquadraticReciprocalGrowth
#check BfgsVerification.objectiveReciprocalGrowth
#print BfgsVerification.objectiveReciprocalGrowth
#print axioms BfgsVerification.objectiveReciprocalGrowth
#check BfgsVerification.objectiveLowerBoundGrowth
#print BfgsVerification.objectiveLowerBoundGrowth
#print axioms BfgsVerification.objectiveLowerBoundGrowth
#check BfgsVerification.compactObjectiveGrowth
#print BfgsVerification.compactObjectiveGrowth
#print axioms BfgsVerification.compactObjectiveGrowth
#check BfgsVerification.objectiveFiniteHorizon_of_lower_bound
#print BfgsVerification.objectiveFiniteHorizon_of_lower_bound
#print axioms BfgsVerification.objectiveFiniteHorizon_of_lower_bound
#check BfgsVerification.objectiveGrowth_of_value_limit
#print BfgsVerification.objectiveGrowth_of_value_limit
#print axioms BfgsVerification.objectiveGrowth_of_value_limit
#check BfgsVerification.AdmissibleBFGSRun.toFullBFGSRun
#print BfgsVerification.AdmissibleBFGSRun.toFullBFGSRun
#print axioms BfgsVerification.AdmissibleBFGSRun.toFullBFGSRun
#check BfgsVerification.AdmissibleBFGSRun.positive_invariants
#print BfgsVerification.AdmissibleBFGSRun.positive_invariants
#print axioms BfgsVerification.AdmissibleBFGSRun.positive_invariants
#check BfgsVerification.AdmissibleBFGSRun.dimension_pos
#print BfgsVerification.AdmissibleBFGSRun.dimension_pos
#print axioms BfgsVerification.AdmissibleBFGSRun.dimension_pos
#check BfgsVerification.AdmissibleBFGSRun.beta_lower_bound
#print BfgsVerification.AdmissibleBFGSRun.beta_lower_bound
#print axioms BfgsVerification.AdmissibleBFGSRun.beta_lower_bound
#check BfgsVerification.inverseBFGS_step_det_beta
#print BfgsVerification.inverseBFGS_step_det_beta
#print axioms BfgsVerification.inverseBFGS_step_det_beta
#check BfgsVerification.principalGramSumIdentity
#print BfgsVerification.principalGramSumIdentity
#print axioms BfgsVerification.principalGramSumIdentity
#check BfgsVerification.sharpPrincipalPotential
#print BfgsVerification.sharpPrincipalPotential
#print axioms BfgsVerification.sharpPrincipalPotential
