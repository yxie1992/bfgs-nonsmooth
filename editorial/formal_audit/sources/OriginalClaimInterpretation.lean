import BfgsVerification.OptimizerInterceptExamples
import BfgsVerification.NormalSpikeVariableTargets

noncomputable section
open Set
namespace BfgsVerification.OriginalClaimInterpretation

/-- Degree zero forces constancy under the actual homogeneity definition. -/
theorem degree_zero_constant {n : ℕ} {F : Vec n → ℝ}
    (h : InterceptExamples.PositiveDegree 0 F) (x : Vec n) : F x = F 0 := by
  simpa using (h 0 le_rfl x).symm

/-- The general formula's constant term cannot be dropped without a convention. -/
theorem degree_zero_intercept {n : ℕ} {F : Vec n → ℝ}
    (h : InterceptExamples.PositiveDegree 0 F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F 0 x g = 0 := by
  rw [InterceptExamples.degree_intercept_with_zero_value h hg,
    degree_zero_constant h x]
  ring

theorem positive_constant_homogeneous :
    InterceptExamples.PositiveDegree 0 (fun _ : Vec 1 => (1 : ℝ)) := by
  intro t ht x
  simp

theorem positive_constant_derivative (x : Vec 1) :
    HasFDerivAt (fun _ : Vec 1 => (1 : ℝ)) (gradientFunctional 0) x := by
  simpa [gradientFunctional] using (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x)

/-- A counterexample to the unrestricted displayed identity, not to a compact
sublevel convergence theorem. The compact-sublevel issue is checked separately. -/
theorem unrestricted_zero_degree_formula_fails (x : Vec 1) :
    RadialCertificate.optimizerIntercept (fun _ : Vec 1 => (1 : ℝ)) 0 x 0 ≠
      ((0 : ℝ) - 1) * 1 := by
  rw [degree_zero_intercept positive_constant_homogeneous (positive_constant_derivative x)]
  norm_num

theorem degree_zero_positive_sublevel_not_compact (n : ℕ) {F : Vec (n+1) → ℝ}
    (hh : InterceptExamples.PositiveDegree 0 F) {b : ℝ} (hb : F 0 < b) :
    ¬IsCompact {x | F x ≤ b} := by
  have he : {x | F x ≤ b} = (univ : Set (Vec (n+1))) := by
    ext x
    simp only [mem_setOf_eq, mem_univ, iff_true]
    rw [degree_zero_constant hh x]
    exact hb.le
  rw [he]
  exact noncompact_univ _

/-- Under R's actual compact positive-sublevel hypotheses in positive
finite dimension, positivity of the homogeneous degree is a consequence. -/
theorem compact_nonnegative_homogeneity_positive_degree (n : ℕ)
    {F : Vec (n+1) → ℝ} (hF : ConvexOn ℝ univ F)
    (hnonneg : ∀ x, 0 ≤ F x) {p b : ℝ}
    (hh : InterceptExamples.PositiveDegree p F) {z : Vec (n+1)} (hb : F z < b)
    (hK : IsCompact {x | F x ≤ b}) : 0 < p := by
  by_contra hn
  have hp : p ≤ 0 := le_of_not_gt hn
  have hpow : (2 : ℝ)^p ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hp
  have hupper : ∀ x, F x ≤ F 0 := by
    intro x
    have hc := hF.2 (show (2 : ℝ) • x ∈ univ by trivial)
      (show (0 : Vec (n+1)) ∈ univ by trivial)
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (1/2 : ℝ)+1/2=1 by norm_num)
    have he : (1/2 : ℝ) • ((2 : ℝ) • x) + (1/2 : ℝ) • (0 : Vec (n+1)) = x := by
      simp [smul_smul]
    rw [he, hh 2 (by norm_num) x] at hc
    simp only [smul_eq_mul] at hc
    have hm := mul_le_mul_of_nonneg_right hpow (hnonneg x)
    simp only [one_mul] at hm
    linarith
  have hconst : ∀ x, F x = F 0 := by
    intro x
    have hc := hF.2 (show x ∈ univ by trivial) (show -x ∈ univ by trivial)
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (1/2 : ℝ)+1/2=1 by norm_num)
    have he : (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) = 0 := by module
    rw [he] at hc
    simp only [smul_eq_mul] at hc
    have hx := hupper x
    have hn := hupper (-x)
    linarith
  have he : {x | F x ≤ b} = (univ : Set (Vec (n+1))) := by
    ext x
    simp only [mem_setOf_eq, mem_univ, iff_true]
    rw [hconst x]
    rw [hconst z] at hb
    exact hb.le
  rw [he] at hK
  exact noncompact_univ _ hK

/-- R's displayed degree-p identity with its compact context; positive degree
is derived rather than added to the source hypotheses. -/
theorem compact_degree_intercept (n : ℕ) {F : Vec (n+1) → ℝ}
    (hF : ConvexOn ℝ univ F) (hnonneg : ∀ x, 0 ≤ F x) {p b : ℝ}
    (hh : InterceptExamples.PositiveDegree p F) {z : Vec (n+1)} (hb : F z < b)
    (hK : IsCompact {x | F x ≤ b}) {x g : Vec (n+1)}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F 0 x g = (p-1)*F x :=
  InterceptExamples.degree_intercept
    (compact_nonnegative_homogeneity_positive_degree n hF hnonneg hh hb hK) hh hg

theorem positive_constant_convex :
    ConvexOn ℝ univ (fun _ : Vec 1 => (1 : ℝ)) :=
  convexOn_const 1 convex_univ

theorem positive_constant_assumptions :
    (∀ _ : Vec 1, (0 : ℝ) ≤ 1) ∧
    IsMinOn (fun _ : Vec 1 => (1 : ℝ)) univ 0 := by
  constructor
  · intro x
    norm_num
  · exact isMinOn_const

theorem zero_coupling_split {n : ℕ} (a x : Vec n) :
    NormalSpike.variableObjective a 0 x =
      NormalSpike.quadratic x + (NormalSpike.sourcePrimitive (dot a x) + |dot a x|) := by
  simp [NormalSpike.variableObjective, dot]
  ring

theorem quadratic_smooth {n : ℕ} : ContDiff ℝ ⊤ (@NormalSpike.quadratic n) := by
  unfold NormalSpike.quadratic sqNorm
  apply contDiff_const.mul
  exact ContDiff.sum (fun i _ => (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).contDiff.pow 2)

/-- The parameter allowed by U's norm restriction can be zero, in which case
there is an actual smooth-plus-scalar representation. -/
theorem printed_zero_coupling_has_split (n : ℕ) :
    Real.sqrt (sqNorm (0 : Vec (n+1))) < 1 ∧
    ∃ (S : Vec (n+2) → ℝ) (h : ℝ → ℝ), ContDiff ℝ ⊤ S ∧
      ∀ x, NormalSpike.printedVariableObjective n 0 x = S x + h (x 0) := by
  refine ⟨by simp [sqNorm], NormalSpike.quadratic,
    (fun t => NormalSpike.sourcePrimitive t + |t|), quadratic_smooth, ?_⟩
  intro x
  have hc : Fin.cons (0 : ℝ) (0 : Vec (n+1)) = (0 : Vec (n+2)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [NormalSpike.printedVariableObjective, hc, zero_coupling_split]
  rw [NormalSpike.normal_coordinate]

/-- A zero-valued homogeneous ray cannot lie in a bounded nonnegative sublevel
unless its generating vector is zero. No positive-degree premise is needed. -/
theorem zero_value_eq_zero_of_compact_sublevel {n : ℕ} {F : Vec n → ℝ}
    {p b : ℝ} (hh : InterceptExamples.PositiveDegree p F) (hb : 0 ≤ b)
    (hK : IsCompact {x | F x ≤ b}) {x : Vec n} (hx : F x = 0) : x = 0 := by
  by_contra hne
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hne
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  let t := (|M| + 1) / ‖x‖
  have ht : 0 < t := div_pos (by positivity) hnx
  have hv : F (t • x) ≤ b := by
    rw [hh t ht.le x, hx, mul_zero]
    exact hb
  have hn := hM (t • x) hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hn
  dsimp only [t] at hn
  rw [div_mul_cancel₀ _ hnx.ne'] at hn
  linarith [le_abs_self M]

/-- In the original compact homogeneous context, the optimizer is necessarily
the origin. The origin is not selected by convention. -/
theorem compact_homogeneous_minimizer_eq_zero (n : ℕ) {F : Vec (n+1) → ℝ}
    (hF : ConvexOn ℝ univ F) (hnonneg : ∀ x, 0 ≤ F x) {p b : ℝ}
    (hh : InterceptExamples.PositiveDegree p F) {z : Vec (n+1)} (hb : F z < b)
    (hK : IsCompact {x | F x ≤ b}) {xStar : Vec (n+1)}
    (hmin : IsMinOn F univ xStar) : xStar = 0 := by
  have hp := compact_nonnegative_homogeneity_positive_degree n hF hnonneg hh hb hK
  have h0 := InterceptExamples.degree_value_zero hp hh
  have hs : F xStar = 0 := le_antisymm
    (by simpa only [mem_setOf_eq, h0] using hmin (mem_univ (0 : Vec (n+1)))) (hnonneg xStar)
  exact zero_value_eq_zero_of_compact_sublevel hh (lt_of_le_of_lt (hnonneg z) hb).le hK hs

/-- Literal homogeneous supporting-error identity for any optimizer in R's
compact positive-sublevel setting. Positivity of the degree and the optimizer's
location are derived, not added to the hypotheses. -/
theorem compact_homogeneous_optimizer_intercept (n : ℕ) {F : Vec (n+1) → ℝ}
    (hF : ConvexOn ℝ univ F) (hnonneg : ∀ x, 0 ≤ F x) {p b : ℝ}
    (hh : InterceptExamples.PositiveDegree p F) {z : Vec (n+1)} (hb : F z < b)
    (hK : IsCompact {x | F x ≤ b}) {xStar : Vec (n+1)}
    (hmin : IsMinOn F univ xStar) {x g : Vec (n+1)}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F xStar x g = (p-1)*F x := by
  rw [compact_homogeneous_minimizer_eq_zero n hF hnonneg hh hb hK hmin]
  exact compact_degree_intercept n hF hnonneg hh hb hK hg

/-- The homogeneous Euler identity at an arbitrary reference point, without
an optimizer or zero-reference convention. -/
theorem degree_intercept_at_reference {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hh : InterceptExamples.PositiveDegree p F) (xStar : Vec n) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F xStar x g =
      (p-1)*F x + F xStar - dot g xStar := by
  have he : dot g (x-xStar) = dot g x - dot g xStar := by
    simp [dot, mul_sub, Finset.sum_sub_distrib]
  rw [RadialCertificate.optimizerIntercept, he, InterceptExamples.degree_euler hh hg]
  ring

end BfgsVerification.OriginalClaimInterpretation

#check BfgsVerification.OriginalClaimInterpretation.degree_zero_constant
#print axioms BfgsVerification.OriginalClaimInterpretation.degree_zero_constant
#check BfgsVerification.OriginalClaimInterpretation.degree_zero_intercept
#print axioms BfgsVerification.OriginalClaimInterpretation.degree_zero_intercept
#check BfgsVerification.OriginalClaimInterpretation.positive_constant_homogeneous
#print axioms BfgsVerification.OriginalClaimInterpretation.positive_constant_homogeneous
#check BfgsVerification.OriginalClaimInterpretation.positive_constant_derivative
#print axioms BfgsVerification.OriginalClaimInterpretation.positive_constant_derivative
#check BfgsVerification.OriginalClaimInterpretation.unrestricted_zero_degree_formula_fails
#print axioms BfgsVerification.OriginalClaimInterpretation.unrestricted_zero_degree_formula_fails
#check BfgsVerification.OriginalClaimInterpretation.degree_zero_positive_sublevel_not_compact
#print axioms BfgsVerification.OriginalClaimInterpretation.degree_zero_positive_sublevel_not_compact
#check BfgsVerification.OriginalClaimInterpretation.compact_nonnegative_homogeneity_positive_degree
#print axioms BfgsVerification.OriginalClaimInterpretation.compact_nonnegative_homogeneity_positive_degree
#check BfgsVerification.OriginalClaimInterpretation.compact_degree_intercept
#print axioms BfgsVerification.OriginalClaimInterpretation.compact_degree_intercept
#check BfgsVerification.OriginalClaimInterpretation.positive_constant_convex
#print axioms BfgsVerification.OriginalClaimInterpretation.positive_constant_convex
#check BfgsVerification.OriginalClaimInterpretation.positive_constant_assumptions
#print axioms BfgsVerification.OriginalClaimInterpretation.positive_constant_assumptions
#check BfgsVerification.OriginalClaimInterpretation.zero_coupling_split
#print axioms BfgsVerification.OriginalClaimInterpretation.zero_coupling_split
#check BfgsVerification.OriginalClaimInterpretation.quadratic_smooth
#print axioms BfgsVerification.OriginalClaimInterpretation.quadratic_smooth
#check BfgsVerification.OriginalClaimInterpretation.printed_zero_coupling_has_split
#print axioms BfgsVerification.OriginalClaimInterpretation.printed_zero_coupling_has_split

#check BfgsVerification.OriginalClaimInterpretation.zero_value_eq_zero_of_compact_sublevel
#print axioms BfgsVerification.OriginalClaimInterpretation.zero_value_eq_zero_of_compact_sublevel

#check BfgsVerification.OriginalClaimInterpretation.compact_homogeneous_minimizer_eq_zero
#print axioms BfgsVerification.OriginalClaimInterpretation.compact_homogeneous_minimizer_eq_zero

#check BfgsVerification.OriginalClaimInterpretation.compact_homogeneous_optimizer_intercept
#print axioms BfgsVerification.OriginalClaimInterpretation.compact_homogeneous_optimizer_intercept

#check BfgsVerification.OriginalClaimInterpretation.degree_intercept_at_reference
#print axioms BfgsVerification.OriginalClaimInterpretation.degree_intercept_at_reference
