import BfgsVerification.NormalSpikeVariableSeparation

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal

theorem variableObjective_not_differentiable_on_plane {n : ℕ} {a c x : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (hx : dot a x = 0)
    (hw : 0 < 1+dot c x) : ¬ DifferentiableAt ℝ (variableObjective a c) x := by
  intro hF
  have haa : dot a a = 1 := by simpa only [dot, sqNorm, pow_two] using ha
  have hca : dot c a = 0 := by change c ⬝ᵥ a = 0; rw [dotProduct_comm]; exact hc
  have hp : DifferentiableAt ℝ (fun t : ℝ => x+t • a) 0 :=
    (differentiableAt_const x).add (differentiableAt_id.smul_const a)
  have hcomp : DifferentiableAt ℝ (fun t : ℝ => variableObjective a c (x+t • a)) 0 := by
    have hF' : DifferentiableAt ℝ (variableObjective a c) (x+(0 : ℝ) • a) := by
      simpa only [zero_smul, add_zero] using hF
    convert hF'.comp (0 : ℝ) hp using 1
  have hquad : DifferentiableAt ℝ (fun t : ℝ => quadratic (x+t • a)) 0 := by
    have hq : DifferentiableAt ℝ (@quadratic n) (x+(0 : ℝ) • a) :=
      quadratic_contDiff.differentiable (by decide) _
    convert hq.comp (0 : ℝ) hp using 1
  have hR : DifferentiableAt ℝ sourcePrimitive 0 := (sourcePrimitive_hasDerivAt 0).differentiableAt
  have hd := (hcomp.sub hquad).sub hR
  have hwabs : DifferentiableAt ℝ (fun t : ℝ => (1+dot c x)*|t|) 0 := by
    convert hd using 1
    ext t
    simp only [variableObjective, dot_add_smul, hx, haa, hca, mul_one, mul_zero, zero_add,
      add_zero, abs_mul, abs_of_pos hw]
    ring
  have hdabs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    convert hwabs.const_mul ((1+dot c x)⁻¹) using 1
    ext t
    field_simp
  exact not_differentiableAt_abs_zero hdabs

theorem variableObjective_differentiable_iff_on_region {n : ℕ} {a c : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (x : Vec n) (hx : x ∈ variableRegion c) :
    DifferentiableAt ℝ (variableObjective a c) x ↔ dot a x ≠ 0 := by
  constructor
  · intro hd hzero
    exact variableObjective_not_differentiable_on_plane ha hc hzero (variableRegion_positive hx) hd
  · intro hne
    exact (variableObjective_contDiffAt_regular a c x (variableRegion_positive hx) hne).differentiableAt (by decide)

def printedVariableObjective (n : ℕ) (c : Vec (n+1)) : Vec (n+2) → ℝ :=
  variableObjective (normal n) (Fin.cons 0 c)

theorem extended_coupling_tangent (n : ℕ) (c : Vec (n+1)) :
    dot (normal n) (Fin.cons 0 c) = 0 := by rw [normal_coordinate, Fin.cons_zero]

theorem extended_coupling_sqNorm (n : ℕ) (c : Vec (n+1)) :
    sqNorm (Fin.cons 0 c) = sqNorm c := by
  simp only [sqNorm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]

theorem printed_variable_formula (n : ℕ) (c u : Vec (n+1)) (v : ℝ) :
    printedVariableObjective n c (Fin.cons v u) =
      (1/2 : ℝ)*(sqNorm u+v^2)+|(1+dot c u)*v|+sourcePrimitive v := by
  have hdot : dot (Fin.cons 0 c) (Fin.cons v u) = dot c u := by
    simp only [dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
  have hsq : sqNorm (Fin.cons v u) = v^2+sqNorm u := by
    simp only [sqNorm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [printedVariableObjective, variableObjective, quadratic, normal_coordinate, Fin.cons_zero, hdot, hsq]
  ring

theorem printed_variable_tangent_formula (n : ℕ) (c u : Vec (n+1)) (v : ℝ) :
    variableTangent (normal n) (Fin.cons 0 c) (Fin.cons v u) = Fin.cons 0 (u+|v| • c) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [variableTangent, normal_tangent_coordinate, normal_coordinate]
  · simp only [variableTangent, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      normal_tangent_coordinate, normal_coordinate, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, if_false]

theorem printed_variable_strongConvex (n : ℕ) (c : Vec (n+1)) :
    EuclideanStrongConvexOn univ (1-Real.sqrt (sqNorm c)) (printedVariableObjective n c) := by
  have hh := variableObjective_strongConvex (normal_unit n) (extended_coupling_tangent n c)
    (Real.sqrt_nonneg (sqNorm (Fin.cons 0 c))) (Real.sq_sqrt (sqNorm_nonneg (Fin.cons 0 c)))
  simpa only [extended_coupling_sqNorm] using hh

theorem printed_variable_local_fullBFGS (n : ℕ) (c : Vec (n+1)) (hc : Real.sqrt (sqNorm c) < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun (n+2) (printedVariableObjective n c),
      printedVariableObjective n c (R.x 0) < ε →
        Tendsto (fun k => printedVariableObjective n c (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  apply variableObjective_local_fullBFGS (normal_unit n) (extended_coupling_tangent n c)
  simpa only [extended_coupling_sqNorm] using hc

theorem printed_variable_no_radial_secant (n : ℕ) (c : Vec (n+1)) (hc : Real.sqrt (sqNorm c) < 1)
    {K : Set (Vec (n+2))} (hK : K ∈ 𝓝 0) :
    ¬ RadialCertificate.HasRadialSecantBounds (printedVariableObjective n c) K 0 := by
  apply variable_not_radial_secant_neighborhood n (extended_coupling_tangent n c) ?_ hK
  simpa only [extended_coupling_sqNorm] using hc

theorem printed_variable_no_local_smooth_scalar_split (n : ℕ) (c : Vec (n+1)) (hc : c ≠ 0)
    {U : Set (Vec (n+2))} (hU : IsOpen U) (h0 : (0 : Vec (n+2)) ∈ U)
    (S : Vec (n+2) → ℝ) (h : ℝ → ℝ) (hS : DifferentiableOn ℝ S U)
    (hrep : ∀ x ∈ U, printedVariableObjective n c x = S x+h (x 0)) : False := by
  have hcne : (Fin.cons 0 c : Vec (n+2)) ≠ 0 := by
    intro he
    apply hc
    ext i
    simpa only [Fin.cons_succ, Pi.zero_apply] using congrArg (fun x : Vec (n+2) => x i.succ) he
  apply variableObjective_no_local_smooth_scalar_split (normal_unit n) (extended_coupling_tangent n c)
    hcne hU h0 S h hS
  intro x hx
  simpa only [normal_coordinate] using hrep x hx

end BfgsVerification.NormalSpike
