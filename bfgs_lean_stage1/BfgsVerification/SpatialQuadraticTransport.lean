import BfgsVerification.SpatialQuadraticPairs
import BfgsVerification.TransportedCertificateVariants

/-! C's exact obstruction to scalar transport of the canonical common-rate
field. This excludes this field, not every possible BFGS certificate. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace SpatialQuadraticWarning
open TransportedCertificate

theorem canonicalField_base : canonicalField base = (1/14 : ℝ) • gradient base := by
  rw [canonicalField,base_gradient_sqNorm]
  norm_num

theorem canonicalField_unscale (ε : ℝ) :
    sqNorm (gradient (next ε)) • canonicalField (next ε) = gradient (next ε) := by
  rw [canonicalField,smul_smul,mul_inv_cancel₀ (next_gradient_sqNorm_pos ε).ne',one_smul]

/-- The source rank-one transport identity fails for every pair of finite real
coefficients, including zero coefficients; its failure is derived from the
literal nonzero determinant. -/
theorem canonicalField_not_scalar_transport {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    canonicalField (next ε) ≠ a • canonicalField base + b • step ε := by
  intro he
  have hu := canonicalField_unscale ε
  rw [he,canonicalField_base] at hu
  have hy : change ε =
      (sqNorm (gradient (next ε))*a*(1/14)-1) • gradient base +
      (sqNorm (gradient (next ε))*b) • step ε := by
    calc
      change ε = gradient (next ε)-gradient base := rfl
      _ = sqNorm (gradient (next ε)) •
          (a • (1/14 : ℝ) • gradient base+b • step ε)-gradient base :=
        congrArg (fun v => v-gradient base) hu.symm
      _ = _ := by module
  have hz : (tripleColumns (gradient base) (step ε) (change ε)).det = 0 := by
    rw [hy]
    exact determinant_of_linear_combination _ _ _ _
  exact (printed_determinant_pos hε).ne' hz

theorem canonicalField_not_in_span {ε : ℝ} (hε : 0 < ε) :
    canonicalField (next ε) ∉ Submodule.span ℝ ({canonicalField base,step ε} : Set (Vec 3)) := by
  rintro hmem
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hmem
  exact canonicalField_not_scalar_transport hε a b he.symm

theorem canonicalField_smooth_at_pair (ε : ℝ) {N : WithTop ℕ∞} :
    ContDiffAt ℝ N canonicalField base ∧ ContDiffAt ℝ N canonicalField (next ε) := by
  exact ⟨canonicalField_contDiffAt (by rw [base_gradient_sqNorm]; norm_num),
    canonicalField_contDiffAt (next_gradient_sqNorm_pos ε).ne'⟩

theorem canonicalField_equal_rate_at_pair (ε : ℝ) :
    dot (gradient base) (canonicalField base) = 1 ∧
      dot (gradient (next ε)) (canonicalField (next ε)) = 1 := by
  exact ⟨canonicalField_pairing (by rw [base_gradient_sqNorm]; norm_num),
    canonicalField_pairing (next_gradient_sqNorm_pos ε).ne'⟩

theorem radial_field_exact_transport (ε : ℝ) : next ε = base+step ε := rfl

def separatingVector (ε : ℝ) : Vec 3 := ![-2*(1+ε),10+ε,-6]

theorem separatingVector_pairings (ε : ℝ) :
    dot (separatingVector ε) (step ε) = 0 ∧
      dot (gradient base) (separatingVector ε) = 0 ∧
      dot (gradient (next ε)) (separatingVector ε) = 4*ε*(1+ε) := by
  rw [base_gradient,next_gradient]
  constructor
  · simp [separatingVector,step,dot,Fin.sum_univ_succ]
    ring
  constructor <;> simp [separatingVector,dot,Fin.sum_univ_succ] <;> ring

/-- The exact projected rank-one Loewner transport fails for every real
multiplier. An explicit step-perpendicular vector annihilates the old field
but has nonzero pairing with the new one. -/
theorem canonicalField_projected_transport_fails {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ¬(a • (stepProjector (step ε) * outer (canonicalField base) (canonicalField base) *
        stepProjector (step ε)) -
      stepProjector (step ε) * outer (canonicalField (next ε)) (canonicalField (next ε)) *
        stepProjector (step ε)).PosSemidef := by
  intro h
  have hsymm (v : Vec 3) : (outer v v).IsSymm := by
    ext i j
    simp [outer,mul_comm]
  have hb := (projected_transport_iff_perpendicular _ _
    (hsymm _) (hsymm _) (step ε) a).mp h
    (separatingVector ε) (separatingVector_pairings ε).1
  have henergy (u v : Vec 3) : metricEnergy (outer u u) v = (dot u v)^2 := by
    rw [metricEnergy,outer_mulVec,dot_smul_right]
    rw [show dot v u = dot u v from dotProduct_comm _ _]
    ring
  rw [henergy,henergy] at hb
  have hold : dot (canonicalField base) (separatingVector ε) = 0 := by
    rw [canonicalField_base]
    change ((1/14 : ℝ) • gradient base) ⬝ᵥ separatingVector ε = 0
    rw [smul_dotProduct]
    change (1/14 : ℝ) * dot (gradient base) (separatingVector ε) = 0
    rw [(separatingVector_pairings ε).2.1,mul_zero]
  have hnew : 0 < dot (canonicalField (next ε)) (separatingVector ε) := by
    rw [canonicalField]
    change 0 < ((sqNorm (gradient (next ε)))⁻¹ • gradient (next ε)) ⬝ᵥ separatingVector ε
    rw [smul_dotProduct]
    change 0 < (sqNorm (gradient (next ε)))⁻¹ * dot (gradient (next ε)) (separatingVector ε)
    rw [(separatingVector_pairings ε).2.2]
    exact mul_pos (inv_pos.mpr (next_gradient_sqNorm_pos ε)) (by positivity)
  rw [hold,zero_pow (by decide : 2 ≠ 0),mul_zero] at hb
  exact (not_le_of_gt (sq_pos_of_pos hnew)) hb

end SpatialQuadraticWarning
end BfgsVerification
