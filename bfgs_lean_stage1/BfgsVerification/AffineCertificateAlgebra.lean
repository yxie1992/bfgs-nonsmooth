import BfgsVerification.AffineProjection
import BfgsVerification.TransportedCertificateVariants

/-! Actual affine coordinate changes for the objective-only certificate.
Gradients transform contragrediently; step and certificate vectors transform
by the original matrix. Projected transport is compared on perpendicular vectors. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Set

namespace BfgsVerification
namespace AffineCertificate
open AffineProjection TransportedCertificate

def forward {n : ℕ} (A : Mat n) (b x : Vec n) : Vec n := A.mulVec x + b
def backward {n : ℕ} (A : Mat n) (b z : Vec n) : Vec n := A⁻¹.mulVec (z - b)
def objective {n : ℕ} (A : Mat n) (b : Vec n) (F : Vec n → ℝ) : Vec n → ℝ :=
  fun z => F (backward A b z)
def field {n : ℕ} (A : Mat n) (b : Vec n) (W : Vec n → Mat n) : Vec n → Mat n :=
  fun z => A * W (backward A b z) * Aᵀ

theorem backward_forward {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b x : Vec n) :
    backward A b (forward A b x) = x := by
  simp only [backward, forward, add_sub_cancel_right, Matrix.mulVec_mulVec]
  rw [Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec]

theorem forward_backward {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b z : Vec n) :
    forward A b (backward A b z) = z := by
  simp only [backward, forward, Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]
  abel

theorem forward_difference {n : ℕ} (A : Mat n) (b x z : Vec n) :
    forward A b z - forward A b x = A.mulVec (z - x) := by
  rw [Matrix.mulVec_sub]
  simp only [forward]
  abel

theorem backward_difference {n : ℕ} (A : Mat n) (b x z : Vec n) :
    backward A b z - backward A b x = A⁻¹.mulVec (z - x) := by
  simp only [backward, ← Matrix.mulVec_sub]
  congr 1
  abel

theorem dot_inverse_transpose {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (g s : Vec n) :
    dot ((A⁻¹)ᵀ.mulVec g) (A.mulVec s) = dot g s := by
  rw [dot_transpose_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec]

theorem transpose_inverse_transpose {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (g : Vec n) :
    Aᵀ.mulVec ((A⁻¹)ᵀ.mulVec g) = g := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.transpose_one, Matrix.one_mulVec]

theorem inverse_transpose_transpose {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (g : Vec n) :
    (A⁻¹)ᵀ.mulVec (Aᵀ.mulVec g) = g := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.transpose_one, Matrix.one_mulVec]

/-- The backward affine map has its actual inverse-matrix derivative. -/
theorem backward_hasFDerivAt {n : ℕ} (A : Mat n) (b z : Vec n) :
    HasFDerivAt (backward A b) (matrixCLM A⁻¹) z := by
  simpa only [backward, ContinuousLinearMap.comp_id, Function.comp_def, matrixCLM_apply] using
    ((matrixCLM A⁻¹).hasFDerivAt (x := z - b)).comp z
      ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const b)

theorem forward_hasFDerivAt {n : ℕ} (A : Mat n) (b x : Vec n) :
    HasFDerivAt (forward A b) (matrixCLM A) x := by
  simpa only [forward, matrixCLM_apply] using
    ((matrixCLM A).hasFDerivAt (x := x)).add_const b

/-- Gradients transform by the actual inverse transpose, without a substitute
or unproved derivative oracle. -/
theorem transformed_gradient {n : ℕ} (A : Mat n) (b : Vec n) {F : Vec n → ℝ}
    {z g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) (backward A b z)) :
    HasFDerivAt (objective A b F) (gradientFunctional ((A⁻¹)ᵀ.mulVec g)) z := by
  simpa only [objective, Function.comp_def, gradientFunctional_comp] using
    hg.comp z (backward_hasFDerivAt A b z)

/-- Conversely, a transformed actual derivative gives the original derivative. -/
theorem original_gradient {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} {z h : Vec n}
    (hh : HasFDerivAt (objective A b F) (gradientFunctional h) z) :
    HasFDerivAt F (gradientFunctional (Aᵀ.mulVec h)) (backward A b z) := by
  have hh' : HasFDerivAt (objective A b F) (gradientFunctional h)
      (forward A b (backward A b z)) := by simpa only [forward_backward A hA] using hh
  have heq : (objective A b F) ∘ forward A b = F := by
    funext x
    simp only [Function.comp_apply, objective, backward_forward A hA]
  have hd := hh'.comp (backward A b z) (forward_hasFDerivAt A b _)
  rw [heq, gradientFunctional_comp] at hd
  exact hd

/-- Certificate congruence preserves all scalar energies exactly. -/
theorem transformed_energy {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (W : Mat n) (g : Vec n) :
    metricEnergy (A * W * Aᵀ) ((A⁻¹)ᵀ.mulVec g) = metricEnergy W g := by
  have he := metricEnergy_congruence W Aᵀ ((A⁻¹)ᵀ.mulVec g)
  simpa only [Matrix.transpose_transpose, transpose_inverse_transpose A hA] using he

theorem congruence_energy {n : ℕ} (A W : Mat n) (g : Vec n) :
    metricEnergy (A * W * Aᵀ) g = metricEnergy W (Aᵀ.mulVec g) := by
  simpa only [Matrix.transpose_transpose] using metricEnergy_congruence W Aᵀ g

/-- Transport has no preferred Euclidean coordinate projection: its
perpendicular quadratic formulation is invariant under affine coordinates. -/
theorem projected_transport_covariant {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (W Z : Mat n) (hW : W.IsSymm) (hZ : Z.IsSymm) (s : Vec n) (a : ℝ) :
    (a • (stepProjector s * W * stepProjector s) -
      stepProjector s * Z * stepProjector s).PosSemidef ↔
    (a • (stepProjector (A.mulVec s) * (A * W * Aᵀ) * stepProjector (A.mulVec s)) -
      stepProjector (A.mulVec s) * (A * Z * Aᵀ) * stepProjector (A.mulVec s)).PosSemidef := by
  have hAW : (A * W * Aᵀ).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hW.eq,
      Matrix.mul_assoc]
  have hAZ : (A * Z * Aᵀ).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hZ.eq,
      Matrix.mul_assoc]
  rw [projected_transport_iff_perpendicular W Z hW hZ s a,
    projected_transport_iff_perpendicular _ _ hAW hAZ (A.mulVec s) a]
  constructor
  · intro hb v hv
    rw [congruence_energy, congruence_energy]
    apply hb
    rw [dot_transpose_mulVec]
    exact hv
  · intro hb v hv
    have hn := hb ((A⁻¹)ᵀ.mulVec v) (by rw [dot_inverse_transpose A hA]; exact hv)
    simpa only [transformed_energy A hA] using hn

end AffineCertificate
end BfgsVerification
