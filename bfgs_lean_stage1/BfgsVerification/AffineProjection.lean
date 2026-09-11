import BfgsVerification.ConvexGradientLimits
import BfgsVerification.RunShift
import BfgsVerification.BFGSCompression

/-! Exact rectangular projection and actual derivative descent. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection

/-- Full row rank means genuine linear independence of the transposed columns. -/
def FullRowRank {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  Function.Injective Aᵀ.mulVec

def compress {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (H : Mat n) : Mat r :=
  A * H * Aᵀ

def lift {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (H : Mat n) :
    Matrix (Fin n) (Fin r) ℝ := H * Aᵀ * (compress A H)⁻¹

def rightInverse {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin n) (Fin r) ℝ := Aᵀ * (A * Aᵀ)⁻¹

def matrixCLM {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) : Vec n →L[ℝ] Vec r :=
  LinearMap.toContinuousLinearMap A.mulVecLin

@[simp] theorem matrixCLM_apply {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (x : Vec n) :
    matrixCLM A x = A.mulVec x := rfl

theorem dot_transpose_mulVec {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (u : Vec r) (v : Vec n) : dot (Aᵀ.mulVec u) v = dot u (A.mulVec v) := by
  change (Aᵀ *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v)
  rw [dotProduct_mulVec, Matrix.mulVec_transpose]

theorem gradientFunctional_comp {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (g : Vec r) :
    (gradientFunctional g).comp (matrixCLM A) = gradientFunctional (Aᵀ.mulVec g) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, gradientFunctional_apply, matrixCLM_apply]
  exact (dot_transpose_mulVec A g v).symm

theorem compress_posDef {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) : (compress A H).PosDef := by
  simpa only [metricGram, Matrix.transpose_transpose, compress] using
    metricGram_posDef hH hA

theorem mul_lift {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) : A * lift A H = 1 := by
  unfold lift compress
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (compress_posDef A hA hH).det_pos.ne')

theorem mul_rightInverse {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) : A * rightInverse A = 1 := by
  have h := mul_lift A hA (H := 1) Matrix.PosDef.one
  simpa only [lift, compress, Matrix.one_mul, Matrix.mul_one, rightInverse] using h

/-- A right inverse descends actual differentiability through a surjective
linear image, using the affine section through the accepted point. -/
theorem hasGradient_descend {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (J : Matrix (Fin n) (Fin r) ℝ) (hAJ : A * J = 1)
    (F : Vec r → ℝ) (x g : Vec n)
    (hg : HasFDerivAt (fun z => F (A.mulVec z)) (gradientFunctional g) x) :
    HasFDerivAt F (gradientFunctional (Jᵀ.mulVec g)) (A.mulVec x) := by
  let σ : Vec r → Vec n := fun z => x + J.mulVec (z - A.mulVec x)
  have hσ : HasFDerivAt σ (matrixCLM J) (A.mulVec x) := by
    have h := (((matrixCLM J).hasFDerivAt).comp (A.mulVec x)
      ((hasFDerivAt_id (𝕜 := ℝ) (A.mulVec x)).sub_const (A.mulVec x))).const_add x
    simpa only [sub_self, ContinuousLinearMap.comp_id, matrixCLM_apply] using h
  have hσx : σ (A.mulVec x) = x := by simp [σ]
  have heq : (fun z => F (A.mulVec (σ z))) = F := by
    funext z
    congr 1
    dsimp only [σ]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hAJ, Matrix.one_mulVec]
    abel
  have hg' : HasFDerivAt (fun z => F (A.mulVec z)) (gradientFunctional g)
      (σ (A.mulVec x)) := by simpa only [hσx] using hg
  have h := hg'.comp (A.mulVec x) hσ
  rw [gradientFunctional_comp] at h
  simpa only [Function.comp_def, heq] using h

/-- Forward chain rule, retaining the actual transpose action on gradients. -/
theorem hasGradient_comp {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (F : Vec r → ℝ) (x : Vec n) (g : Vec r)
    (hg : HasFDerivAt F (gradientFunctional g) (A.mulVec x)) :
    HasFDerivAt (fun z => F (A.mulVec z)) (gradientFunctional (Aᵀ.mulVec g)) x := by
  simpa only [gradientFunctional_comp, matrixCLM_apply, Function.comp_def] using
    hg.comp x ((matrixCLM A).hasFDerivAt (x := x))

theorem gradientFunctional_injective {n : ℕ} :
    Function.Injective (gradientFunctional (n := n)) := by
  intro g h he
  funext i
  have hi := congrArg (fun f : Vec n →L[ℝ] ℝ => f (Pi.single i 1)) he
  simp only [gradientFunctional_apply] at hi
  change dotProduct g (Pi.single i 1) = dotProduct h (Pi.single i 1) at hi
  simpa only [dotProduct_single_one] using hi

/-- Actual gradients of a factored objective lie in the transposed row space. -/
theorem gradient_in_image {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (J : Matrix (Fin n) (Fin r) ℝ) (hAJ : A * J = 1)
    (F : Vec r → ℝ) (x g : Vec n)
    (hg : HasFDerivAt (fun z => F (A.mulVec z)) (gradientFunctional g) x) :
    Aᵀ.mulVec (Jᵀ.mulVec g) = g := by
  exact gradientFunctional_injective
    ((hasGradient_comp A F x _ (hasGradient_descend A J hAJ F x g hg)).unique hg)

end AffineProjection
end BfgsVerification
