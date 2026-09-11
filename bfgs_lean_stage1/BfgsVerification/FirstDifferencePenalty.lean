import BfgsVerification.ScalarResidualFamilies

/-! Literal first-difference fused ℓ1 penalty and the source local-basin wrapper. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.FirstDifference

/-- The actual first-difference matrix has -1 on its diagonal and +1 immediately
above it; the length-one case has zero rows. -/
def differenceMatrix (n : ℕ) : Matrix (Fin n) (Fin (n+1)) ℝ :=
  fun i => Pi.single i.succ 1-Pi.single i.castSucc 1

theorem differenceMatrix_mulVec (n : ℕ) (x : Vec (n+1)) (i : Fin n) :
    (differenceMatrix n).mulVec x i=x i.succ-x i.castSucc := by
  change (Pi.single i.succ 1-Pi.single i.castSucc 1) ⬝ᵥ x = _
  rw [sub_dotProduct,single_dotProduct,single_dotProduct,one_mul,one_mul]

def penalty (n : ℕ) (weight : ℝ) (x : Vec (n+1)) : ℝ :=
  weight*∑ i : Fin n, |x i.succ-x i.castSucc|

def objective (n : ℕ) (weight : ℝ) (ψ : Vec (n+1) → ℝ) (x : Vec (n+1)) : ℝ :=
  ψ x+penalty n weight x

theorem penalty_matrix (n : ℕ) (weight : ℝ) (hweight : 0 ≤ weight) (x : Vec (n+1)) :
    penalty n weight x=∑ i : Fin n, |((weight • differenceMatrix n).mulVec x) i| := by
  simp only [penalty,Matrix.smul_mulVec_assoc,Pi.smul_apply,smul_eq_mul,
    differenceMatrix_mulVec,abs_mul,abs_of_nonneg hweight,Finset.mul_sum]

theorem penalty_translation_constant (n : ℕ) (weight t : ℝ) (x : Vec (n+1)) :
    penalty n weight (x+fun _ => t)=penalty n weight x := by
  simp only [penalty,Pi.add_apply,add_sub_add_right_eq_sub]

/-- This is an actual fused-penalty objective, at any unique minimizer. The
basin precedes every admissible full-BFGS run and no difference-matrix rank or
nonzero optimal residual premise is required. -/
theorem local_fullBFGS {n : ℕ} {weight : ℝ} (hweight : 0 ≤ weight) {ψ : Vec (n+1) → ℝ}
    (hF : ConvexOn ℝ univ (objective n weight ψ))
    {U : Set (Vec (n+1))} (hU : IsOpen U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ) {star : Vec (n+1)} (hs : star ∈ U)
    (hmin : ∀ x, objective n weight ψ star ≤ objective n weight ψ x)
    (hu : ∀ x, objective n weight ψ x=objective n weight ψ star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun (n+1) (objective n weight ψ),
      objective n weight ψ (R.x 0) ≤ objective n weight ψ star+δ →
      (∀ k, R.x k ∈ U) ∧
      Tendsto (fun k => objective n weight ψ (R.x k)) atTop (𝓝 (objective n weight ψ star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  apply AffineKinks.local_matrix_l1_basin hF (weight • differenceMatrix n) 0 hU hψ hs _ hmin hu
  intro x hx
  simp only [objective,penalty_matrix n weight hweight,sub_zero]

/-- A scalar residual vanishing at the optimizer becomes literally centered. -/
theorem centered_absolute_residual {n : ℕ} (a star z : Vec n) (b : ℝ)
    (h : dot a star-b=0) : |dot a (star+z)-b|=|dot a z| := by
  have he : dot a (star+z)=dot a star+dot a z := by
    change a ⬝ᵥ (star+z)=a ⬝ᵥ star+a ⬝ᵥ z
    exact dotProduct_add a star z
  rw [he]
  congr 1
  linarith

/-- A nonzero scalar residual has one fixed affine branch on an actual open
neighborhood of the optimizer. This is independent of all iteration sequences. -/
theorem nonzero_absolute_residual {n : ℕ} (a star : Vec n) (b : ℝ)
    (h : dot a star-b ≠ 0) :
    ∃ U : Set (Vec n), IsOpen U ∧ star ∈ U ∧ ∀ x ∈ U,
      |dot a x-b|=(if 0 < dot a star-b then 1 else -1)*(dot a x-b) := by
  have hc : Continuous (fun x : Vec n => dot a x-b) := by
    simpa only [gradientFunctional_apply] using
      ((gradientFunctional a).continuous.sub (continuous_const : Continuous (fun _ : Vec n => b)))
  rcases lt_or_gt_of_ne h with hn|hp
  · refine ⟨{x | dot a x-b<0},isOpen_lt hc continuous_const,hn,?_⟩
    intro x hx
    rw [if_neg (by linarith),neg_one_mul,abs_of_neg hx]
  · refine ⟨{x | 0<dot a x-b},isOpen_lt continuous_const hc,hp,?_⟩
    intro x hx
    rw [if_pos hp,one_mul,abs_of_pos hx]

end BfgsVerification.FirstDifference
