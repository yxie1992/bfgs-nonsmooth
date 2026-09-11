import BfgsVerification.HomogeneousConsequences
import BfgsVerification.PoweredGaugeRadial
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
open scoped BigOperators Topology Matrix.L2OpNorm
open Set Filter
namespace BfgsVerification.CenteredSpectral

def matrix {m n : ℕ} (x : Vec (m*n)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => x (finProdFinEquiv (i,j))

def objective {m n : ℕ} (x : Vec (m*n)) : ℝ := ‖matrix (m := m) (n := n) x‖

/-- The norm is the actual Euclidean operator norm, not the default entrywise
matrix norm. This is the source spectral norm definition. -/
theorem objective_operator_norm {m n : ℕ} (x : Vec (m*n)) :
    objective (m := m) (n := n) x =
      ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (matrix (m := m) (n := n) x)‖ :=
  Matrix.l2_opNorm_def _

theorem matrix_add {m n : ℕ} (x z : Vec (m*n)) :
    matrix (m := m) (n := n) (x+z)=matrix x+matrix z := rfl

theorem matrix_smul {m n : ℕ} (t : ℝ) (x : Vec (m*n)) :
    matrix (m := m) (n := n) (t • x)=t • matrix x := rfl

theorem matrix_injective {m n : ℕ} : Function.Injective (matrix (m := m) (n := n)) := by
  intro x z h
  ext k
  let ij := (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).symm k
  have he := congrArg (fun A : Matrix (Fin m) (Fin n) ℝ => A ij.1 ij.2) h
  simpa only [matrix,Prod.mk.eta,ij,Equiv.apply_symm_apply] using he

theorem objective_convex (m n : ℕ) : ConvexOn ℝ univ (objective (m := m) (n := n)) := by
  refine ⟨convex_univ,?_⟩
  intro x _ z _ a b ha hb hab
  change ‖matrix (m := m) (n := n) (a • x+b • z)‖ ≤ a*‖matrix x‖+b*‖matrix z‖
  rw [matrix_add,matrix_smul,matrix_smul]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb])

theorem objective_homogeneous (m n : ℕ) : Homogeneous.PositiveDegreeOne (objective (m := m) (n := n)) := by
  intro t ht x
  simp only [objective,matrix_smul,norm_smul,Real.norm_of_nonneg ht]

theorem objective_zero (m n : ℕ) : objective (m := m) (n := n) 0=0 :=
  Homogeneous.value_zero (objective_homogeneous m n)

theorem objective_minimum {m n : ℕ} (x : Vec (m*n)) :
    objective (m := m) (n := n) 0 ≤ objective x := by
  rw [objective_zero]
  exact norm_nonneg _

theorem objective_unique_zero {m n : ℕ} (x : Vec (m*n)) (hx : objective (m := m) (n := n) x=0) : x=0 := by
  apply matrix_injective
  have hh : matrix (m := m) (n := n) x=0 := norm_eq_zero.mp hx
  exact hh

theorem objective_sublevel_compact (m n : ℕ) (b : ℝ) :
    IsCompact {x | objective (m := m) (n := n) x ≤ b} :=
  Localization.sublevel_compact (objective_convex m n) 0 objective_minimum
    (fun x hx => objective_unique_zero x (by simpa only [objective_zero] using hx)) b

/-- Every actual full-BFGS run for an arbitrary rectangular real spectral norm
centered at zero converges, with no singular-value simplicity assumption. -/
theorem fullBFGS_convergence {m n : ℕ} (R : AdmissibleBFGSRun (m*n) (objective (m := m) (n := n))) :
    Tendsto (fun k => objective (m := m) (n := n) (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  refine ⟨(R.homogeneous_bounded_below_convergence (objective_homogeneous m n) 0
    (fun x => norm_nonneg _)).2.2,?_⟩
  exact R.homogeneous_iterates_zero_of_bounded_zero_sublevel (objective_homogeneous m n)
    (objective_sublevel_compact m n 0).isBounded

theorem inward_error_zero {m n : ℕ} {x g : Vec (m*n)}
    (hg : HasFDerivAt (objective (m := m) (n := n)) (gradientFunctional g) x)
    {t : ℝ} (ht : t ≤ 1) :
    RadialCertificate.supportingError (objective (m := m) (n := n)) x g
      (RadialCertificate.inwardPoint 0 x t)=0 := by
  simpa only [sub_zero] using RadialPower.degree_one_inward_error_zero (objective_convex m n)
    (objective_homogeneous m n) 0 (by simpa only [sub_zero] using hg) ht

theorem matrix_surjective {m n : ℕ} : Function.Surjective (matrix (m := m) (n := n)) := by
  intro A
  refine ⟨fun k => A ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).symm k).1
    ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).symm k).2,?_⟩
  ext i j
  simp only [matrix,Equiv.symm_apply_apply]

/-- The ordinary BFGS coordinate pairing is exactly the matrix Frobenius pairing. -/
theorem coordinate_pairing_frobenius {m n : ℕ} (x z : Vec (m*n)) :
    dot x z=∑ i : Fin m, ∑ j : Fin n, matrix (m := m) (n := n) x i j*matrix z i j := by
  have he := (Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n))
    (fun k => x k*z k)).symm
  simpa only [dot,matrix,Fintype.sum_prod_type] using he

theorem inward_bounds (m n : ℕ) (K : Set (Vec (m*n))) :
    RadialCertificate.HasInwardTaylorBounds (objective (m := m) (n := n)) K 0 := by
  intro η hη
  refine ⟨0,1/2,by norm_num,le_rfl,?_⟩
  intro x g hx hband hg t ht htmax
  rw [inward_error_zero hg (by linarith)]
  norm_num

theorem radial_bounds {m n : ℕ} {K : Set (Vec (m*n))} (hK : IsCompact K) :
    RadialCertificate.HasRadialSecantBounds (objective (m := m) (n := n)) K 0 :=
  RadialCertificate.radial_of_inward_on_compact (objective_convex m n) hK 0 (inward_bounds m n K)

end BfgsVerification.CenteredSpectral
