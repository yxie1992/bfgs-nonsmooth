import BfgsVerification.NuclearNormFacts
import BfgsVerification.PoweredGaugeProfiles

/-! R's actual arbitrary rectangular nuclear family and full-BFGS conclusions. -/
noncomputable section
open scoped BigOperators Topology Matrix.L2OpNorm
open Set Filter
namespace BfgsVerification.RectangularNuclear
variable {m n : ℕ}

def matrixLinear (m n : ℕ) : Vec (m*n) →ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun := CenteredSpectral.matrix
  map_add' := CenteredSpectral.matrix_add
  map_smul' := CenteredSpectral.matrix_smul

def objective {m n : ℕ} (x : Vec (m*n)) : ℝ :=
  nuclear (CenteredSpectral.matrix (m := m) (n := n) x)

def coordinateSeminorm (m n : ℕ) : Seminorm ℝ (Vec (m*n)) :=
  (nuclearSeminorm m n).comp (matrixLinear m n)

theorem coordinateSeminorm_apply (x : Vec (m*n)) : coordinateSeminorm m n x=objective x := rfl

theorem objective_singularValues (x : Vec (m*n)) :
    objective (m := m) (n := n) x = ∑ i : Fin n,
      Real.sqrt ((Matrix.isHermitian_transpose_mul_self
        (CenteredSpectral.matrix (m := m) (n := n) x)).eigenvalues i) := rfl

theorem objective_convex (m n : ℕ) : ConvexOn ℝ univ (objective (m := m) (n := n)) :=
  (coordinateSeminorm m n).convexOn

theorem objective_homogeneous (m n : ℕ) :
    Homogeneous.PositiveDegreeOne (objective (m := m) (n := n)) := by
  intro t ht x
  exact nuclear_smul_nonneg t ht (CenteredSpectral.matrix (m := m) (n := n) x)

theorem objective_zero (m n : ℕ) : objective (m := m) (n := n) 0=0 := nuclear_zero m n

theorem objective_nonneg (x : Vec (m*n)) : 0 ≤ objective (m := m) (n := n) x := nuclear_nonneg _

theorem objective_minimum (x : Vec (m*n)) :
    objective (m := m) (n := n) 0 ≤ objective (m := m) (n := n) x := by
  rw [objective_zero]
  exact objective_nonneg x

theorem objective_unique_zero (x : Vec (m*n)) (hx : objective (m := m) (n := n) x=0) : x=0 := by
  apply CenteredSpectral.matrix_injective (m := m) (n := n)
  exact (nuclear_eq_zero_iff _).mp hx

theorem objective_sublevel_compact (m n : ℕ) (b : ℝ) :
    IsCompact {x | objective (m := m) (n := n) x ≤ b} :=
  Localization.sublevel_compact (objective_convex m n) 0 objective_minimum
    (fun x hx => objective_unique_zero x (by simpa only [objective_zero] using hx)) b

/-- Actual full, unmodified BFGS with every admissible accepted-step selection
and arbitrary coupled SPD initialization, for every finite rectangular dimension. -/
theorem fullBFGS_convergence (R : AdmissibleBFGSRun (m*n) (objective (m := m) (n := n))) :
    Tendsto (fun k => objective (m := m) (n := n) (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  refine ⟨(R.homogeneous_bounded_below_convergence (objective_homogeneous m n) 0
    (fun x => objective_nonneg x)).2.2,?_⟩
  exact R.homogeneous_iterates_zero_of_bounded_zero_sublevel (objective_homogeneous m n)
    (objective_sublevel_compact m n 0).isBounded

theorem inward_error_zero {x g : Vec (m*n)}
    (hg : HasFDerivAt (objective (m := m) (n := n)) (gradientFunctional g) x)
    {t : ℝ} (ht : t ≤ 1) :
    RadialCertificate.supportingError (objective (m := m) (n := n)) x g
      (RadialCertificate.inwardPoint 0 x t)=0 := by
  simpa only [sub_zero] using RadialPower.degree_one_inward_error_zero (objective_convex m n)
    (objective_homogeneous m n) 0 (by simpa only [sub_zero] using hg) ht

theorem inward_bounds (m n : ℕ) (K : Set (Vec (m*n))) :
    RadialCertificate.HasInwardTaylorBounds (objective (m := m) (n := n)) K 0 := by
  intro η hη
  refine ⟨0,1/2,by norm_num,le_rfl,?_⟩
  intro x g hx hband hg t ht htmax
  rw [inward_error_zero hg (by linarith)]
  norm_num

theorem radial_bounds {K : Set (Vec (m*n))} (hK : IsCompact K) :
    RadialCertificate.HasRadialSecantBounds (objective (m := m) (n := n)) K 0 :=
  RadialCertificate.radial_of_inward_on_compact (objective_convex m n) hK 0 (inward_bounds m n K)

/-- BFGS's ordinary vector dot product is exactly the Frobenius matrix pairing. -/
theorem coordinate_pairing (x z : Vec (m*n)) :
    dot x z=pairing (CenteredSpectral.matrix (m := m) (n := n) x) (CenteredSpectral.matrix z) := by
  rw [CenteredSpectral.coordinate_pairing_frobenius,pairing_eq_sum,Finset.sum_comm]

/-- Differently powered, linearly composed rectangular nuclear penalties are
actual instances of the source mixed-gauge family, including singular maps. -/
theorem mixed_nuclear_powers_radial {d : ℕ} {ι : Type*} [Fintype ι]
    (rows cols : ι → ℕ) {F ψ : Vec d → ℝ} (hF : ConvexOn ℝ univ F)
    (A : ∀ j, Vec d →ₗ[ℝ] Vec (rows j*cols j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec d) {U K : Set (Vec d)}
    (hU : IsOpen U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j,
      (objective (m := rows j) (n := cols j) (A j (x-star)))^(p j)) :
    RadialCertificate.HasRadialSecantBounds F K star :=
  RadialPower.seminorm_mixed_powers_radial hF (fun j => coordinateSeminorm (rows j) (cols j))
    A p hp star hU hsmooth hK hKU hrep

/-- Full-BFGS convergence for actual finite sums of arbitrary rectangular
nuclear powers, with compactness only for the full objective's initial sublevel. -/
theorem mixed_nuclear_powers_convergence {d : ℕ} {ι : Type*} [Fintype ι]
    (rows cols : ι → ℕ) {F ψ : Vec d → ℝ} (R : AdmissibleBFGSRun d F)
    (A : ∀ j, Vec d →ₗ[ℝ] Vec (rows j*cols j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec d) (hmin : ∀ x, F star ≤ F x)
    {U : Set (Vec d)} (hU : IsOpen U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact R.initialSublevel) (hKU : R.initialSublevel ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j,
      (objective (m := rows j) (n := cols j) (A j (x-star)))^(p j)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) :=
  R.mixed_linear_powers_convergence (fun j => objective (m := rows j) (n := cols j))
    (fun j => objective_convex (rows j) (cols j))
    (fun j => objective_homogeneous (rows j) (cols j)) (fun j x => objective_nonneg x)
    A p hp star hmin hU hsmooth hK hKU hrep

end BfgsVerification.RectangularNuclear
