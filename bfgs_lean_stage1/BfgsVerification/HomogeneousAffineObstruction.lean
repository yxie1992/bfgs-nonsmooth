import BfgsVerification.HomogeneousAffineGeometry

/-! Module H.B: recurrent finite-gradient affine-hull obstruction.
The core matrix theorem uses neither homogeneity nor an objective. Objective
exports derive its budgets; finite max-linear exports derive their alphabet. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace FullBFGSRun

variable {n : ℕ} (R : FullBFGSRun n)

theorem gradient_ne_zero (k : ℕ) : R.g k ≠ 0 := by
  intro hz
  have hp := R.energy_pos k
  simp only [hz, metricEnergy, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hp
  exact lt_irrefl 0 hp

theorem inverse_energy_nonneg (v : Vec n) (k : ℕ) : 0 ≤ metricEnergy (R.H k)⁻¹ v := by
  simpa only [metricEnergy, dot, dotProduct, star_trivial] using
    (R.positive_definite k).inv.posSemidef.2 v

/-- The exact Hessian recurrence for the algebraic full-matrix run. -/
theorem inverse_update (k : ℕ) :
    (R.H (k + 1))⁻¹ = (R.H k)⁻¹ - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
      (dot (R.g (k + 1) - R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)))⁻¹ •
        outer (R.g (k + 1) - R.g k) (R.g (k + 1) - R.g k) := by
  rw [R.update k]
  exact hessianUpdate (R.positive_definite k) (R.gradient_ne_zero k) _
    (R.alpha_pos k) (R.curvature_pos k)

/-- A fixed normal with unit gradient pairing loses exactly 1/q energy. -/
theorem common_component_energy_step (v : Vec n) (k : ℕ)
    (hv : dot v (R.g k) = 1) (hw : dot v (R.g (k + 1)) = 1) :
    metricEnergy (R.H (k + 1))⁻¹ v = metricEnergy (R.H k)⁻¹ v - (R.q k)⁻¹ := by
  have hvg : dot (R.g k) v = 1 := (dotProduct_comm (R.g k) v).trans hv
  have hwy : dot (R.g (k + 1) - R.g k) v = 0 := by
    change (R.g (k + 1) - R.g k) ⬝ᵥ v = 0
    rw [sub_dotProduct, dotProduct_comm (R.g (k + 1)), dotProduct_comm (R.g k)]
    change dot v (R.g (k + 1)) - dot v (R.g k) = 0
    rw [hw, hv, sub_self]
  rw [R.inverse_update, EnergyIdentities.energy_add_matrix, EnergyIdentities.energy_sub_matrix,
    EnergyIdentities.energy_smul_matrix, EnergyIdentities.energy_smul_matrix,
    EnergyIdentities.energy_outer, EnergyIdentities.energy_outer, hvg, hwy]
  ring

/-- A tail common component bounds the actual reciprocal sum by its initial energy. -/
theorem common_component_tail_sum_le (v : Vec n) (J : ℕ)
    (hv : ∀ k, J ≤ k → dot v (R.g k) = 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, (R.q (J + i))⁻¹) ≤ metricEnergy (R.H J)⁻¹ v := by
  have htel : ∀ N, (∑ i ∈ Finset.range N, (R.q (J + i))⁻¹) =
      metricEnergy (R.H J)⁻¹ v - metricEnergy (R.H (J + N))⁻¹ v := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := R.common_component_energy_step v (J + M)
        (hv (J + M) (Nat.le_add_right J M))
        (hv (J + M + 1) (by omega))
      have hidx : J + (M + 1) = J + M + 1 := by omega
      rw [hidx, hstep]
      ring
  rw [htel N]
  linarith [R.inverse_energy_nonneg v (J + N)]

/-- The actual fixed-vector energy excludes common-component tails whenever the
proved reciprocal means diverge. This reusable stage exposes that one premise. -/
theorem common_component_incompatible (v : Vec n) (J : ℕ)
    (hv : ∀ k, J ≤ k → dot v (R.g k) = 1)
    (hmean : Tendsto (reciprocalMean R.q) atTop atTop) : False := by
  let D := (∑ k ∈ Finset.range J, (R.q k)⁻¹) + metricEnergy (R.H J)⁻¹ v
  have hD : 0 ≤ D := add_nonneg
    (Finset.sum_nonneg (fun k _ => inv_nonneg.mpr (R.energy_pos k).le))
    (R.inverse_energy_nonneg v J)
  obtain ⟨N, hN, hbig⟩ := ((eventually_ge_atTop (J + 1)).and
    (hmean.eventually (eventually_gt_atTop D))).exists
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNone : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hsum : (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤ D := by
    have heq : N = J + (N - J) := by omega
    rw [heq, ReciprocalGrowth.sum_prefix_tail]
    exact add_le_add_left (R.common_component_tail_sum_le v J hv (N - J)) _
  have hupper : reciprocalMean R.q N ≤ D := by
    unfold reciprocalMean
    apply (div_le_iff₀ hNpos).2
    exact hsum.trans (le_mul_of_one_le_right hD hNone)
  exact not_lt_of_ge hupper hbig

/-- H.3's algebraic conclusion from a finite gradient alphabet and vanishing d.
The reciprocal divergence premise is supplied by the actual full-BFGS theorem. -/
theorem zero_mem_recurrent_affineSpan (hfinite : (Set.range R.g).Finite)
    (c : ℝ) (hc : 0 < c) (hbeta : ∀ k, c ≤ R.beta k)
    (hd : Tendsto R.d atTop (𝓝 0)) :
    (0 : Vec n) ∈ affineSpan ℝ (Homogeneous.recurrentValues R.g) := by
  by_contra hn
  obtain ⟨v, hv⟩ := Homogeneous.common_component_of_zero_not_mem_affineSpan
    (Homogeneous.recurrentValues_nonempty R.g hfinite) hn
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (Homogeneous.eventually_mem_recurrentValues R.g hfinite)
  obtain ⟨G, hG, hg⟩ := Homogeneous.finite_range_sqNorm_bound R.g hfinite
  have hmean := (reciprocalGrowth n R G c hG hc hg hbeta hd).2
  exact R.common_component_incompatible v J (fun k hk => hv _ (hJ k hk)) hmean

end FullBFGSRun

namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Source H.3 for actual accepted objective runs; Armijo derives the budget. -/
theorem recurrent_affine_zero_of_lower_bound (hfinite : (Set.range R.g).Finite)
    (L : ℝ) (hLower : ∀ k, L ≤ F (R.x k)) :
    (0 : Vec n) ∈ affineSpan ℝ (Homogeneous.recurrentValues R.g) :=
  R.toFullBFGSRun.zero_mem_recurrent_affineSpan hfinite (1 - R.c₂)
    R.wolfe_constant_pos R.beta_lower_bound
    (R.predicted_decreases_tendsto_zero_of_lower_bound L hLower)

theorem recurrent_affine_zero_of_value_limit (hfinite : (Set.range R.g).Finite)
    (L : ℝ) (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) :
    (0 : Vec n) ∈ affineSpan ℝ (Homogeneous.recurrentValues R.g) :=
  R.recurrent_affine_zero_of_lower_bound hfinite L (R.objective_antitone.le_of_tendsto hlim)

/-- H.B for finite max-linear objectives: the gradient alphabet is derived. -/
theorem maxLinear_recurrent_affine_zero (A : Finset (Vec n)) (hA : A.Nonempty)
    (Q : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)) (L : ℝ)
    (hlim : Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (Q.x k)) atTop (𝓝 L)) :
    (0 : Vec n) ∈ affineSpan ℝ (Homogeneous.recurrentValues Q.g) :=
  Q.recurrent_affine_zero_of_value_limit (Q.maxLinear_gradient_range_finite A hA) L hlim

/-- The full-slope affine obstruction forces values to minus infinity. -/
theorem maxLinear_escape_of_zero_not_mem_affineSpan (A : Finset (Vec n)) (hA : A.Nonempty)
    (Q : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA))
    (hzero : (0 : Vec n) ∉ affineSpan ℝ (A : Set (Vec n))) :
    Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (Q.x k)) atTop atBot := by
  rcases Q.maxLinear_value_dichotomy A hA with hvalue | hescape
  · have hrec := maxLinear_recurrent_affine_zero A hA Q 0 hvalue
    apply False.elim
    apply hzero
    apply affineSpan_mono ℝ _ hrec
    intro g hg
    obtain ⟨k, rfl⟩ := Homogeneous.recurrentValues_subset_range Q.g hg
    exact Q.maxLinear_gradient_mem A hA k
  · exact hescape

/-- Any finite max-linear slope family with a fixed nonzero common component
forces objective escape. The slope count is arbitrary; finite termination is not asserted. -/
theorem maxLinear_common_component_escape (A : Finset (Vec n)) (hA : A.Nonempty)
    (Q : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA))
    (v : Vec n) (hv : ∀ a ∈ A, dot v a = 1) :
    Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (Q.x k)) atTop atBot := by
  rcases Q.maxLinear_value_dichotomy A hA with hvalue | hescape
  · obtain ⟨G, hG, hg⟩ := Q.homogeneous_global_gradient_bound (Homogeneous.finiteMaxLinear_homogeneous A hA)
    have hd := (Q.summable_predicted_decreases_of_value_limit 0 hvalue).tendsto_atTop_zero
    have hmean := (objectiveReciprocalGrowth n _ Q G hG hg hd).2
    exact False.elim (Q.toFullBFGSRun.common_component_incompatible v 0
      (fun k _ => hv _ (Q.maxLinear_gradient_mem A hA k)) hmean)
  · exact hescape

end AdmissibleBFGSRun
end BfgsVerification
