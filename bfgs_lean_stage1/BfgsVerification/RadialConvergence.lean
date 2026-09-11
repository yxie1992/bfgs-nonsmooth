import BfgsVerification.RadialCertificate

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
open RadialCertificate

/-- RS on objective pairs bounds each actual reference correction on a positive
band. This is a consequence of the objective hypothesis, not an assumed budget. -/
theorem radial_correction_bound (star : Vec n) {K : Set (Vec n)}
    (hxK : ∀ k, R.x k ∈ K) (η C : ℝ)
    (hband : ∀ k, F star + η ≤ F (R.x k))
    (hRS : ∀ x z g h, x ∈ K → z ∈ K → F star + η ≤ F z → F z ≤ F x →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      0 < secantCurvature x z g h →
      (radialNumerator star z g h) ^ 2 ≤ C * secantCurvature x z g h) (k : ℕ) :
    R.referenceCorrection star k ≤ C := by
  have hstep : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    exact add_sub_cancel_left _ _
  have hcurv : secantCurvature (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1)) =
      R.curvature k := by
    unfold secantCurvature curvature gradientChange
    rw [hstep]
  have hpos : 0 < R.curvature k := R.curvature_pos k
  have h := hRS (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1))
    (hxK k) (hxK (k + 1)) (hband (k + 1))
    (R.objective_antitone (Nat.le_succ k)) (R.hasGradient k) (R.hasGradient (k + 1))
    (by rwa [hcurv])
  unfold referenceCorrection gradientChange
  apply (div_le_iff₀ hpos).2
  simpa only [radialNumerator, hcurv, mul_comm] using h

/-- A uniform linear correction bound implies the quadratic bound used by the
verified Module M criterion, with its constant sign handled explicitly. -/
theorem quadratic_corrections_of_uniform_bound (star : Vec n) (C : ℝ)
    (hcor : ∀ k, R.referenceCorrection star k ≤ C) (N : ℕ) :
    (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤ max C 0 * (N : ℝ) ^ 2 := by
  have hsum : (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤
      (N : ℝ) * max C 0 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, max C 0 :=
        Finset.sum_le_sum (fun k _ => (hcor k).trans (le_max_left C 0))
      _ = _ := by simp
  have hN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast (show N ≤ N ^ 2 by simpa only [pow_two] using Nat.le_mul_self N)
  nlinarith [mul_le_mul_of_nonneg_left hN (le_max_right C 0)]

/-- Positive-band radial secant bounds force optimal values for an actual full
BFGS run in a compact set. No iterate/matrix convergence or correction budget
is assumed: the correction bound is derived from RS in the positive-limit case. -/
theorem radial_certificate_values (K : Set (Vec n)) (hK : IsCompact K)
    (hxK : ∀ k, R.x k ∈ K) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hRS : HasRadialSecantBounds F K star) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) := by
  obtain ⟨ℓ, hlim⟩ := R.objective_value_limit_of_lower_bound (F star) (fun k => hmin _)
  have hfloor : F star ≤ ℓ := ge_of_tendsto (x := (atTop : Filter ℕ)) hlim (Eventually.of_forall (fun k => hmin (R.x k)))
  have hlevels : ∀ k, ℓ ≤ F (R.x k) := R.objective_antitone.le_of_tendsto hlim
  by_cases heq : ℓ = F star
  · simpa only [heq] using hlim
  · have hη : 0 < ℓ - F star := sub_pos.mpr (lt_of_le_of_ne hfloor (Ne.symm heq))
    obtain ⟨C, hC⟩ := hRS (ℓ - F star) hη
    have hcor := R.radial_correction_bound star hxK (ℓ - F star) C
      (fun k => by linarith [hlevels k]) hC
    obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_set K hK hxK
    exact R.objective_tendsto_min_of_quadratic_corrections star hmin G hG hg (max C 0)
      (Eventually.of_forall (R.quadratic_corrections_of_uniform_bound star C hcor))

/-- Compact-sublevel RS convergence including distance to all minimizers. -/
theorem radial_certificate_convergence_on_sublevel (b : ℝ)
    (hK : IsCompact {x : Vec n | F x ≤ b}) (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (hstart : F (R.x 0) ≤ b)
    (hRS : HasRadialSecantBounds F {x | F x ≤ b} star) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) := by
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} :=
    fun k => (R.objective_le_initial k).trans hstart
  have hv := R.radial_certificate_values _ hK hxK star hmin hRS
  exact ⟨hv, R.distance_to_argmin_of_values star hmin hK hxK hv,
    fun hu => R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

end AdmissibleBFGSRun
end BfgsVerification
