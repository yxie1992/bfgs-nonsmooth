import BfgsVerification.HomogeneousCommonTilt

/-! Module H.B's lower bound on the number of recurrent gradients. -/

noncomputable section
open scoped Topology
open Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- Affine zero makes the difference span contain the full linear span. -/
theorem span_le_vectorSpan_of_affine_zero {n : ℕ} {S : Set (Vec n)}
    (hzero : (0 : Vec n) ∈ affineSpan ℝ S) :
    Submodule.span ℝ S ≤ vectorSpan ℝ S := by
  apply Submodule.span_le.mpr
  intro x hx
  rw [← direction_affineSpan]
  simpa only [vsub_eq_sub, sub_zero] using
    (affineSpan ℝ S).vsub_mem_direction (subset_affineSpan ℝ S hx) hzero

/-- At least r+1 vectors are needed to span dimension r and affinely contain zero. -/
theorem finrank_span_add_one_le_ncard {n : ℕ} {S : Set (Vec n)}
    (hfinite : S.Finite) (hne : S.Nonempty)
    (hzero : (0 : Vec n) ∈ affineSpan ℝ S) :
    Module.finrank ℝ (Submodule.span ℝ S) + 1 ≤ S.ncard := by
  letI : Fintype S := hfinite.fintype
  letI : Nonempty S := hne.to_subtype
  have hdim := Submodule.finrank_mono (span_le_vectorSpan_of_affine_zero hzero)
  have hcard := finrank_vectorSpan_range_add_one_le ℝ (fun x : S => (x : Vec n))
  have hrange : Set.range (fun x : S => (x : Vec n)) = S := Subtype.range_coe
  rw [hrange] at hcard
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (Nat.add_le_add_right hdim 1).trans hcard

end Homogeneous
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- H.B's recurrent-alphabet cardinality corollary under the source lower bound. -/
theorem recurrent_gradient_cardinality_of_lower_bound
    (hfinite : (Set.range R.g).Finite) (L : ℝ) (hLower : ∀ k, L ≤ F (R.x k)) :
    Module.finrank ℝ (Submodule.span ℝ (Homogeneous.recurrentValues R.g)) + 1 ≤
      (Homogeneous.recurrentValues R.g).ncard :=
  Homogeneous.finrank_span_add_one_le_ncard
    (Homogeneous.recurrentValues_finite R.g hfinite)
    (Homogeneous.recurrentValues_nonempty R.g hfinite)
    (R.recurrent_affine_zero_of_lower_bound hfinite L hLower)

/-- The finite-value form used in the final H.B paragraph. -/
theorem recurrent_gradient_cardinality_of_value_limit
    (hfinite : (Set.range R.g).Finite) (L : ℝ)
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) :
    Module.finrank ℝ (Submodule.span ℝ (Homogeneous.recurrentValues R.g)) + 1 ≤
      (Homogeneous.recurrentValues R.g).ncard :=
  R.recurrent_gradient_cardinality_of_lower_bound hfinite L
    (R.objective_antitone.le_of_tendsto hlim)

/-- The finite-max specialization derives the alphabet from actual differentiability. -/
theorem maxLinear_recurrent_gradient_cardinality (A : Finset (Vec n)) (hA : A.Nonempty)
    (Q : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)) (L : ℝ)
    (hlim : Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (Q.x k)) atTop (𝓝 L)) :
    Module.finrank ℝ (Submodule.span ℝ (Homogeneous.recurrentValues Q.g)) + 1 ≤
      (Homogeneous.recurrentValues Q.g).ncard :=
  Q.recurrent_gradient_cardinality_of_value_limit (Q.maxLinear_gradient_range_finite A hA) L hlim

end AdmissibleBFGSRun
end BfgsVerification
