import BfgsVerification.HomogeneousRelativeInteriorBounds
import BfgsVerification.HomogeneousLowRankRestriction

/-! Full-slope and recurrent-tail H.8 convergence, with the actual initial/current
metric fiber formula. The recurrent restriction preserves accepted values only;
it is never asserted equal to the original objective globally. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AdmissibleBFGSRun
open Homogeneous AffineProjection

/-- H.8: full-slope relative interior gives convergence to the actual initial
metric projection onto the entire zero-value fiber, with uniqueness of that
metric minimizer. The formula depends only on the initial point and metric. -/
theorem maxLinear_relativeInterior_complete {n r : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hri : RelativeInteriorZero A) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hspan : ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x) :
    Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
    Tendsto R.x atTop (𝓝 (fiberPoint Uᵀ (R.H 0) (R.x 0) 0)) ∧
    finiteMaxLinear A hA (fiberPoint Uᵀ (R.H 0) (R.x 0) 0) = 0 ∧
    (∀ x, finiteMaxLinear A hA x = 0 ↔ Uᵀ.mulVec x = 0) ∧
    ∀ x, finiteMaxLinear A hA x = 0 →
      metricEnergy (R.H 0)⁻¹ (fiberPoint Uᵀ (R.H 0) (R.x 0) 0 - R.x 0) ≤
        metricEnergy (R.H 0)⁻¹ (x - R.x 0) ∧
      (metricEnergy (R.H 0)⁻¹ (x - R.x 0) =
        metricEnergy (R.H 0)⁻¹ (fiberPoint Uᵀ (R.H 0) (R.x 0) 0 - R.x 0) ↔
          x = fiberPoint Uᵀ (R.H 0) (R.x 0) 0) := by
  have hRank := orthonormal_transpose_fullRowRank U hU
  have hzero := relativeInterior_value_zero_iff_projection_zero A hA hri U hU hspan
  refine ⟨R.homogeneous_value_zero_of_lower_bound (finiteMaxLinear_homogeneous A hA) 0
    (fun k => relativeInteriorZero_nonneg A hA hri (R.x k)),
    (R.maxLinear_relativeInterior_convergence A hA hri U hU hspan).2,
    (hzero _).mpr (fiberPoint_in_fiber Uᵀ hRank R.initial_posDef (R.x 0) 0), hzero, ?_⟩
  intro x hx
  have hproj := (hzero x).mp hx
  exact ⟨fiberPoint_minimizes Uᵀ hRank R.initial_posDef (R.x 0) x 0 hproj,
    fiberPoint_minimizer_unique Uᵀ hRank R.initial_posDef (R.x 0) x 0 hproj⟩

/-- No coordinate representation is required as an input to the convergence
conclusion: an orthonormal representation is itself derived from the slope span. -/
theorem maxLinear_relativeInterior_has_limit {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hri : RelativeInteriorZero A) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  obtain ⟨r, U, hU, hspan⟩ := exists_slope_span_coordinates A
  have h := R.maxLinear_relativeInterior_complete A hA hri U hU hspan
  exact ⟨fiberPoint Uᵀ (R.H 0) (R.x 0) 0, h.2.1, h.2.2.1⟩

/-- H.8 on the actual recurrent slope set. The full accepted sequence converges
with the current-tail metric formula; the global original objective is not
identified with the recurrent maximum away from accepted points. -/
theorem maxLinear_recurrent_relativeInterior_convergence {n r : ℕ}
    (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hBrec : (B : Set (Vec n)) = recurrentValues R.g) (hri : RelativeInteriorZero B)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hspan : ∀ x, x ∈ Submodule.span ℝ (B : Set (Vec n)) ↔ ∃ z, U.mulVec z = x) :
    ∃ J : ℕ,
      Tendsto R.x atTop (𝓝 (fiberPoint Uᵀ (R.H J) (R.x J) 0)) ∧
      Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
      finiteMaxLinear A hA (fiberPoint Uᵀ (R.H J) (R.x J) 0) = 0 := by
  have hBA : B ⊆ A := by
    intro b hb
    have hbr : b ∈ recurrentValues R.g := by rw [← hBrec]; exact hb
    obtain ⟨k, rfl⟩ := recurrentValues_subset_range R.g hbr
    exact R.maxLinear_gradient_mem A hA k
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (eventually_mem_recurrentValues R.g (R.maxLinear_gradient_range_finite A hA))
  have hg (k : ℕ) : R.g (J+k) ∈ B := by
    change R.g (J+k) ∈ (B : Set (Vec n))
    rw [hBrec]
    exact hJ (J+k) (Nat.le_add_right J k)
  let Q := restrictMaxLinear A B hA hB hBA (R.shift J) hg
  have hQ := Q.maxLinear_relativeInterior_complete B hB hri U hU hspan
  have hpoint : Tendsto R.x atTop (𝓝 (fiberPoint Uᵀ (R.H J) (R.x J) 0)) := by
    apply (tendsto_add_atTop_iff_nat J).mp
    have h := hQ.2.1
    change Tendsto (fun k => R.x (J+k)) atTop (𝓝 (fiberPoint Uᵀ (R.H J) (R.x J) 0)) at h
    simpa only [Nat.add_comm] using h
  have hvalues : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat J).mp
    have he (k : ℕ) : finiteMaxLinear B hB (Q.x k) = finiteMaxLinear A hA (R.x (J+k)) :=
      (R.shift J).restrictMaxLinear_value A B hA hB hBA hg k
    have h := hQ.1.congr' (Eventually.of_forall he)
    simpa only [Nat.add_comm] using h
  refine ⟨J, hpoint, hvalues, ?_⟩
  exact tendsto_nhds_unique ((convex_continuous R.convex).tendsto _ |>.comp hpoint) hvalues

/-- The recurrent relative-interior criterion requires no coordinate matrix as
an extra hypothesis: the coordinates and the full original sequence limit are
both obtained from the actual recurrent slope set. -/
theorem maxLinear_recurrent_relativeInterior_has_limit {n : ℕ}
    (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hBrec : (B : Set (Vec n)) = recurrentValues R.g) (hri : RelativeInteriorZero B) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  obtain ⟨r, U, hU, hspan⟩ := exists_slope_span_coordinates B
  obtain ⟨J, hx, _, hf⟩ :=
    R.maxLinear_recurrent_relativeInterior_convergence A B hA hB hBrec hri U hU hspan
  exact ⟨fiberPoint Uᵀ (R.H J) (R.x J) 0, hx, hf⟩

end AdmissibleBFGSRun
end BfgsVerification
