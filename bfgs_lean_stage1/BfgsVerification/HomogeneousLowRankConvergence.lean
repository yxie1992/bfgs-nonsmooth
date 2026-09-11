import BfgsVerification.HomogeneousLowRankProjection
import BfgsVerification.HomogeneousLowRankRestriction

/-! End-to-end H.7.4 in actual recurrent effective dimension at most two.
The restricted tail is first proved to be an actual max-linear admissible run;
only that objective is then globally projected. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AdmissibleBFGSRun
open Homogeneous AffineProjection

/-- Full slope span dimension at most two suffices for the finite branch. -/
theorem maxLinear_span_le_two_zero_branch {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hrank : Module.finrank ℝ (Submodule.span ℝ (A : Set (Vec n))) ≤ 2)
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  obtain ⟨r, U, hr, hU, hspan⟩ := exists_slope_span_coordinates_exact A
  exact R.maxLinear_span_coordinates_le_two_convergence A hA U hU (hr ▸ hrank)
    (fun a ha => (hspan a).mp (Submodule.subset_span ha)) hv

/-- H.7.4's arbitrary-ambient-dimensional conclusion with exactly the actual
recurrent-span rank hypothesis. The discarded finite prefix and the recurrent
maximum are derived, and no global factorization of the original objective is
inferred from tail gradient membership. -/
theorem maxLinear_recurrent_span_le_two_zero_branch {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hrank : Module.finrank ℝ (Submodule.span ℝ (recurrentValues R.g)) ≤ 2)
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  obtain ⟨J, B, hB, hBrec, hBA, hg⟩ := R.exists_recurrent_slope_subset A hA
  let Q := restrictMaxLinear A B hA hB hBA (R.shift J) hg
  have hBrank : Module.finrank ℝ (Submodule.span ℝ (B : Set (Vec n))) ≤ 2 := by
    rwa [hBrec]
  have hvQ : Tendsto (fun k => finiteMaxLinear B hB (Q.x k)) atTop (𝓝 0) := by
    have hvJ : Tendsto (fun k => finiteMaxLinear A hA (R.x (J+k))) atTop (𝓝 0) := by
      simpa only [Nat.add_comm] using hv.comp (tendsto_add_atTop_nat J)
    apply hvJ.congr' (Eventually.of_forall (fun k => ?_))
    exact ((R.shift J).restrictMaxLinear_value A B hA hB hBA hg k).symm
  obtain ⟨xstar, hxQ, _⟩ := Q.maxLinear_span_le_two_zero_branch B hB hBrank hvQ
  have hx : Tendsto R.x atTop (𝓝 xstar) := by
    apply (tendsto_add_atTop_iff_nat J).mp
    change Tendsto (fun k => R.x (J+k)) atTop (𝓝 xstar) at hxQ
    simpa only [Nat.add_comm] using hxQ
  exact ⟨xstar, hx, tendsto_nhds_unique ((convex_continuous R.convex).tendsto _ |>.comp hx) hv⟩

/-- The finite limiting value in the planar source need not be assumed zero;
Module H.A derives that fact before H.7.4 is applied. -/
theorem maxLinear_planar_finite_value_has_limit (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (finiteMaxLinear A hA)) (L : ℝ)
    (hlim : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 L)) :
    L = 0 ∧ ∃ xstar : Vec 2, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  have hL := R.homogeneous_finite_value_limit_zero (finiteMaxLinear_homogeneous A hA) L hlim
  exact ⟨hL, R.maxLinear_planar_zero_branch_has_limit A hA (by simpa only [hL] using hlim)⟩

/-- A bound only along accepted planar values selects the convergent branch;
no compact sublevel or assumed finite value limit is needed. -/
theorem maxLinear_planar_lower_bound_has_limit (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (finiteMaxLinear A hA)) (L : ℝ)
    (hL : ∀ k, L ≤ finiteMaxLinear A hA (R.x k)) :
    ∃ xstar : Vec 2, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 :=
  R.maxLinear_planar_zero_branch_has_limit A hA
    (R.homogeneous_value_zero_of_lower_bound (finiteMaxLinear_homogeneous A hA) L hL)

/-- The source finite-limit recurrent-rank theorem has no assumed zero limit. -/
theorem maxLinear_recurrent_span_le_two_finite_value {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hrank : Module.finrank ℝ (Submodule.span ℝ (recurrentValues R.g)) ≤ 2)
    (L : ℝ) (hlim : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 L)) :
    L = 0 ∧ ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  have hL := R.homogeneous_finite_value_limit_zero (finiteMaxLinear_homogeneous A hA) L hlim
  exact ⟨hL, R.maxLinear_recurrent_span_le_two_zero_branch A hA hrank (by simpa only [hL] using hlim)⟩

/-- Actual recurrent effective rank at most two and a bound only on accepted
values derive an actual point limit in every ambient dimension. -/
theorem maxLinear_recurrent_span_le_two_lower_bound {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hrank : Module.finrank ℝ (Submodule.span ℝ (recurrentValues R.g)) ≤ 2)
    (L : ℝ) (hL : ∀ k, L ≤ finiteMaxLinear A hA (R.x k)) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 :=
  R.maxLinear_recurrent_span_le_two_zero_branch A hA hrank
    (R.homogeneous_value_zero_of_lower_bound (finiteMaxLinear_homogeneous A hA) L hL)

end AdmissibleBFGSRun
end BfgsVerification
