import BfgsVerification.HomogeneousDichotomy
import BfgsVerification.LocalizationCorollaries

/-! Bounded-below and coercive consequences of Module H.A. Coercivity here is
explicitly `Tendsto F (cocompact _) atTop`; no bounded-run hypothesis is imposed. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification
namespace Homogeneous

theorem nonneg_of_bounded_below {n : ℕ} {F : Vec n → ℝ} (hF : PositiveDegreeOne F)
    (L : ℝ) (hLower : ∀ x, L ≤ F x) (x : Vec n) : 0 ≤ F x := by
  by_contra hn
  have hx : F x < 0 := lt_of_not_ge hn
  have hL : L ≤ 0 := by simpa only [value_zero hF] using hLower 0
  let t := (L - 1) / F x
  have ht : 0 < t := div_pos_of_neg_of_neg (by linarith) hx
  have h := hLower (t • x)
  rw [hF t ht.le x] at h
  dsimp only [t] at h
  rw [div_mul_cancel₀ _ hx.ne] at h
  linarith

/-- A bounded zero sublevel of a homogeneous objective excludes every nonzero
point of nonpositive value. This is derived from the actual scalar ray. -/
theorem positive_of_bounded_zero_sublevel {n : ℕ} {F : Vec n → ℝ}
    (hF : PositiveDegreeOne F) (hb : Bornology.IsBounded {x | F x ≤ 0})
    {x : Vec n} (hx : x ≠ 0) : 0 < F x := by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_contra hn
  have hnonpos : F x ≤ 0 := le_of_not_gt hn
  let t := (|M| + 1) / ‖x‖
  have ht : 0 < t := div_pos (by positivity) hnx
  have hvalue : F (t • x) ≤ 0 := by
    rw [hF t ht.le x]
    exact mul_nonpos_of_nonneg_of_nonpos ht.le hnonpos
  have hnorm := hM (t • x) hvalue
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hnorm
  dsimp only [t] at hnorm
  rw [div_mul_cancel₀ _ hnx.ne'] at hnorm
  linarith [le_abs_self M]

/-- Coercivity supplies the bounded zero sublevel used by the ray argument. -/
theorem bounded_zero_sublevel_of_coercive {n : ℕ} {F : Vec n → ℝ}
    (hc : Tendsto F (cocompact (Vec n)) atTop) :
    Bornology.IsBounded {x | F x ≤ 0} := by
  have hev : {x | 0 < F x} ∈ cocompact (Vec n) := hc.eventually (eventually_gt_atTop 0)
  obtain ⟨K, hK, hsub⟩ := mem_cocompact'.mp hev
  apply hK.isBounded.subset
  intro x hx
  apply hsub
  simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] using hx

end Homogeneous

namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Source H.A's bounded-below objective consequence, with its minimum value explicit. -/
theorem homogeneous_bounded_below_convergence (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hLower : ∀ x, L ≤ F x) :
    (∀ x, F 0 ≤ F x) ∧ F 0 = 0 ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 0) := by
  refine ⟨?_, Homogeneous.value_zero hF, R.homogeneous_value_zero_of_lower_bound hF L
    (fun k => hLower (R.x k))⟩
  intro x
  rw [Homogeneous.value_zero hF]
  exact Homogeneous.nonneg_of_bounded_below hF L hLower x

/-- Bounded homogeneous sublevels imply actual point convergence to zero.
The bounded-zero-sublevel premise is weaker than requiring every sublevel bounded. -/
theorem homogeneous_iterates_zero_of_bounded_zero_sublevel
    (hF : Homogeneous.PositiveDegreeOne F)
    (hb : Bornology.IsBounded {x | F x ≤ 0}) : Tendsto R.x atTop (𝓝 0) := by
  classical
  have hpositive : ∀ x, x ≠ 0 → 0 < F x := fun _ hx =>
    Homogeneous.positive_of_bounded_zero_sublevel hF hb hx
  have hmin : ∀ x, F 0 ≤ F x := by
    intro x
    by_cases hx : x = 0
    · subst x
      exact le_rfl
    · rw [Homogeneous.value_zero hF]
      exact (hpositive x hx).le
  have huniq : ∀ x, F x = F 0 → x = 0 := by
    intro x he
    by_contra hx
    have hp := hpositive x hx
    rw [he, Homogeneous.value_zero hF] at hp
    exact lt_irrefl 0 hp
  have hvalues := R.homogeneous_value_zero_of_lower_bound hF 0
    (fun k => by simpa only [Homogeneous.value_zero hF] using hmin (R.x k))
  apply R.iterates_tendsto_unique_min_of_values 0 hmin huniq
  simpa only [Homogeneous.value_zero hF] using hvalues

/-- Source H.A's coercive case, expressed by the usual infinity limit. -/
theorem homogeneous_coercive_iterates_zero (hF : Homogeneous.PositiveDegreeOne F)
    (hc : Tendsto F (cocompact (Vec n)) atTop) : Tendsto R.x atTop (𝓝 0) :=
  R.homogeneous_iterates_zero_of_bounded_zero_sublevel hF
    (Homogeneous.bounded_zero_sublevel_of_coercive hc)

end AdmissibleBFGSRun
end BfgsVerification
