import BfgsVerification.HomogeneousPlanarEndpoints
import BfgsVerification.CompactConvergence

/-! Module H.C's complete unbounded-below planar dichotomy, including escape of
the actual Euclidean norm and the absence of stationary points. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

theorem unboundedBelow_iff_negative_value {n : ℕ} {F : Vec n → ℝ}
    (hh : PositiveDegreeOne F) :
    ¬ BddBelow (Set.range F) ↔ ∃ w, F w < 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h ⟨0, by rintro y ⟨x, rfl⟩; exact hn x⟩
  · rintro ⟨w, hw⟩ ⟨L, hL⟩
    exact (not_lt_of_ge (nonneg_of_bounded_below hh L (fun x => hL ⟨x, rfl⟩) w)) hw

/-- A globally unbounded-below convex objective has no stationary subgradient
at any point. This states the actual support inequality, not a chosen derivative. -/
theorem no_stationary_support_of_unboundedBelow {n : ℕ} {F : Vec n → ℝ}
    (hu : ¬ BddBelow (Set.range F)) (x : Vec n) : ¬ Supports F x 0 := by
  intro h
  apply hu
  refine ⟨F x, ?_⟩
  rintro y ⟨z, rfl⟩
  have hz := h z
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hz
  linarith

/-- Finite max-linear objectives obey a global absolute Euclidean linear bound,
with a constant constructed from their actual finite slope alphabet. -/
theorem finiteMaxLinear_abs_euclidean_bound {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |finiteMaxLinear A hA x| ≤ C * ‖euclideanVector x‖ := by
  let C := 1 + ∑ a ∈ A, Real.sqrt (sqNorm a)
  have hsum : 0 ≤ ∑ a ∈ A, Real.sqrt (sqNorm a) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro x
  obtain ⟨a, ha, he⟩ := finiteMaxLinear_active A hA x
  rw [he]
  have hn : ‖euclideanVector x‖ ^ 2 = sqNorm x :=
    FrameNorms.euclidean_norm_sq (euclideanVector x)
  have hbound := abs_dot_le_of_sqNorm_le a x (Real.sqrt (sqNorm a)) ‖euclideanVector x‖
    (Real.sqrt_nonneg _) (norm_nonneg _)
    (by rw [Real.sq_sqrt (sqNorm_nonneg a)]) (by rw [hn])
  have haC : Real.sqrt (sqNorm a) ≤ C := by
    have hs := Finset.single_le_sum (s := A) (f := fun a => Real.sqrt (sqNorm a))
      (fun _ _ => Real.sqrt_nonneg _) ha
    dsimp only [C]
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right haC (norm_nonneg _))

/-- Escape of objective values forces the actual Euclidean norm to infinity,
in arbitrary dimension. No convergence of directions is asserted. -/
theorem finiteMaxLinear_value_escape_norm {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (x : ℕ → Vec n) (hv : Tendsto (fun k => finiteMaxLinear A hA (x k)) atTop atBot) :
    Tendsto (fun k => ‖euclideanVector (x k)‖) atTop atTop := by
  obtain ⟨C, hC, hb⟩ := finiteMaxLinear_abs_euclidean_bound A hA
  have hneg : Tendsto (fun k => -finiteMaxLinear A hA (x k)) atTop atTop :=
    tendsto_neg_atTop_iff.mpr hv
  have hm : Tendsto (fun k => C * ‖euclideanVector (x k)‖) atTop atTop :=
    tendsto_atTop_mono (fun k => (neg_le_abs _).trans (hb (x k))) hneg
  exact (tendsto_const_mul_atTop_of_pos hC).mp hm

end Homogeneous
namespace AdmissibleBFGSRun

/-- Theorem H.C: an unbounded-below planar finite max-linear objective has
exactly the stated zero-limit or escaping behavior for every infinite admissible
full-BFGS run. No bounded-run or independent-transition premise is retained. -/
theorem maxLinear_planar_unbounded_dichotomy (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA))
    (hu : ¬ BddBelow (Set.range (Homogeneous.finiteMaxLinear A hA))) :
    (Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
      ∀ k, 0 < Homogeneous.finiteMaxLinear A hA (R.x k)) ∨
    (Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop atBot ∧
      Tendsto (fun k => ‖euclideanVector (R.x k)‖) atTop atTop) := by
  have hh := Homogeneous.finiteMaxLinear_homogeneous A hA
  obtain ⟨w, hw⟩ := (Homogeneous.unboundedBelow_iff_negative_value hh).mp hu
  rcases R.maxLinear_value_dichotomy A hA with hv | hv
  · exact Or.inl ⟨R.maxLinear_planar_zero_branch_iterates A hA w hw hv, hv,
      R.homogeneous_finite_branch_positive hh 0 hv⟩
  · exact Or.inr ⟨hv, Homogeneous.finiteMaxLinear_value_escape_norm A hA R.x hv⟩

/-- H.C with its mutually exclusive alternatives and nonstationarity clause
explicit. The first branch has strictly positive decreasing objective values. -/
theorem maxLinear_planar_unbounded_complete (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA))
    (hu : ¬ BddBelow (Set.range (Homogeneous.finiteMaxLinear A hA))) :
    (∀ x, ¬ Homogeneous.Supports (Homogeneous.finiteMaxLinear A hA) x 0) ∧
    Xor' (Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0 < Homogeneous.finiteMaxLinear A hA (R.x k)) ∧
      StrictAnti (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)))
    (Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop atBot ∧
      Tendsto (fun k => ‖euclideanVector (R.x k)‖) atTop atTop) := by
  refine ⟨Homogeneous.no_stationary_support_of_unboundedBelow hu, ?_⟩
  rcases R.maxLinear_planar_unbounded_dichotomy A hA hu with h | h
  · left
    refine ⟨⟨h.1, h.2.1, h.2.2, strictAnti_nat_of_succ_lt R.objective_strict_decrease⟩, ?_⟩
    intro he
    exact not_tendsto_atBot_of_tendsto_nhds h.2.1 he.1
  · right
    refine ⟨h, ?_⟩
    intro he
    exact not_tendsto_nhds_of_tendsto_atBot h.1 0 he.2.1

end AdmissibleBFGSRun
end BfgsVerification
