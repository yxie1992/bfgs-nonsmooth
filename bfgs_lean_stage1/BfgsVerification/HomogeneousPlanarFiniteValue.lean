import BfgsVerification.HomogeneousBlockStitching

/-! H.7.4's actual planar finite-value branch. Opposing-gradient blocks have
uniform bounds because their first pairs belong to the actual finite alphabet. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace HomogeneousBlock

theorem opposite_inverse_multiplier {n : ℕ} (g h : Vec n) (hg : g ≠ 0)
    (κ : ℝ) (hκ : 0 < κ) (he : h = -κ • g) :
    |dot g g / dot g h| = 1/κ := by
  have hp : 0 < dot g g := by
    simpa only [metricEnergy, Matrix.one_mulVec] using metricEnergy_pos Matrix.PosDef.one hg
  have hd : dot g h = -κ * dot g g := by
    rw [he]
    exact dotProduct_smul _ _ _
  rw [hd]
  have hv : dot g g / (-κ * dot g g) = -(1/κ) := by field_simp; ring
  rw [hv, abs_neg, abs_of_pos (div_pos zero_lt_one hκ)]

end HomogeneousBlock
namespace AdmissibleBFGSRun
open Homogeneous HomogeneousBlock HomogeneousPlanar

/-- The convergence of independent anchors is uniform over all late accepted
independent transitions, without any enumeration or bounded-gap assumption. -/
theorem maxLinear_planar_anchor_small (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (finiteMaxLinear A hA))
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j, J ≤ j → pairDet (R.g j) (R.g (j+1)) ≠ 0 → ‖R.x (j+1)‖ < ε := by
  obtain ⟨C, _, hC⟩ := finite_pair_inverse_bound A
  obtain ⟨h1, h2⟩ := R.homogeneous_endpoint_pairings_tendsto_zero (finiteMaxLinear_homogeneous A hA) hv
  have ht : Tendsto (fun j => C*(|dot (R.g j) (R.x (j+1))|+|dot (R.g (j+1)) (R.x (j+1))|))
      atTop (𝓝 0) := by simpa using (h1.abs.add h2.abs).const_mul C
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  exact ⟨J, fun j hj hd => (hC _ (R.maxLinear_gradient_mem A hA j) _
    (R.maxLinear_gradient_mem A hA (j+1)) _ hd).trans_lt (hJ j hj)⟩

/-- Every pair of consecutive actual independent-transition endpoints controls
all intervening points by the same constant from the finite slope alphabet. -/
theorem maxLinear_planar_uniform_anchor_blocks (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (finiteMaxLinear A hA))
    (hp : ∀ k, 0 < finiteMaxLinear A hA (R.x k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, a < b →
      pairDet (R.g a) (R.g (a+1)) ≠ 0 → pairDet (R.g b) (R.g (b+1)) ≠ 0 →
      (∀ j, a < j → j < b → ¬pairDet (R.g j) (R.g (j+1)) ≠ 0) →
      ∀ k, a ≤ k → k ≤ b → ‖R.x (k+1)‖ ≤ (1+C)*‖R.x (a+1)‖+C*‖R.x (b+1)‖ := by
  obtain ⟨C, hC, hpair⟩ := finite_pair_scalar_bound A
    (fun g h => (1+|dot g g / dot g h|)/R.c₁)
    (fun _ _ => div_nonneg (by positivity) R.c₁_pos.le)
  refine ⟨C, hC, ?_⟩
  intro a b hab _ _ hnone k hak hkb
  by_cases hadj : b = a+1
  · have hcases : k = a ∨ k = b := by omega
    rcases hcases with hka | hkbEq
    · rw [hka]
      nlinarith [norm_nonneg (R.x (a+1)), mul_nonneg hC (norm_nonneg (R.x (a+1))),
        mul_nonneg hC (norm_nonneg (R.x (b+1)))]
    · rw [hkbEq]
      have hC1 : 1 ≤ C := by
        have hh := hpair _ (R.maxLinear_gradient_mem A hA 0) _ (R.maxLinear_gradient_mem A hA 0)
        have hc1 := R.c₁_lt_c₂.trans R.c₂_lt_one
        have hh1 : 1 ≤ (1+|dot (R.g 0) (R.g 0)/dot (R.g 0) (R.g 0)|)/R.c₁ := by
          apply (le_div_iff₀ R.c₁_pos).mpr
          have hp0 := abs_nonneg (dot (R.g 0) (R.g 0)/dot (R.g 0) (R.g 0))
          linarith
        exact hh1.trans hh
      nlinarith [norm_nonneg (R.x (a+1)), norm_nonneg (R.x (b+1)),
        mul_nonneg hC (norm_nonneg (R.x (a+1))),
        mul_le_mul_of_nonneg_right hC1 (norm_nonneg (R.x (b+1)))]
  let Q := R.shift (a+1)
  let N := b-a-1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hd : ∀ j, j < N → pairDet (Q.g j) (Q.g (j+1)) = 0 := by
    intro j hj
    change pairDet (R.g (a+1+j)) (R.g (a+1+(j+1))) = 0
    have h := hnone (a+1+j) (by omega) (by dsimp [N] at hj; omega)
    simpa only [Nat.add_assoc] using not_ne_iff.mp h
  have hQp (j : ℕ) : 0 < finiteMaxLinear A hA (Q.x j) := hp (a+1+j)
  obtain ⟨κ, hκ, hκg⟩ := Q.homogeneous_dependent_transition_opposite
    (finiteMaxLinear_homogeneous A hA) hQp 0 (hd 0 (by omega))
  have hbound := Q.maxLinear_opposite_block_norm_bound A hA hQp N hN hd κ hκ hκg (k-a) (by dsimp [N]; omega)
  have hcoeff : (1+1/κ)/R.c₁ ≤ C := by
    have h := hpair _ (R.maxLinear_gradient_mem A hA (a+1)) _ (R.maxLinear_gradient_mem A hA (a+1+1))
    have hr := opposite_inverse_multiplier (Q.g 0) (Q.g 1) (Q.gradient_nonzero 0) κ hκ hκg
    change |dot (R.g (a+1+0)) (R.g (a+1+0))/dot (R.g (a+1+0)) (R.g (a+1+1))| = 1/κ at hr
    simpa only [Nat.add_zero, hr] using h
  have hxk : Q.x (k-a) = R.x (k+1) := by
    change R.x (a+1+(k-a)) = R.x (k+1)
    rw [show a+1+(k-a) = k+1 by omega]
  have hxb : Q.x (N+1) = R.x (b+1) := by
    change R.x (a+1+(N+1)) = R.x (b+1)
    rw [show a+1+(N+1) = b+1 by dsimp [N]; omega]
  have hxa : Q.x 0 = R.x (a+1) := by rfl
  change ‖Q.x (k-a)‖ ≤ (1+(1+1/κ)/R.c₁)*‖Q.x 0‖ + ((1+1/κ)/R.c₁)*‖Q.x (N+1)‖ at hbound
  rw [hxk, hxb, hxa] at hbound
  nlinarith [mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (R.x (a+1))),
    mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (R.x (b+1)))]

/-- H.7.4: every actual planar finite max-linear zero-value branch converges,
including bounded-below objectives with noncompact sublevels and opposing slopes. -/
theorem maxLinear_planar_zero_branch_has_limit (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (finiteMaxLinear A hA))
    (hv : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 0)) :
    ∃ xstar : Vec 2, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0 := by
  have hp := R.homogeneous_finite_branch_positive (finiteMaxLinear_homogeneous A hA) 0 hv
  by_cases hinf : ∀ K : ℕ, ∃ j, K ≤ j ∧ pairDet (R.g j) (R.g (j+1)) ≠ 0
  · obtain ⟨C, hC, hblock⟩ := R.maxLinear_planar_uniform_anchor_blocks A hA hp
    have hx : Tendsto R.x atTop (𝓝 0) := by
      apply (tendsto_add_atTop_iff_nat 1).mp
      exact tendsto_zero_of_anchor_blocks (fun k => R.x (k+1))
        (fun j => pairDet (R.g j) (R.g (j+1)) ≠ 0) hinf
        (R.maxLinear_planar_anchor_small A hA hv) C hC hblock
    exact ⟨0, hx, value_zero (finiteMaxLinear_homogeneous A hA)⟩
  · push_neg at hinf
    obtain ⟨J, hJ⟩ := hinf
    have hline (k : ℕ) : ∃ c : ℝ, R.g (J+k) = c • R.g J := by
      have h := (R.shift J).planar_dependent_prefix_line k (fun j _ => by
        change pairDet (R.g (J+j)) (R.g (J+(j+1))) = 0
        simpa only [Nat.add_assoc] using hJ (J+j) (Nat.le_add_right J j)) k le_rfl
      simpa only [shift, Nat.add_zero] using h
    have hx := R.maxLinear_fixed_line_tail_convergence A hA J (R.g J) (R.gradient_nonzero J) hline hv
    refine ⟨_, hx, ?_⟩
    exact tendsto_nhds_unique ((convex_continuous R.convex).tendsto _ |>.comp hx) hv

end AdmissibleBFGSRun
end BfgsVerification
