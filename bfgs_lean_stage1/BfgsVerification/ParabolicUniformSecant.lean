import BfgsVerification.ParabolicDenominator

/-! Uniform visibility and secant suppression for Q's parabolic direction.
Calibrated transport is a separate obligation, not assumed in these bounds. -/
noncomputable section
open scoped BigOperators Topology
open Set Matrix
namespace BfgsVerification
namespace Parabolic
namespace Family
open TransportedCertificate
variable {m : ℕ} (P : Family m)

theorem secant_coefficient_le (i j : Fin m) :
    4*(P.a i)^2/(P.a i+P.a j) ≤ 4*P.maxQuadratic := by
  apply (div_le_iff₀ (add_pos (P.a_pos i) (P.a_pos j))).mpr
  have h1 := mul_le_mul_of_nonneg_right (P.le_maxQuadratic i) (P.a_pos i).le
  have h2 := mul_nonneg P.maxQuadratic_pos.le (P.a_pos j).le
  nlinarith

/-- A single constant works on the whole compact set for every actual eligible
pair with d≤1, independent of branch adjacency or vanishing components. -/
theorem exists_uniform_secant_bound {K : Set (Vec 2)} (hK : IsCompact K)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ z ∈ K, ∀ g h : Vec 2,
      EligiblePair P.objective c₁ c₂ x z g h → pairDecrease x z g ≤ 1 →
      (dot (h-g) (radialDirection z))^2 ≤ C*pairCurvature x z g h := by
  obtain ⟨R, hR, hrad⟩ := compact_sqNorm_radius hK (0 : Vec 2)
  have hA := P.maxQuadratic_pos
  refine ⟨4*P.maxQuadratic*R^2+4, by positivity, ?_⟩
  intro x _hx z hz g h hp hd
  obtain ⟨i, hi, hgi⟩ := P.gradient_from_active hp.gradient_x
  obtain ⟨j, hj, hhj⟩ := P.gradient_from_active hp.gradient_z
  have he := (P.eligible_deficit_le hc₁ hi hp).trans hd
  have hzsq : (z 0)^2 ≤ R^2 := by
    have hcoord : (z 0)^2 ≤ sqNorm z :=
      Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ 0)
    exact hcoord.trans (by simpa only [sub_zero] using hrad z hz)
  have hterm : 4*(P.a i)^2/(P.a i+P.a j)*(z 0)^2 + 4*P.deficit i z ≤
      4*P.maxQuadratic*R^2+4 := by
    have hc := mul_le_mul_of_nonneg_right (P.secant_coefficient_le i j) (sq_nonneg (z 0))
    have hz := mul_le_mul_of_nonneg_left hzsq (show 0 ≤ 4*P.maxQuadratic by positivity)
    linarith
  have ht : 0 ≤ pairCurvature x z g h :=
    (mul_pos (sub_pos.mpr hc₂) hp.decrease_pos).le.trans hp.curvature
  have hs := P.secant_square_bound hi hj
  rw [← hgi, ← hhj] at hs
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left hterm ht])

theorem positive_visibility {x g : Vec 2} {η : ℝ} (hη : 0 ≤ η)
    (hx : η ≤ P.objective x) (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    4*η^2 ≤ (dot g (radialDirection x))^2 := by
  obtain ⟨i, hi, hgi⟩ := P.gradient_from_active hg
  rw [hgi, P.visibility_identity hi]
  nlinarith

end Family
end Parabolic
end BfgsVerification
