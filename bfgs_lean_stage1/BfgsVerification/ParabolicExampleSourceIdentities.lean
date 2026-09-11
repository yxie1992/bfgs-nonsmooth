import BfgsVerification.ParabolicExampleScale

/-! Literal strict acceptance and positive limiting value assertions printed
in Q's explicit example; these supplement the stronger separation theorem. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace Parabolic
namespace Example
open TransportedCertificate

theorem strict_armijo {u ρ ε c₁ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hs : ρ*ε < 3*u^2) (hc₁ : c₁*(1+ρ) < 1) :
    c₁*pairDecrease (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) <
      objective (oldPoint u ε)-objective (newPoint u ρ ε) := by
  obtain ⟨hx, hz⟩ := pair_values hρ hε hs
  rw [pair_decrease, hx, hz]
  nlinarith [mul_lt_mul_of_pos_right hc₁ hε]

theorem strict_weak_wolfe {u ρ ε c₂ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hc₂ : 0 < c₂) :
    c₂*dot (oldGradient u) (pairStep (oldPoint u ε) (newPoint u ρ ε)) <
      dot (newGradient u) (pairStep (oldPoint u ε) (newPoint u ρ ε)) := by
  have ho : dot (oldGradient u) (pairStep (oldPoint u ε) (newPoint u ρ ε)) = -(1+ρ)*ε := by
    have h := pair_decrease u ρ ε
    unfold pairDecrease at h
    linarith
  have hn : dot (newGradient u) (pairStep (oldPoint u ε) (newPoint u ρ ε)) = 0 := by
    simp [newGradient, pairStep, oldPoint, newPoint, dot, Fin.sum_univ_two]
  rw [ho, hn]
  nlinarith [mul_pos hc₂ (mul_pos (show 0 < 1+ρ by linarith) hε)]

theorem printed_strict_acceptance {u ε c₁ c₂ : ℝ} (hε : 0 < ε) (hs : ε < 6*u^2)
    (hc₁ : c₁ < 2/3) (hc₂ : 0 < c₂) :
    c₁*pairDecrease (oldPoint u ε) (newPoint u (1/2) ε) (oldGradient u) <
      objective (oldPoint u ε)-objective (newPoint u (1/2) ε) ∧
    c₂*dot (oldGradient u) (pairStep (oldPoint u ε) (newPoint u (1/2) ε)) <
      dot (newGradient u) (pairStep (oldPoint u ε) (newPoint u (1/2) ε)) :=
  ⟨strict_armijo (by norm_num) hε (by linarith) (by linarith),
    strict_weak_wolfe (by norm_num) hε hc₂⟩

theorem pair_values_tendsto (u ρ : ℝ) :
    Tendsto (fun ε => objective (oldPoint u ε)) (𝓝[>] 0) (𝓝 (3*u^2)) ∧
      Tendsto (fun ε => objective (newPoint u ρ ε)) (𝓝[>] 0) (𝓝 (3*u^2)) := by
  have hb : objective (oldPoint u 0) = 3*u^2 := by
    apply objective_middle_closed (by change -u^2 ≤ 2*u^2+0; nlinarith [sq_nonneg u])
      (by change 2*u^2+0 ≤ 2*u^2; linarith)
  have hc := family.objective_continuous.tendsto (oldPoint u 0)
  change Tendsto objective (𝓝 (oldPoint u 0)) (𝓝 (objective (oldPoint u 0))) at hc
  rw [hb] at hc
  constructor
  · simpa only [Function.comp_def, hb] using hc.comp (pair_points_tendsto u ρ).1
  · simpa only [Function.comp_def, hb] using hc.comp (pair_points_tendsto u ρ).2

end Example
end Parabolic
end BfgsVerification
