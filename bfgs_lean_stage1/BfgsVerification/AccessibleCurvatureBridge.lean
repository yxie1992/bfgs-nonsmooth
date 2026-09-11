import BfgsVerification.ModuleGGeometry

/-! Source G states vanishing accessible curvature. The accepted-pair Wolfe
inequality derives the small-decrease limit required by the generic bridge. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace AccessibleJumpGeometry
open TransportedCertificate

theorem eligible_decrease_tendsto_zero_of_curvature {n : ℕ} {ι : Type*} {l : Filter ι}
    {F : Vec n → ℝ} {c₁ c₂ : ℝ} (hc₂ : c₂ < 1) (x z g h : ι → Vec n)
    (hp : ∀ᶠ a in l, EligiblePair F c₁ c₂ (x a) (z a) (g a) (h a))
    (ht : Tendsto (fun a => pairCurvature (x a) (z a) (g a) (h a)) l (𝓝 0)) :
    Tendsto (fun a => pairDecrease (x a) (z a) (g a)) l (𝓝 0) := by
  apply squeeze_zero' (hp.mono fun a ha => ha.decrease_pos.le)
    (hp.mono fun a ha => (le_div_iff₀ (sub_pos.mpr hc₂)).mpr (by simpa only [mul_comm] using ha.curvature))
  simpa only [zero_div] using ht.div_const (1-c₂)

/-- The source's continuous-extension annihilation claim, deriving the
small-decrease condition from t→0 and the fixed weak-Wolfe constant. -/
theorem accessible_curvature_annihilated_of_continuousAt {n : ℕ} {ι : Type*}
    {l : Filter ι} [NeBot l] {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (hc₂ : c₂ < 1)
    (B : VisibilitySecantCertificate F K fstar c₁ c₂ η)
    (x z g h : ι → Vec n) (p jump : Vec n)
    (hp : ∀ᶠ a in l, x a ∈ positiveBand F K fstar η ∧ z a ∈ positiveBand F K fstar η ∧
      EligiblePair F c₁ c₂ (x a) (z a) (g a) (h a))
    (ht : Tendsto (fun a => pairCurvature (x a) (z a) (g a) (h a)) l (𝓝 0))
    (hy : Tendsto (fun a => h a-g a) l (𝓝 jump))
    (hz : Tendsto z l (𝓝 p)) (hc : ContinuousAt B.W p) : (B.W p).mulVec jump = 0 :=
  accessible_jump_annihilated_of_continuousAt B x z g h p jump hp
    (eligible_decrease_tendsto_zero_of_curvature hc₂ x z g h (hp.mono fun _ ha => ha.2.2) ht)
    ht hy hz hc

end AccessibleJumpGeometry
end BfgsVerification
