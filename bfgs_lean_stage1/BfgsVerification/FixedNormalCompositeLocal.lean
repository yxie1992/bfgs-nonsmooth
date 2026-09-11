import BfgsVerification.FixedNormalCompositeConvergence

/-! The local composite basin, chosen before the actual full-BFGS run. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter
namespace BfgsVerification.FixedNormal

/-- A fixed positive range of strictly convex sublevels suffices for a common
local basin, independently of the SPD initialization and valid line search. -/
theorem local_tangential_composite_basin {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ z, F star ≤ F z)
    (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    (hψ : ConvexOn ℝ Ω ψ) (hsmooth : CenteredSmoothSublinear.LocallyC11On Ω ψ)
    (hh : ConvexOn ℝ univ h) (hhsm : ScalarLocallyC11On ({0} : Set ℝ)ᶜ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection a x)))
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (hplane : dot a star = b) {c : ℝ} (hc : F star < c)
    (hcontour : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ c → StrictConvex ℝ {x : Vec n | F x ≤ ℓ}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨η, hη, hsub⟩ := Localization.neighborhood_basin hF star hmin hunique (hΩ.mem_nhds hstar)
  refine ⟨min η (c - F star), lt_min hη (sub_pos.mpr hc), ?_⟩
  intro R hstart
  have hKΩ : R.initialSublevel ⊆ Ω := by
    intro x hx
    apply hsub
    have hm := min_le_left η (c - F star)
    change F x ≤ F star + η
    change F x ≤ F (R.x 0) at hx
    linarith
  have hstartc : F (R.x 0) ≤ c := by
    have hm := min_le_right η (c - F star)
    linarith
  exact R.tangential_composite_convergence hΩ
    (R.initialSublevel_compact_of_unique_minimizer star hmin hunique) hKΩ hψ hsmooth hh hhsm
    ha b hμ hstrong hrep star hmin hunique hplane
    (fun ℓ hℓ hl0 => hcontour ℓ hℓ (hl0.trans hstartc))

end BfgsVerification.FixedNormal
