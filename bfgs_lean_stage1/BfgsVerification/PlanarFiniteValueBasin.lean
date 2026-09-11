import BfgsVerification.FiniteCriticalGraphValues
import BfgsVerification.PlanarConvergence

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry
open AffineCriticalObjective PlanarCornerCharts ConvexSubdifferential

/-- A finite actual critical-value set supplies the low basin uniformly before
the actual BFGS run. Uniqueness is needed only for the whole-iterate conclusion. -/
theorem planar_low_basin_of_finite_critical_values {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) (hfinite : (F '' {x | IsAffineCritical F x}).Finite)
    (star : Vec 2) (hmin : ∀ z, F star ≤ F z) {b : ℝ} (hb : F star < b)
    (hK : IsCompact {x : Vec 2 | F x ≤ b})
    (hstrict : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y)
    (hregular : ∀ p : Vec 2, F p ≤ b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) ≤ F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ z, F z = F star → z = star) → Tendsto R.x atTop (𝓝 star)) := by
  obtain ⟨δ,hδ,hgap⟩ := AffineSupportPath.low_level_affine_correct_of_finite_values hfinite star hmin
  let ε := min (δ/2) (b-F star)
  have hε : 0 < ε := lt_min (half_pos hδ) (sub_pos.mpr hb)
  have heδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have heb : F star + ε ≤ b := by
    have h := min_le_right (δ/2) (b-F star)
    dsimp [ε]
    linarith
  have hsub : {x : Vec 2 | F x ≤ F star + ε} ⊆ {x | F x ≤ b} :=
    fun _ hx => hx.trans heb
  have hsmall := hK.of_isClosed_subset
    (isClosed_le (convex_continuous hF) continuous_const) hsub
  refine ⟨ε,hε,?_⟩
  intro R hstart
  apply R.planar_convergence_on_sublevel star hmin (F star+ε) hsmall hstart
  · intro ℓ hℓ hl
    exact hstrict ℓ hℓ (hl.trans heb)
  · intro p hp
    exact hregular p (hp.trans heb)
  · intro p hp ha
    exact hgap p (lt_of_le_of_lt hp (add_lt_add_left heδ _)) ha

/-- Local structural data and uniqueness give an objective-only basin; actual
affine correctness is obtained from the finite values, not an added hypothesis. -/
theorem planar_local_basin_of_finite_critical_values {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) (hfinite : (F '' {x | IsAffineCritical F x}).Finite)
    (star : Vec 2) (hmin : ∀ z, F star ≤ F z) (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    (hregular : ∀ p ∈ Ω, ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) {b : ℝ} (hb : F star < b)
    (hstrict : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨δ,hδ,hgap⟩ := AffineSupportPath.low_level_affine_correct_of_finite_values hfinite star hmin
  let U := Ω ∩ {p : Vec 2 | F p < F star + δ}
  have hU : IsOpen U := hΩ.inter (isOpen_lt (convex_continuous hF) continuous_const)
  have hstarU : star ∈ U := ⟨hstar,by change F star < F star + δ; linarith⟩
  exact PlanarConvergence.local_convergence_basin hF star hmin hunique hU hstarU
    (fun p hp => hregular p hp.1) (fun p hp => hgap p hp.2) hb hstrict

end BfgsVerification.RealAlgebraicGeometry
