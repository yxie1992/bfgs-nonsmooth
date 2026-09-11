import BfgsVerification.SemialgebraicSmoothCover
import BfgsVerification.PlanarFiniteValueBasin

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry
open AffineCriticalObjective AffineSupportPath PlanarCornerCharts ConvexSubdifferential

/-- The actual finite critical-value conclusion for arbitrary finite-dimensional
finite convex semialgebraic objectives. The finite smooth graph cover is proved. -/
theorem semialgebraic_affine_critical_values {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F) :
    (F '' {x | IsAffineCritical F x}).Finite := by
  obtain ⟨C,hC,hcover⟩ := semialgebraic_finite_smooth_cover (affineCriticalGraph_semialgebraic hSA)
  exact finite_critical_values_of_smooth_graph_cover hF C (fun T hT => (hC T hT).2) hcover

theorem semialgebraic_affine_critical_components {n : ℕ} {F : Vec n → ℝ}
    (hSA : IsSemialgebraicObjective F) :
    (connectedComponentIn {x | IsAffineCritical F x} '' {x | IsAffineCritical F x}).Finite ∧
      ∀ p, IsSemialgebraic (connectedComponentIn {x | IsAffineCritical F x} p) := by
  obtain ⟨C,hC,hcover⟩ := semialgebraic_finite_smooth_cover (affineCritical_set_semialgebraic hSA)
  exact finite_semialgebraic_components_of_smooth_cover C hC hcover

theorem semialgebraic_affine_critical_component_constant {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F) {x p q : Vec n}
    (hp : p ∈ connectedComponentIn {z | IsAffineCritical F z} x)
    (hq : q ∈ connectedComponentIn {z | IsAffineCritical F z} x) : F p = F q :=
  objective_eq_on_affineCritical_component_of_finite_values hF
    (semialgebraic_affine_critical_values hF hSA) hp hq

/-- Module A's original low-level gap, with actual subdifferentials and affine
criticality. No finite-value, path, projection or decomposition premise remains. -/
theorem semialgebraic_low_affine_critical_gap {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p, F p < F star + ε →
      IsAffineCritical F p → (0 : Vec n) ∈ subdifferential F p :=
  low_level_affine_correct_of_finite_values (semialgebraic_affine_critical_values hF hSA) star hmin

/-- C's tame alternative on a compact structural sublevel. The same basin
works for every actual full-BFGS run and all its allowed algorithmic choices. -/
theorem semialgebraic_planar_low_basin {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F)
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
      ((∀ z, F z = F star → z = star) → Tendsto R.x atTop (𝓝 star)) :=
  planar_low_basin_of_finite_critical_values hF (semialgebraic_affine_critical_values hF hSA)
    star hmin hb hK hstrict hregular

/-- The local structural-neighborhood variant requires uniqueness to trap an
objective-only basin there; no optimal barycentric multiplier premise is added. -/
theorem semialgebraic_planar_local_basin {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F)
    (star : Vec 2) (hmin : ∀ z, F star ≤ F z) (hunique : ∀ z, F z = F star → z = star)
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) (hstar : star ∈ Ω)
    (hregular : ∀ p ∈ Ω, ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) {b : ℝ} (hb : F star < b)
    (hstrict : ∀ ℓ : ℝ, F star < ℓ → ℓ ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) :=
  planar_local_basin_of_finite_critical_values hF (semialgebraic_affine_critical_values hF hSA)
    star hmin hunique hΩ hstar hregular hb hstrict

end BfgsVerification.RealAlgebraicGeometry
