import BfgsVerification.SemialgebraicCriticalGeometry

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification
open RealAlgebraicGeometry AffineCriticalObjective ConvexSubdifferential PlanarCornerCharts

/-- Actual Module A geometry and its original low-level gap. All quantifiers
refer to the original objective and its actual supporting-vector set. -/
def SemialgebraicAffineCriticalTarget : Prop := ∀ {n : ℕ} (F : Vec n → ℝ),
    ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    IsSemialgebraic (supportGraph F) ∧ IsSemialgebraic {x | IsAffineCritical F x} ∧
    (connectedComponentIn {x | IsAffineCritical F x} '' {x | IsAffineCritical F x}).Finite ∧
    (∀ x, IsSemialgebraic (connectedComponentIn {z | IsAffineCritical F z} x)) ∧
    (∀ x p q : Vec n, p ∈ connectedComponentIn {z | IsAffineCritical F z} x →
      q ∈ connectedComponentIn {z | IsAffineCritical F z} x → F p = F q) ∧
    (F '' {x | IsAffineCritical F x}).Finite ∧
    ∀ star : Vec n, (∀ x, F star ≤ F x) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ p, F p < F star + ε →
        IsAffineCritical F p → (0 : Vec n) ∈ subdifferential F p

theorem semialgebraicAffineCritical : SemialgebraicAffineCriticalTarget := by
  intro n F hF hSA
  have hc := semialgebraic_affine_critical_components hSA
  exact ⟨supportGraph_semialgebraic hSA,affineCritical_set_semialgebraic hSA,hc.1,hc.2,
    fun _ _ _ hp hq => semialgebraic_affine_critical_component_constant hF hSA hp hq,
    semialgebraic_affine_critical_values hF hSA,semialgebraic_low_affine_critical_gap hF hSA⟩

def SemialgebraicPlanarBasinTarget : Prop := ∀ {F : Vec 2 → ℝ},
    ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    ∀ (star : Vec 2), (∀ z, F star ≤ F z) → ∀ {b : ℝ}, F star < b →
    IsCompact {x : Vec 2 | F x ≤ b} →
    (∀ ℓ : ℝ, F star < ℓ → ℓ ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y) →
    (∀ p : Vec 2, F p ≤ b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) ≤ F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ z, F z = F star → z = star) → Tendsto R.x atTop (𝓝 star))

theorem semialgebraicPlanarBasin : SemialgebraicPlanarBasinTarget := semialgebraic_planar_low_basin

def SemialgebraicPlanarLocalBasinTarget : Prop := ∀ {F : Vec 2 → ℝ},
    ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    ∀ (star : Vec 2), (∀ z, F star ≤ F z) → (∀ z, F z = F star → z = star) →
    ∀ {Ω : Set (Vec 2)}, IsOpen Ω → star ∈ Ω →
    (∀ p ∈ Ω, ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) →
    ∀ {b : ℝ}, F star < b →
    (∀ ℓ : ℝ, F star < ℓ → ℓ ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F star + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

theorem semialgebraicPlanarLocalBasin : SemialgebraicPlanarLocalBasinTarget :=
  semialgebraic_planar_local_basin

end BfgsVerification
