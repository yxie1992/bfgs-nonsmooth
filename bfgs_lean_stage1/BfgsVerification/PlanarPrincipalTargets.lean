import BfgsVerification.PlanarConvergence

/-! Exact original-objective targets for C's principal cluster theorem and
its affine-correctness and local-basin consequences. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification
open ClusterSetGeometry PlanarCornerCharts AffineCriticalObjective

def PlanarAffineCriticalClusterTarget : Prop :=
  ∀ {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {x : Vec 2 | F x≤b}) (hstart : F (R.x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p),
    ∃ p∈clusterSet R.x, F p≤b ∧ IsAffineCritical F p

def PlanarConvergenceTarget : Prop :=
  ∀ {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (b : ℝ)
    (hK : IsCompact {x : Vec 2 | F x≤b}) (hstart : F (R.x 0)≤b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y)
    (hregular : ∀ p : Vec 2, F p≤b → ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p)
    (hcorrect : ∀ p : Vec 2, F p≤b → AffineCorrectAt F p),
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ z, F z=F star → z=star) → Tendsto R.x atTop (𝓝 star))

def PlanarLocalBasinTarget : Prop :=
  ∀ {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 2) (hmin : ∀ z, F star≤F z) (hunique : ∀ z, F z=F star → z=star)
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) (hstar : star∈Ω)
    (hregular : ∀ p∈Ω, ¬IsAffineCritical F p →
      ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p)
    (hcorrect : ∀ p∈Ω, AffineCorrectAt F p) {b : ℝ} (hb : F star<b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {w | F w≤ℓ} → x=y),
    ∃ ε : ℝ, 0<ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0)<F star+ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

end BfgsVerification
