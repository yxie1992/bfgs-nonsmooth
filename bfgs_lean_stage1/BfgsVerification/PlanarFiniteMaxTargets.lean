import BfgsVerification.PlanarMaxHessianBasin

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Metric Matrix
namespace BfgsVerification
open ConvexSubdifferential PlanarCornerCharts AffineCriticalObjective AffineBarycentric

def PlanarFiniteMaxLocalBasinTarget : Prop :=
  ∀ {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 2) (hmin : ∀ x, F star≤F x) (hunique : ∀ x, F x=F star → x=star)
    {m : ℕ} {f : Fin m → Vec 2 → ℝ} {U : Set (Vec 2)}
    (hU : IsOpen U) (hstar : star∈U) (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hrep : LocalFiniteMax F f star)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f star i)) star))
    (w : Vec (activeIndices F f star).card) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, w i=1)
    (hzero : ∑ i, w i • coordinateGradient (f (activeIndexMap F f star i)) star=0)
    {b : ℝ} (hb : F star<b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {z | F z≤ℓ} → x=y),

    ∃ ε : ℝ, 0<ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0)<F star+ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

theorem planarFiniteMaxLocalBasin : PlanarFiniteMaxLocalBasinTarget := @PlanarMaxRegular.finite_max_local_basin

def PlanarFiniteMaxHessianBasinTarget : Prop :=
  ∀ {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 2) (hmin : ∀ x, F star≤F x) (hunique : ∀ x, F x=F star → x=star)
    {m : ℕ} {f : Fin m → Vec 2 → ℝ} {U : Set (Vec 2)}
    (hU : IsOpen U) (hstar : star∈U) (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hrep : LocalFiniteMax F f star)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f star i)) star))
    (w : Vec (activeIndices F f star).card) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, w i=1)
    (hzero : ∑ i, w i • coordinateGradient (f (activeIndexMap F f star i)) star=0)
    {μ : ℝ} (hμ : 0<μ)
    (hh : ∀ i : Fin (activeIndices F f star).card, ∀ x∈U,
      (RadialHessian.matrix (f (activeIndexMap F f star i)) x-μ • (1 : Mat 2)).PosSemidef),

    ∃ ε : ℝ, 0<ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0)<F star+ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

theorem planarFiniteMaxHessianBasin : PlanarFiniteMaxHessianBasinTarget := @PlanarMaxRegular.finite_max_hessian_local_basin

end BfgsVerification
