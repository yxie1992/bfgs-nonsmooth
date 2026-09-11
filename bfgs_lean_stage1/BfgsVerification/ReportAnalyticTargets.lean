import BfgsVerification.FiniteMaxSubdifferential
import BfgsVerification.FiniteMaxLocalCorrectness
import BfgsVerification.FiniteMaxRadialSufficiency
import BfgsVerification.EuclideanResidualRadial
import BfgsVerification.FiniteRayLineSearch
import BfgsVerification.UnexcitedMetric
import BfgsVerification.ParabolicRadialBoundary
import BfgsVerification.AlgebraicSeedRoot
import BfgsVerification.AffineRankLossObjective
import BfgsVerification.CellDerivativeMatching
import BfgsVerification.ClusterSetGeometry
import BfgsVerification.PlanarActiveGeometry
import BfgsVerification.PlanarTransportAlgebra
import BfgsVerification.ScalarTransportEnergy
import BfgsVerification.AlgebraicSeedJacobian
import BfgsVerification.NuclearRotatedPairs

/-! Exact source contracts for the seventh report milestone. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix
open BfgsVerification.RadialCertificate
namespace BfgsVerification

open ConvexSubdifferential in
def ActualFiniteMaxSubdifferentialTarget : Prop :=
  ∀ {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n}
    {x : Vec n} (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x),
  subdifferential F x = convexHull ℝ (g '' (activeIndices F f x : Set (Fin m)))

open ConvexSubdifferential in
def LocalAffineCorrectnessTarget : Prop :=
  ∀ {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ}
    (g : Vec n → Fin m → Vec n) (xstar : Vec n)
    (hrep : LocalFiniteMax F f xstar)
    (hg : ∀ᶠ p in 𝓝 xstar, ∀ i,
      HasFDerivAt (f i) (gradientFunctional (g p i)) p)
    (hc : ∀ i, ContinuousAt (fun p => g p i) xstar)
    (hind : AffineIndependent ℝ (fun i => g xstar (activeIndexMap F f xstar i)))
    (wstar : Vec (activeIndices F f xstar).card)
    (hpos : ∀ i, 0 < wstar i) (hsum : (∑ i, wstar i) = 1)
    (hzero : (∑ i, wstar i • g xstar (activeIndexMap F f xstar i)) = 0),
  ∀ᶠ p in 𝓝 xstar,
      ((0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) ↔ ∀ z, F p ≤ F z)

open FiniteMaxRadial in
def FiniteMaxRadialBasinTarget : Prop :=
  ∀ {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne (fun i => f i w))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w-star) = (fderiv ℝ (f j) w) (w-star))
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star),
  ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star)

open EuclideanResidual in
def EuclideanResidualBasinTarget : Prop :=
  ∀ {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (A : ∀ i, Matrix (Fin (m i)) (Fin n) ℝ) (b : ∀ i, Vec (m i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ i, ‖euclideanVector ((A i).mulVec x-b i)‖)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star),
  ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star)

open FiniteRayLineSearch in
def FiniteRayStepTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t))
    (hbad : {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ F (x+bfgsStep H g t)}.Finite),
  ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α)

open UnexcitedMetric in
def UnexcitedMetricTarget : Prop :=
  ∀ (A v₀ ρ c₁ c₂ : ℝ) (hA : 0 < A) (hv : 0 < v₀)
    (hρ : 0 < ρ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (hr : ρ < (1-c₁)/(1+c₁)),
  let R := run A v₀ ρ c₁ c₂ hA hv hρ hc₁ hc hc₂ hr;
    Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.H atTop (𝓝 (diagonal A 0)) ∧
      (∀ k, R.H k 0 0 = A) ∧
      (∀ k, R.x k = ![0,(-ρ)^k*v₀])

open ParabolicRadialBoundary in
def ParabolicRadialBoundaryTarget : Prop :=
  ∀ {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)),
  (∀ R : AdmissibleBFGSRun 2 objective,
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ¬ HasRadialSecantBounds objective K 0

open AlgebraicSeed in
def AlgebraicSeedRootTarget : Prop :=
  ∃! x : Vec 2,
    (∀ i, |x i-AlgebraicSeed.center i| ≤ 1/(10:ℝ)^30) ∧
      264192*R (x 0) (x 1)*K (x 0) (x 1)-U (x 0) (x 1)*V (x 0) (x 1)*(U (x 0) (x 1)+129)=0 ∧
      16*V (x 0) (x 1)*T (x 0) (x 1)*K (x 0) (x 1)-R (x 0) (x 1)*U (x 0) (x 1)*Y (x 0) (x 1)=0

open AlgebraicSeed in
def AlgebraicSeedBoundsTarget : Prop :=
  ∀ {x : Vec 2} (hx : ‖x-AlgebraicSeed.center‖ ≤ radius),
  0 < U (x 0) (x 1) ∧ 0 < V (x 0) (x 1) ∧ 0 < R (x 0) (x 1) ∧
      0 < K (x 0) (x 1) ∧ 0 < T (x 0) (x 1) ∧ 0 < Y (x 0) (x 1) ∧
      0 < U (x 0) (x 1)+129 ∧
      (60/1000:ℝ) < ratio (x 0) (x 1) ∧ ratio (x 0) (x 1) < 61/1000

open AffineRankLoss AffineCriticalObjective in
def AffineRankLossTarget : Prop :=
  (∀ x, AffineCorrectAt objective x) ∧ affineDistance 0=1 ∧
    (∀ t : ℝ, t ≠ 0 → affineDistance ![0,t]=2*|t|) ∧
    Tendsto (fun t : ℝ => affineDistance ![0,t]) (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun t : ℝ => objective ![0,t]-objective ![-1/2,0]) (𝓝[≠] 0) (𝓝 (1/4))

open AlgebraicSeed AffineProjection in
def AlgebraicJacobianCertificateTarget : Prop :=
  fderiv ℝ P AlgebraicSeed.center = matrixCLM AlgebraicSeed.J ∧ M=AlgebraicSeed.J⁻¹ ∧
    (matrixCLM M).comp (fderiv ℝ P AlgebraicSeed.center) = ContinuousLinearMap.id ℝ (Vec 2) ∧
    ‖M.mulVec (P AlgebraicSeed.center)‖ < 1/(10:ℝ)^50 ∧
    sSup ((fun z => ‖ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P z)‖) ''
      {z | ‖z-AlgebraicSeed.center‖ ≤ radius}) < 1/(10:ℝ)^26

def NuclearBoundaryTarget : Prop :=
  ∀ {K : Set (Vec 3)}, K ∈ 𝓝 NuclearSymmetric2.minimizer →
    ¬ HasRadialSecantBounds NuclearSymmetric2.objective K NuclearSymmetric2.minimizer

end BfgsVerification
