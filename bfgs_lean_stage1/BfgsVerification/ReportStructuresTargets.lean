import BfgsVerification.HomogeneousSourceConsequences
import BfgsVerification.MaxAffineBasin
import BfgsVerification.FivePieceObstruction
import BfgsVerification.PoweredGaugeProfiles
import BfgsVerification.ParabolicEnvelopeBreakpoints
import BfgsVerification.ParabolicExampleSourceIdentities
import BfgsVerification.ParabolicExampleScale
import BfgsVerification.QuadraticCellRadial
import BfgsVerification.AffineBarycentricLocal

/-! Exact source contracts for the sixth report milestone. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification

open MaxAffine.Family in
def MaxAffineThresholdTarget : Prop :=
  ∀ {n m : ℕ} (P : MaxAffine.Family n m) {ψ : Vec n → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hs : CenteredSmoothSublinear.LocallyC11On univ ψ) (star : Vec n)
    (hmin : ∀ x, ψ star+P.objective star ≤ ψ x+P.objective x)
    (hu : ∀ x, ψ x+P.objective x = ψ star+P.objective star → x=star)
    (R : AdmissibleBFGSRun n (fun x => ψ x+P.objective x)) (J : ℕ)
    (hstart : ((ψ (R.x J)+P.objective (R.x J) : ℝ) : EReal) <
      P.threshold (fun x => ψ x+P.objective x) star),
    Tendsto (fun k => ψ (R.x k)+P.objective (R.x k)) atTop (𝓝 (ψ star+P.objective star)) ∧
      Tendsto R.x atTop (𝓝 star)

open RadialPower in
def MixedLinearPowersTarget : Prop :=
  ∀ {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (γ : ∀ j, Vec (m j) → ℝ)
    (hγ : ∀ j, ConvexOn ℝ univ (γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (γ j))
    (hn : ∀ j x, 0 ≤ γ j x) (A : ∀ j, Vec n →ₗ[ℝ] Vec (m j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hu : ∀ x, F x = F star → x = star) {U : Set (Vec n)} (hU : IsOpen U)
    (hstar : star ∈ U) (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ j, (γ j (A j (x-star)))^(p j)),
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star)

open Homogeneous in
def RecurrentLowRankTarget : Prop :=
  ∀ {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hrank : Module.finrank ℝ (Submodule.span ℝ (recurrentValues R.g)) ≤ 2)
    (L : ℝ) (hlim : Tendsto (fun k => finiteMaxLinear A hA (R.x k)) atTop (𝓝 L)),
    L = 0 ∧ ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ finiteMaxLinear A hA xstar = 0

open Homogeneous in
def RelativeInteriorClassTarget : Prop :=
  ∀ {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty),
    RelativeInteriorZero A ↔ (∀ x, 0 ≤ finiteMaxLinear A hA x) ∧
      ∃ S : Submodule ℝ (Vec n), ∀ x, finiteMaxLinear A hA x = 0 ↔ x ∈ S

open Parabolic.Family in
def ParabolicPruningTarget : Prop :=
  ∀ {m : ℕ} (P : Parabolic.Family m),
    (∀ x, P.prunedFamily.objective x = P.objective x) ∧
      StrictMono P.prunedFamily.b ∧ StrictMono (P.orderedBreakpoint P.prunedOrder) ∧
      (∀ i : {i : Fin P.prunedOrder.count // i.val+1 < P.prunedOrder.count},
        let l := P.prunedOrder.index i.val
        let r := P.prunedOrder.index ⟨i.val.val+1, i.property⟩
        P.ProfileActive l (P.breakpoint l r) ∧ P.ProfileActive r (P.breakpoint l r) ∧
        0 < P.profile l (P.breakpoint l r) ∧
        P.calibration r-P.calibration l = -(P.a r-P.a l)/(2*P.profile l (P.breakpoint l r)))

open Parabolic.Example TransportedCertificate in
def ParabolicPrintedFieldTarget : Prop :=
  ∀ {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1),
    ∃ B : BandCertificate objective K 0 c₁ c₂ η,
      ∀ x, B.W x = outer (sourceVector x) (sourceVector x)

open ConvexCellRadial in
def PolyhedralBasinTarget : Prop :=
  ∀ {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (V : ι → Set (Vec n)) (f : ι → Vec n → ℝ)
    (hV : ∀ i, IsOpen (V i))
    (hsmooth : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hpart : ∀ i, U ∩ polyhedron (a i) (b i) ⊆ V i)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ polyhedron (a i) (b i))
    (hrep : ∀ i x, x ∈ U → x ∈ polyhedron (a i) (b i) → F x = f i x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star),
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star)

open FivePieceObstruction in
def FivePieceObstructionTarget : Prop :=
  ∀ (K : Set (Vec 3)) (hK : K ∈ 𝓝 0),
    ∃ τ : ℝ, 0 < τ ∧ ray τ 0 ∈ K ∧ (initialMetric τ).PosDef ∧
      HasFDerivAt objective (gradientFunctional initialGradient) (ray τ 0) ∧
      ∀ α : ℝ, 0 < α → ∀ g : Vec 3,
        HasFDerivAt objective (gradientFunctional g) (ray τ α) →
        ¬ (objective (ray τ α) ≤ objective (ray τ 0) +
            (1/4)*dot initialGradient (bfgsStep (initialMetric τ) initialGradient α) ∧
           (1/2)*dot initialGradient (bfgsStep (initialMetric τ) initialGradient α) ≤
            dot g (bfgsStep (initialMetric τ) initialGradient α))

open ConvexCellRadial in
def SmoothPLQBasinTarget : Prop :=
  ∀ {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ polyhedron (a i) (b i))
    (hrep : ∀ i x, x ∈ U → x ∈ polyhedron (a i) (b i) →
      F x = ψ x+quadratic (Q i) (c i) (d i) x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star),
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star)

end BfgsVerification
