import BfgsVerification.PoweredGaugeProfiles
import BfgsVerification.QuadraticCellRadial
import BfgsVerification.AffineProjection
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual affine Euclidean residuals, split according to their value at the
optimizer. All new development remains outside the frozen library. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.EuclideanResidual

def residual {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (x : Vec n) := A x-b

def centeredGauge {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star z : Vec n) : ℝ :=
  ∑ i, if residual (A i) (b i) star = 0 then ‖A i z‖ else 0

def smoothPart {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star x : Vec n) : ℝ :=
  ∑ i, if residual (A i) (b i) star = 0 then 0 else ‖residual (A i) (b i) x‖

theorem residual_contDiff {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) {N : WithTop ℕ∞} :
    ContDiff ℝ N (residual A b) := A.contDiff.sub contDiff_const

theorem centeredGauge_nonneg {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star z : Vec n) :
    0 ≤ centeredGauge A b star z := by
  unfold centeredGauge
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> positivity

theorem centeredGauge_homogeneous {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star : Vec n) :
    Homogeneous.PositiveDegreeOne (centeredGauge A b star) := by
  intro t ht z
  simp only [centeredGauge,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · rw [map_smul,norm_smul,Real.norm_of_nonneg ht]
  · simp

theorem centeredGauge_convex {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star : Vec n) :
    ConvexOn ℝ univ (centeredGauge A b star) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ α β hα hβ hsum
  simp only [centeredGauge,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · rw [map_add,map_smul,map_smul]
    calc
      ‖α • A i x+β • A i y‖ ≤ ‖α • A i x‖+‖β • A i y‖ := norm_add_le _ _
      _ = α*‖A i x‖+β*‖A i y‖ := by
        rw [norm_smul,norm_smul,Real.norm_of_nonneg hα,Real.norm_of_nonneg hβ]
  · simp

theorem exact_decomposition {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star x : Vec n) :
    (∑ i, ‖residual (A i) (b i) x‖) = smoothPart A b star x+centeredGauge A b star (x-star) := by
  simp only [smoothPart,centeredGauge,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with hz
  · have hs : A i star = b i := sub_eq_zero.mp hz
    simp only [zero_add,map_sub,hs,residual]
  · simp

theorem smooth_neighborhood {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (star : Vec n) :
    ∃ ε : ℝ, 0 < ε ∧ ContDiffOn ℝ 2 (smoothPart A b star) (Metric.ball star ε) := by
  have he (i : ι) : ∀ᶠ x in 𝓝 star,
      residual (A i) (b i) star ≠ 0 → residual (A i) (b i) x ≠ 0 := by
    by_cases hi : residual (A i) (b i) star = 0
    · exact Eventually.of_forall (fun _ h => (h hi).elim)
    · filter_upwards [((residual_contDiff (N := 0) (A i) (b i)).continuous.isOpen_preimage
        _ isOpen_ne).mem_nhds hi] with x hx
      exact fun _ => hx
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.mpr he)
  refine ⟨ε,hε,?_⟩
  unfold smoothPart
  apply ContDiffOn.sum
  intro i hi
  by_cases hz : residual (A i) (b i) star = 0
  · simpa only [if_pos hz] using (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : Vec n => (0 : ℝ)) _)
  · simp only [if_neg hz]
    apply (residual_contDiff (A i) (b i)).contDiffOn.norm ℝ
    intro x hx
    exact hball hx i hz

/-- Actual Euclidean affine residuals, including arbitrary overlaps and zero
optimal residuals, satisfy the local full-BFGS conclusion. The individual maps
need not be surjective, injective, or associated with disjoint coordinate groups. -/
theorem local_euclidean_residual_basin {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i)))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ i, ‖residual (A i) (b i) x‖)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ε,hε,hs⟩ := smooth_neighborhood A b star
  let W := U ∩ Metric.ball star ε
  have hW : IsOpen W := hU.inter Metric.isOpen_ball
  have hsW : star ∈ W := ⟨hsU,Metric.mem_ball_self hε⟩
  have hψW : CenteredSmoothSublinear.LocallyC11On W ψ :=
    ⟨hψ.1.mono inter_subset_left,hψ.2.mono inter_subset_left⟩
  have hsm : CenteredSmoothSublinear.LocallyC11On W (smoothPart A b star) :=
    ConvexCellRadial.contDiffOn_two_locallyC11 hW (hs.mono inter_subset_right)
  have hall := ConvexCellRadial.locallyC11_add hW hψW hsm
  have hr : ∀ x ∈ W, F x = (ψ x+smoothPart A b star x)+
      ∑ _i : Unit, (centeredGauge A b star ((LinearMap.id : Vec n →ₗ[ℝ] Vec n) (x-star)))^(1 : ℝ) := by
    intro x hx
    rw [hrep x hx.1,exact_decomposition A b star x]
    simp only [LinearMap.id_apply,Real.rpow_one,Finset.sum_const,Finset.card_univ,
      Fintype.card_unique,Nat.cast_one,one_smul]
    ring
  obtain ⟨δ,hδ,hbasin⟩ := RadialPower.local_mixed_linear_powers_basin (ι := Unit)
    hF (fun _ => centeredGauge A b star) (fun _ => centeredGauge_convex A b star)
    (fun _ => centeredGauge_homogeneous A b star) (fun _ => centeredGauge_nonneg A b star)
    (fun _ => LinearMap.id) (fun _ => 1) (fun _ => le_rfl) star hmin hu hW hsW hall hr
  refine ⟨δ,hδ,?_⟩
  intro R hstart
  have hb := hbasin R hstart
  exact ⟨fun k => (hb.1 k).1,hb.2⟩

/-- The source matrix A acting into the Euclidean, rather than Pi-normed,
coordinate space. The topology conversion is derived in finite dimension. -/
def matrixEuclideanCLM {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Vec n →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ((WithLp.linearEquiv 2 ℝ (Vec m)).symm.toContinuousLinearEquiv).toContinuousLinearMap.comp
    (AffineProjection.matrixCLM A)

theorem matrix_residual {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (x : Vec n) :
    residual (matrixEuclideanCLM A) (euclideanVector b) x = euclideanVector (A.mulVec x-b) := rfl

theorem local_matrix_euclidean_residual_basin {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (A : ∀ i, Matrix (Fin (m i)) (Fin n) ℝ) (b : ∀ i, Vec (m i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hrep : ∀ x ∈ U, F x = ψ x+∑ i, ‖euclideanVector ((A i).mulVec x-b i)‖)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  apply local_euclidean_residual_basin hF (fun i => matrixEuclideanCLM (A i))
    (fun i => euclideanVector (b i)) hU hsU hψ
  · simpa only [matrix_residual] using hrep
  · exact hmin
  · exact hu

end BfgsVerification.EuclideanResidual
