import BfgsVerification.CenteredSecants
import BfgsVerification.LocalizationCorollaries
import BfgsVerification.CompactConvergence

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix

namespace BfgsVerification
namespace CenteredSmoothSublinear

/-- All constants in the centered correction estimate are derived from the
compact set and objective fields. Gradients at the two endpoints are actual
Fréchet derivatives; component differentiability is not an extra premise. -/
theorem exists_pair_correction_bound {n : ℕ} {F ψ γ : Vec n → ℝ}
    (star : Vec n) {U K : Set (Vec n)} (hU : IsOpen U)
    (hψ : ConvexOn ℝ U ψ) (hsmooth : LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L G R : ℝ, 0 < L ∧ 0 < G ∧ 0 < R ∧
      (∀ x ∈ K, ∀ y ∈ K,
        sqNorm (coordinateGradient ψ y - coordinateGradient ψ x) ≤
          L * dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x)) ∧
      (∀ x g, Homogeneous.Supports γ x g → sqNorm g ≤ G ^ 2) ∧
      (∀ x ∈ K, sqNorm (x - star) ≤ R ^ 2) ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ g g' : Vec n,
        HasFDerivAt F (gradientFunctional g) x →
        HasFDerivAt F (gradientFunctional g') y →
        0 < dot (g' - g) (y - x) →
        (dot (g' - g) (y - star)) ^ 2 / dot (g' - g) (y - x) ≤
          L * R ^ 2 + 2 * G * R := by
  obtain ⟨L, hL, hcoco⟩ := exists_cocoercivity_constant_on_compact hU hψ hsmooth hK hKU
  obtain ⟨G, hG, hgbound⟩ := Homogeneous.global_supporting_bound hγ hhom
  obtain ⟨R, hR, hrbound⟩ := compact_sqNorm_radius hK star
  refine ⟨L, G, R, hL, hG, hR, hcoco, hgbound, hrbound, ?_⟩
  intro x hx y hy g g' hg hg' ht
  let p := coordinateGradient ψ x
  let p' := coordinateGradient ψ y
  have hp : HasFDerivAt ψ (gradientFunctional p) x :=
    hasFDerivAt_coordinateGradient ((hsmooth.1 x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx)))
  have hp' : HasFDerivAt ψ (gradientFunctional p') y :=
    hasFDerivAt_coordinateGradient ((hsmooth.1 y (hKU hy)).differentiableAt (hU.mem_nhds (hKU hy)))
  have hs : Homogeneous.Supports γ (x - star) (g - p) := convex_supporting_inequality hγ
    (homogeneous_summand_derivative star hU hrep (hKU hx) hg hp)
  have hs' : Homogeneous.Supports γ (y - star) (g' - p') := convex_supporting_inequality hγ
    (homogeneous_summand_derivative star hU hrep (hKU hy) hg' hp')
  have hv := homogeneous_secant_pairing hhom hs hs'
  rw [show y - star - (x - star) = y - x by abel] at hv
  have hvn : sqNorm ((g' - p') - (g - p)) ≤ (2 * G) ^ 2 :=
    sqNorm_difference_le_four _ _ G (hgbound _ _ hs') (hgbound _ _ hs)
  have hsplit : (p' - p) + ((g' - p') - (g - p)) = g' - g := by abel
  have h := correction_le_of_split (p' - p) ((g' - p') - (g - p)) (y - star) (y - x)
    L G R hL hG.le hR.le (hcoco x hx y hy) hv hvn (hrbound y hy) (by rwa [hsplit])
  simpa only [hsplit] using h

end CenteredSmoothSublinear
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (A : AdmissibleBFGSRun n F)

/-- The actual full-BFGS correction obeys LR²+2GγR under the centered source
hypotheses. No matrix or iterate convergence is present in the hypotheses. -/
theorem centered_uniform_correction (star : Vec n) {ψ γ : Vec n → ℝ}
    {U : Set (Vec n)} (hU : IsOpen U) (hψ : ConvexOn ℝ U ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    (hK : IsCompact A.initialSublevel) (hKU : A.initialSublevel ⊆ U) :
    ∃ L G R : ℝ, 0 < L ∧ 0 < G ∧ 0 < R ∧
      ∀ k, A.referenceCorrection star k ≤ L * R ^ 2 + 2 * G * R := by
  obtain ⟨L, G, R, hL, hG, hR, _hcoco, _hgbound, _hrbound, hbound⟩ := CenteredSmoothSublinear.exists_pair_correction_bound
    star hU hψ hsmooth hγ hhom hrep hK hKU
  refine ⟨L, G, R, hL, hG, hR, ?_⟩
  intro k
  have hstep : A.displacement k = A.x (k + 1) - A.x k := by
    rw [A.step]
    simp only [add_sub_cancel_left, displacement]
  have hcur : dot (A.g (k + 1) - A.g k) (A.x (k + 1) - A.x k) = A.curvature k := by
    simp only [curvature, gradientChange, hstep]
  have h := hbound _ (A.iterate_mem_initialSublevel k) _ (A.iterate_mem_initialSublevel (k + 1))
    (A.g k) (A.g (k + 1)) (A.hasGradient k) (A.hasGradient (k + 1)) (by rw [hcur]; exact A.curvature_pos k)
  simpa only [referenceCorrection, gradientChange, hcur] using h

/-- Centered smooth-plus-sublinear objectives converge in value for every
admissible full-BFGS run on the compact initial sublevel, without uniqueness. -/
theorem centered_values (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    {ψ γ : Vec n → ℝ} {U : Set (Vec n)} (hU : IsOpen U) (hψ : ConvexOn ℝ U ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    (hK : IsCompact A.initialSublevel) (hKU : A.initialSublevel ⊆ U) :
    Tendsto (fun k => F (A.x k)) atTop (𝓝 (F star)) := by
  obtain ⟨L, G, R, hL, hG, hR, hbound⟩ :=
    A.centered_uniform_correction star hU hψ hsmooth hγ hhom hrep hK hKU
  let C := L * R ^ 2 + 2 * G * R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply A.compact_objective_tendsto_min_of_quadratic_corrections star hmin hK C
  exact Eventually.of_forall fun N => by
    calc
      (∑ k ∈ Finset.range N, A.referenceCorrection star k) ≤
          ∑ _k ∈ Finset.range N, C := Finset.sum_le_sum (fun k _ => hbound k)
      _ = C * (N : ℝ) := by simp [mul_comm]
      _ ≤ C * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by exact_mod_cast (show N ≤ N ^ 2 by simpa only [pow_two] using Nat.le_mul_self N)) hC

/-- With a unique minimizer the same source assumptions give iterate convergence. -/
theorem centered_iterates (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hunique : ∀ x, F x = F star → x = star)
    {ψ γ : Vec n → ℝ} {U : Set (Vec n)} (hU : IsOpen U) (hψ : ConvexOn ℝ U ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    (hK : IsCompact A.initialSublevel) (hKU : A.initialSublevel ⊆ U) :
    Tendsto A.x atTop (𝓝 star) :=
  A.iterates_tendsto_unique_min_of_values star hmin hunique
    (A.centered_values star hmin hU hψ hsmooth hγ hhom hrep hK hKU)

end AdmissibleBFGSRun
namespace CenteredSmoothSublinear

/-- A representation only on a neighborhood of a unique minimizer gives a
uniform positive basin before choosing the run or its initial SPD matrix. -/
theorem local_centered_basin {n : ℕ} {F ψ γ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hunique : ∀ x, F x = F star → x = star) {U : Set (Vec n)}
    (hU : IsOpen U) (hstar : star ∈ U) (hψ : ConvexOn ℝ U ψ)
    (hsmooth : LocallyC11On U ψ) (hγ : ConvexOn ℝ univ γ)
    (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : AdmissibleBFGSRun n F,
      F (A.x 0) ≤ F star + δ →
      (∀ k, A.x k ∈ U) ∧
      Tendsto (fun k => F (A.x k)) atTop (𝓝 (F star)) ∧ Tendsto A.x atTop (𝓝 star) := by
  obtain ⟨δ, hδ, hsub⟩ := Localization.neighborhood_basin hF star hmin hunique (hU.mem_nhds hstar)
  refine ⟨δ, hδ, ?_⟩
  intro A hstart
  have hK := A.initialSublevel_compact_of_unique_minimizer star hmin hunique
  have hKU : A.initialSublevel ⊆ U := fun x hx => hsub (hx.trans hstart)
  have hv := A.centered_values star hmin hU hψ hsmooth hγ hhom hrep hK hKU
  exact ⟨fun k => hKU (A.iterate_mem_initialSublevel k), hv,
    A.iterates_tendsto_unique_min_of_values star hmin hunique hv⟩

end CenteredSmoothSublinear
end BfgsVerification
