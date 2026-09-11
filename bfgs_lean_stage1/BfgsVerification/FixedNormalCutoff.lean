import BfgsVerification.FixedNormalRunBounds
import BfgsVerification.ClusterSetGeometry

/-! A Lipschitz cutoff separates a compact scalar set from any closed exceptional
set. Empty sets are handled explicitly; no number-of-interfaces assumption is used. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric

namespace BfgsVerification
namespace FixedNormal

def distanceCutoff (E : Set ℝ) (δ : ℝ) (t : ℝ) : ℝ :=
  min 1 (max 0 ((infDist t E - δ) / δ))

theorem distanceCutoff_bounds (E : Set ℝ) (δ t : ℝ) :
    0 ≤ distanceCutoff E δ t ∧ distanceCutoff E δ t ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem distanceCutoff_zero {E : Set ℝ} {δ t : ℝ} (hδ : 0 < δ)
    (ht : infDist t E ≤ δ) : distanceCutoff E δ t = 0 := by
  have hq : (infDist t E - δ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp [distanceCutoff, max_eq_left hq]

theorem distanceCutoff_one {E : Set ℝ} {δ t : ℝ} (hδ : 0 < δ)
    (ht : 2 * δ ≤ infDist t E) : distanceCutoff E δ t = 1 := by
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  exact (le_div_iff₀ hδ).mpr (by linarith)

theorem distanceCutoff_lipschitz {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith ⟨δ⁻¹, (inv_pos.mpr hδ).le⟩ (distanceCutoff E δ) := by
  have hl : LipschitzWith ⟨δ⁻¹, (inv_pos.mpr hδ).le⟩
      (fun t : ℝ => (infDist t E - δ) / δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hd := (lipschitz_infDist_pt E).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at hd
    calc
      dist ((infDist x E - δ) / δ) ((infDist y E - δ) / δ) =
          δ⁻¹ * dist (infDist x E) (infDist y E) := by
        rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div,
          abs_of_pos hδ, div_eq_inv_mul]
      _ ≤ δ⁻¹ * dist x y := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hδ.le)
  exact (hl.const_max 0).const_min 1

/-- A compact set disjoint from a closed exceptional set admits a scalar cutoff
which is one on the compact set and zero on a uniform strip around every
exceptional level. Both empty-set cases are included. -/
theorem exists_separating_cutoff {E Z : Set ℝ} (hE : IsClosed E) (hZ : IsCompact Z)
    (hdis : Disjoint Z E) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ≥0, ∃ τ : ℝ → ℝ,
      LipschitzWith L τ ∧ (∀ t, 0 ≤ τ t ∧ τ t ≤ 1) ∧
      (∀ t ∈ Z, τ t = 1) ∧
      (∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0) := by
  rcases E.eq_empty_or_nonempty with rfl | hEn
  · exact ⟨1, by norm_num, 0, fun _ => 1, LipschitzWith.const 1,
      fun _ => ⟨by norm_num, le_rfl⟩, fun _ _ => rfl, by simp⟩
  rcases Z.eq_empty_or_nonempty with rfl | hZn
  · exact ⟨1, by norm_num, 0, fun _ => 0, LipschitzWith.const 0,
      fun _ => ⟨le_rfl, by norm_num⟩, by simp, fun _ _ _ _ => rfl⟩
  obtain ⟨z, hz, hmin⟩ := hZ.exists_isMinOn hZn (continuous_infDist_pt E).continuousOn
  have hzE : z ∉ E := fun he => Set.disjoint_left.mp hdis hz he
  have hdpos : 0 < infDist z E := (hE.not_mem_iff_infDist_pos hEn).mp hzE
  let δ : ℝ := infDist z E / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ⟨δ⁻¹, (inv_pos.mpr hδ).le⟩, distanceCutoff E δ,
    distanceCutoff_lipschitz hδ, distanceCutoff_bounds E δ, ?_, ?_⟩
  · intro t ht
    apply distanceCutoff_one hδ
    have h := hmin ht
    change infDist z E ≤ infDist t E at h
    dsimp [δ]
    linarith
  · intro t e he hte
    apply distanceCutoff_zero hδ
    exact (infDist_le_dist_of_mem he).trans (by simpa only [Real.dist_eq] using hte)

end FixedNormal
end BfgsVerification
