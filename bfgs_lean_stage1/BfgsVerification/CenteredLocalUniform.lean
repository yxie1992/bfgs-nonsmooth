import BfgsVerification.CenteredSmoothCalculus

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric

namespace BfgsVerification
namespace CenteredSmoothSublinear

/-- A finite family of positive radii has a positive common lower bound,
including an empty family. -/
theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ s, 0 < e i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun j hj => he j (Finset.mem_insert_of_mem hj))
    refine ⟨min (e i) δ, lt_min (he i (Finset.mem_insert_self _ _)) hδ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb j hj)

/-- Local Lipschitz continuity on an open neighborhood of a compact set gives
one radius and one constant on full balls centered at every point of that set. -/
theorem compact_uniform_local_lipschitz
    {E D : Type*} [PseudoMetricSpace E] [PseudoMetricSpace D]
    {U K : Set E} {f : E → D} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hf : LocallyLipschitzOn U f) :
    ∃ M : ℝ≥0, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K,
      ball x ρ ⊆ U ∧ LipschitzOnWith M f (ball x ρ) := by
  classical
  have hloc : ∀ x : K, ∃ M : ℝ≥0, ∃ e : ℝ, 0 < e ∧
      ball (x : E) (3 * e) ⊆ U ∧ LipschitzOnWith M f (ball (x : E) (3 * e)) := by
    intro x
    obtain ⟨M, V, hV, hMV⟩ := hf (hKU x.property)
    have hV' : V ∈ 𝓝 (x : E) := by
      simpa only [nhdsWithin_eq_nhds.mpr (hU.mem_nhds (hKU x.property))] using hV
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (inter_mem hV' (hU.mem_nhds (hKU x.property)))
    have hr3 : 3 * (r / 3) = r := by ring
    refine ⟨M, r / 3, by positivity, ?_, ?_⟩
    · intro z hz
      exact (hball (by simpa only [hr3] using hz)).2
    · apply hMV.mono
      intro z hz
      exact (hball (by simpa only [hr3] using hz)).1
  choose C e he hsub hLip using hloc
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => ball (x : E) (e x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (he ⟨x, hx⟩)⟩)
  obtain ⟨ρ, hρ, hρe⟩ := finite_positive_lower_bound s e (fun x _ => he x)
  refine ⟨s.sup C, ρ, hρ, ?_⟩
  intro x hx
  obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
  have hball : ball x ρ ⊆ ball (i : E) (3 * e i) := by
    intro z hz
    change dist z (i : E) < 3 * e i
    have htri := dist_triangle z x (i : E)
    have hz' := mem_ball.mp hz
    have hx' := mem_ball.mp hxi
    linarith [hρe i his, he i]
  exact ⟨hball.trans (hsub i), lipschitzOnWith_iff_restrict.mpr
    (((hLip i).mono hball).to_restrict.weaken (Finset.le_sup his))⟩

/-- The actual coordinate gradient is continuous wherever the derivative is
locally Lipschitz. -/
theorem continuousOn_coordinateGradient {n : ℕ} {U : Set (Vec n)} {ψ : Vec n → ℝ}
    (hψ : LocallyLipschitzOn U (fderiv ℝ ψ)) :
    ContinuousOn (coordinateGradient ψ) U := by
  apply continuousOn_pi.mpr
  intro i
  exact hψ.continuousOn.clm_apply continuousOn_const

/-- Compactness supplies one actual Euclidean bound for the smooth gradients. -/
theorem compact_coordinateGradient_bound {n : ℕ} {U K : Set (Vec n)} {ψ : Vec n → ℝ}
    (hψ : LocallyLipschitzOn U (fderiv ℝ ψ)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ G : ℝ, 0 < G ∧ ∀ x ∈ K, sqNorm (coordinateGradient ψ x) ≤ G ^ 2 := by
  have hc := continuous_sqNorm.continuousOn.comp
    (continuousOn_coordinateGradient hψ) (fun _ _ => mem_univ _)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hc.mono hKU)
  refine ⟨Real.sqrt (|M| + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro x hx
  rw [Real.sq_sqrt (by positivity)]
  exact (hM ⟨x, hx, rfl⟩).trans (by linarith [le_abs_self M])

end CenteredSmoothSublinear
end BfgsVerification
