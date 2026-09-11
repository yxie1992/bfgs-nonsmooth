import BfgsVerification.ParameterDegreeRootPersistence

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Positive radii can be chosen uniformly over a finite family, while keeping
closed intervals about distinct centers disjoint. Empty families are allowed. -/
theorem finite_root_separating_radius (S : Finset ℝ) (γ : ℝ → ℝ)
    (hγ : ∀ b ∈ S, 0 < γ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ (∀ b ∈ S, δ < γ b) ∧
      ∀ b ∈ S, ∀ c ∈ S, b ≠ c → 2*δ < dist b c := by
  classical
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < ε :=
    (gt_mem_nhds hε).filter_mono nhdsWithin_le_nhds
  have hg : ∀ b : S, ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < γ b :=
    fun b => (gt_mem_nhds (hγ b b.2)).filter_mono nhdsWithin_le_nhds
  have hd : ∀ b c : S, ∀ᶠ δ : ℝ in 𝓝[>] 0, b ≠ c → 2*δ < dist (b : ℝ) c := by
    intro b c
    by_cases hbc : b=c
    · exact Filter.Eventually.of_forall (by simp [hbc])
    · have hpos : 2*(0 : ℝ) < dist (b : ℝ) c := by
        simpa using dist_pos.mpr (show (b : ℝ) ≠ c from fun h => hbc (Subtype.ext h))
      have hh := (continuous_const.mul continuous_id).continuousAt.eventually (gt_mem_nhds hpos)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono (fun δ hδ _ => hδ)
  have hallg : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ b : S, δ < γ b := Filter.eventually_all.mpr hg
  have halld : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ b c : S, b ≠ c → 2*δ < dist (b : ℝ) c :=
    Filter.eventually_all.mpr (fun b => Filter.eventually_all.mpr (hd b))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hδε,hδg,hδd⟩ := (hpos.and (he.and (hallg.and halld))).exists
  refine ⟨δ,hδ,hδε,(fun b hb => hδg ⟨b,hb⟩),?_⟩
  intro b hb c hc hbc
  exact hδd ⟨b,hb⟩ ⟨c,hc⟩ (fun h => hbc (congrArg Subtype.val h))

theorem rootWeightIn_mono (p : Polynomial ℝ) {I J : Set ℝ} (h : I ⊆ J) :
    rootWeightIn p I ≤ rootWeightIn p J := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro t ht
  obtain ⟨hr,htI⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hr,h htI⟩

theorem disjoint_closed_root_intervals {b c δ : ℝ} (h : 2*δ < dist b c) :
    Disjoint (Icc (b-δ) (b+δ)) (Icc (c-δ) (c+δ)) := by
  rw [Set.disjoint_left]
  intro t hb hc
  rcases le_total b c with hbc | hcb
  · have hd : dist b c = c-b := by rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hbc)]; ring
    rw [hd] at h
    linarith [hb.1,hb.2,hc.1,hc.2]
  · have hd : dist b c = b-c := by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hcb)]
    rw [hd] at h
    linarith [hb.1,hb.2,hc.1,hc.2]

end RealAlgebraicGeometry
end BfgsVerification
