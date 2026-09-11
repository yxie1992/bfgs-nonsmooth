import BfgsVerification.ParabolicEnvelopeOrdered

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

theorem essential_witness_active {i : Fin m} (hi : P.Essential i) :
    ∃ ξ, P.ProfileActive i ξ ∧
      ∀ j, P.Canonical j → j ≠ i → P.profile j ξ < P.profile i ξ := by
  obtain ⟨ξ, hξ⟩ := hi.2
  refine ⟨ξ, ?_, hξ⟩
  intro j
  have he : P.profile (P.canonicalIndex j) ξ = P.profile j ξ := by
    simp only [profile, (P.canonicalIndex_coefficients j).1, (P.canonicalIndex_coefficients j).2]
  rw [← he]
  by_cases hc : P.canonicalIndex j = i
  · rw [hc]
  · exact (hξ _ (P.canonicalIndex_canonical j) hc).le

theorem essential_same_slope_maximal {i : Fin m} (hi : P.Essential i)
    (j : Fin m) (hb : P.b j = P.b i) : P.a j ≤ P.a i := by
  obtain ⟨ξ, hξ, _⟩ := P.essential_witness_active hi
  have h := hξ j
  dsimp [profile] at h
  rw [hb] at h
  linarith

theorem exists_essential_positive_slope : ∃ i, P.Essential i ∧ 0 < P.b i := by
  obtain ⟨j, hj⟩ := P.positive_slope
  have hp : 0 < P.objective ![(0 : ℝ), 1] := by
    have hb := P.branch_le j ![(0 : ℝ), 1]
    simpa [branch] using hj.trans_le (by simpa [branch] using hb)
  obtain ⟨i, hi, ha⟩ := P.exists_essential_active ![(0 : ℝ), 1]
  rw [ha] at hp
  exact ⟨i, hi, by simpa [branch] using hp⟩

theorem exists_essential_negative_slope : ∃ i, P.Essential i ∧ P.b i < 0 := by
  obtain ⟨j, hj⟩ := P.negative_slope
  have hp : 0 < P.objective ![(0 : ℝ), -1] := by
    have hb := P.branch_le j ![(0 : ℝ), -1]
    have hneg : 0 < -P.b j := neg_pos.mpr hj
    exact hneg.trans_le (by simpa [branch] using hb)
  obtain ⟨i, hi, ha⟩ := P.exists_essential_active ![(0 : ℝ), -1]
  rw [ha] at hp
  refine ⟨i, hi, ?_⟩
  have h : 0 < -P.b i := by simpa [branch] using hp
  linarith

/-- The actual strictly ordered, pruned family, derived for every original
family. Both extreme slope signs survive; no arbitrary nonzero-slope premise
is added, so an essential zero-slope branch remains allowed. -/
def prunedFamily : Family P.prunedOrder.count where
  a k := P.a (P.prunedOrder.index k)
  b k := P.b (P.prunedOrder.index k)
  a_pos k := P.a_pos _
  negative_slope := by
    obtain ⟨i, hi, hb⟩ := P.exists_essential_negative_slope
    obtain ⟨k, hk⟩ := P.prunedOrder.covers i hi
    exact ⟨k, by simpa only [hk] using hb⟩
  positive_slope := by
    obtain ⟨i, hi, hb⟩ := P.exists_essential_positive_slope
    obtain ⟨k, hk⟩ := P.prunedOrder.covers i hi
    exact ⟨k, by simpa only [hk] using hb⟩

theorem prunedFamily_slopes_strictMono : StrictMono P.prunedFamily.b :=
  P.prunedOrder.slopes_strictMono

theorem prunedFamily_branch (k : Fin P.prunedOrder.count) (x : Vec 2) :
    P.prunedFamily.branch k x = P.branch (P.prunedOrder.index k) x := rfl

theorem prunedFamily_objective (x : Vec 2) : P.prunedFamily.objective x = P.objective x := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    exact P.branch_le (P.prunedOrder.index k) x
  · obtain ⟨i, hi, ha⟩ := P.exists_essential_active x
    obtain ⟨k, hk⟩ := P.prunedOrder.covers i hi
    rw [ha, ← hk]
    exact P.prunedFamily.branch_le k x

theorem prunedFamily_gradient {x g : Vec 2}
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    HasFDerivAt P.prunedFamily.objective (gradientFunctional g) x := by
  have he : P.prunedFamily.objective = P.objective := funext P.prunedFamily_objective
  rw [he]
  exact hg

/-- Every retained branch has an actual nonempty open cell. In particular,
singleton/tie-only activity is not retained by the literal source pruning. -/
theorem essential_strict_interval {i : Fin m} (hi : P.Essential i) :
    ∃ ξ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ Ioo (ξ-δ) (ξ+δ),
      ∀ j, P.Canonical j → j ≠ i → P.profile j ζ < P.profile i ζ := by
  obtain ⟨ξ, hξ⟩ := hi.2
  have he : ∀ᶠ ζ in 𝓝 ξ, ∀ j, P.Canonical j → j ≠ i → P.profile j ζ < P.profile i ζ := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hc : P.Canonical j
    · by_cases hne : j ≠ i
      · have hev : ∀ᶠ ζ in 𝓝 ξ, P.profile j ζ < P.profile i ζ :=
          (isOpen_lt (P.profile_continuous j) (P.profile_continuous i)).mem_nhds (hξ j hc hne)
        exact hev.mono (fun ζ hζ _ _ => hζ)
      · exact Filter.Eventually.of_forall (fun _ _ h => (hne h).elim)
    · exact Filter.Eventually.of_forall (fun _ h _ => (hc h).elim)
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ξ, δ, hδ, ?_⟩
  intro ζ hζ
  apply hb
  rw [Metric.mem_ball, Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hζ.1], by linarith [hζ.2]⟩

end Family
end Parabolic
end BfgsVerification
