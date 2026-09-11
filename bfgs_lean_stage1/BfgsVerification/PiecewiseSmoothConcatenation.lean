import BfgsVerification.PiecewiseSmoothPaths

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def joinedCurve (p q : ℝ → E) (t : ℝ) : E :=
  if t ≤ 1/2 then p (2*t) else q (2*t-1)

theorem joinedCurve_continuousOn {p q : ℝ → E}
    (hp : ContinuousOn p (Icc 0 1)) (hq : ContinuousOn q (Icc 0 1))
    (he : p 1 = q 0) : ContinuousOn (joinedCurve p q) (Icc 0 1) := by
  have hleft : ContinuousOn (fun t : ℝ => p (2*t)) (Icc 0 1 ∩ Iic (1/2)) := by
    apply hp.comp (continuous_const.mul continuous_id).continuousOn
    intro t ht
    have hth : t ≤ 1/2 := ht.2
    change 0 ≤ 2*t ∧ 2*t ≤ 1
    exact ⟨by linarith [ht.1.1], by linarith⟩
  have hright : ContinuousOn (fun t : ℝ => q (2*t-1)) (Icc 0 1 ∩ Ici (1/2)) := by
    apply hq.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
    intro t ht
    have hth : 1/2 ≤ t := ht.2
    change 0 ≤ 2*t-1 ∧ 2*t-1 ≤ 1
    exact ⟨by linarith, by linarith [ht.1.2]⟩
  apply ContinuousOn.if
  · intro t ht
    have ht' : t = 1/2 := by
      have hh := ht.2
      change t ∈ frontier (Iic (1/2 : ℝ)) at hh
      simpa only [frontier_Iic, mem_singleton_iff] using hh
    subst t
    norm_num
    exact he
  · simpa only [show {t : ℝ | t ≤ 1/2} = Iic (1/2) from rfl,
      isClosed_Iic.closure_eq] using hleft
  · simpa only [not_le, show {t : ℝ | 1/2 < t} = Ioi (1/2) from rfl,
      closure_Ioi] using hright

theorem PiecewiseSmoothPathIn.trans {S : Set E} {x y z : E}
    (hxy : PiecewiseSmoothPathIn S x y) (hyz : PiecewiseSmoothPathIn S y z) :
    PiecewiseSmoothPathIn S x z := by
  classical
  obtain ⟨p⟩ := hxy
  obtain ⟨q⟩ := hyz
  let B := insert (1/2 : ℝ) (p.exceptions.image (fun t => t/2) ∪
    q.exceptions.image (fun t => (t+1)/2))
  refine ⟨⟨joinedCurve p.curve q.curve,
    joinedCurve_continuousOn p.continuousOn q.continuousOn (p.target.trans q.source.symm),
    by simpa [joinedCurve] using p.source,
    by norm_num [joinedCurve]; exact q.target, ?_, B, ?_⟩⟩
  · intro t ht
    change (if t ≤ 1/2 then p.curve (2*t) else q.curve (2*t-1)) ∈ S
    split_ifs with h
    · exact p.mapsTo ⟨by linarith [ht.1], by linarith⟩
    · exact q.mapsTo ⟨by linarith, by linarith [ht.2]⟩
  · intro t ht hB
    have htne : t ≠ 1/2 := by
      intro he
      exact hB (he ▸ Finset.mem_insert_self _ _)
    rcases lt_or_gt_of_ne htne with hl | hr
    · have hpne : 2*t ∉ p.exceptions := by
        intro hpne
        apply hB
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨2*t, hpne, by ring⟩))
      have hpt := p.smoothAt (2*t) ⟨by linarith [ht.1], by linarith⟩ hpne
      have hc := hpt.comp t (contDiffAt_const.mul contDiffAt_id)
      apply hc.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hl] with u hu
      exact if_pos (show u ≤ 1/2 from hu.le)
    · have hqne : 2*t-1 ∉ q.exceptions := by
        intro hqne
        apply hB
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨2*t-1, hqne, by ring⟩))
      have hqt := q.smoothAt (2*t-1) ⟨by linarith, by linarith [ht.2]⟩ hqne
      have hc := hqt.comp t ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)
      apply hc.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hr] with u hu
      exact if_neg (not_le.mpr hu)

end RealAlgebraicGeometry
end BfgsVerification
