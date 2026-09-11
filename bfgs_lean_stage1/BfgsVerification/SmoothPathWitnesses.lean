import BfgsVerification.SmoothPathTargets

/-! Concrete analytic path witnesses, with their curves retained for adjoining
an actual semialgebraic graph certificate in the next layer. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def constantSmoothPath {S : Set E} {x : E} (hx : x ∈ S) :
    PiecewiseSmoothPath S x x := by
  refine ⟨fun _ => x, continuousOn_const, rfl, rfl, fun _ _ => hx, ∅, ?_⟩
  exact fun _ _ _ => contDiffAt_const

def mappedSmoothPath {S : Set E} {T : Set F} {x y : E}
    (p : PiecewiseSmoothPath S x y) {G : E → F}
    (hG : ContDiffOn ℝ ∞ G S) (hGT : MapsTo G S T) :
    PiecewiseSmoothPath T (G x) (G y) := by
  refine ⟨G ∘ p.curve, hG.continuousOn.comp p.continuousOn p.mapsTo,
    by simp [p.source], by simp [p.target], hGT.comp p.mapsTo, p.exceptions, ?_⟩
  intro t ht he
  have hpt : p.curve t ∈ S := p.mapsTo ⟨ht.1.le, ht.2.le⟩
  have hc := (hG (p.curve t) hpt).comp t (p.smoothAt t ht he).contDiffWithinAt p.mapsTo
  exact hc.contDiffAt (Icc_mem_nhds ht.1 ht.2)

def reversedSmoothPath {S : Set E} {x y : E}
    (p : PiecewiseSmoothPath S x y) : PiecewiseSmoothPath S y x := by
  classical
  have hm : MapsTo (fun t : ℝ => 1-t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    change 0 ≤ 1-t ∧ 1-t ≤ 1
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨fun t => p.curve (1-t), p.continuousOn.comp
    (continuous_const.sub continuous_id).continuousOn hm,
    by simpa using p.target, by simpa using p.source,
    p.mapsTo.comp hm, p.exceptions.image (fun t => 1-t), ?_⟩
  intro t ht he
  have ht' : 1-t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have he' : 1-t ∉ p.exceptions := by
    intro he'
    exact he (Finset.mem_image.mpr ⟨1-t, he', by ring⟩)
  exact (p.smoothAt (1-t) ht' he').comp t (contDiffAt_const.sub contDiffAt_id)

def segmentSmoothPath {S : Set E} (hS : Convex ℝ S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) : PiecewiseSmoothPath S x y := by
  refine ⟨fun t => (1-t) • x + t • y,
    ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const)).continuousOn,
    by simp, by simp, ?_, ∅, ?_⟩
  · intro t ht
    exact hS hx hy (by linarith [ht.2]) ht.1 (by ring)
  · intro t _ _
    exact ((contDiffAt_const.sub contDiffAt_id).smul contDiffAt_const).add
      (contDiffAt_id.smul contDiffAt_const)

def concatenatedSmoothPath {S : Set E} {x y z : E}
    (p : PiecewiseSmoothPath S x y) (q : PiecewiseSmoothPath S y z) :
    PiecewiseSmoothPath S x z := by
  classical
  let B := insert (1/2 : ℝ) (p.exceptions.image (fun t => t/2) ∪
    q.exceptions.image (fun t => (t+1)/2))
  refine ⟨joinedCurve p.curve q.curve,
    joinedCurve_continuousOn p.continuousOn q.continuousOn (p.target.trans q.source.symm),
    by simpa [joinedCurve] using p.source,
    by norm_num [joinedCurve]; exact q.target, ?_, B, ?_⟩
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
