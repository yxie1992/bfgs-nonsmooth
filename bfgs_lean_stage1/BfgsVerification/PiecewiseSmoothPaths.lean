import BfgsVerification.ObjectiveDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Connected.PathConnected

/-! Objective-independent paths with finitely many exceptional interior
parameters. These are actual real-parameter curves, not assumed cell or
semialgebraic-path decomposition theorems. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure PiecewiseSmoothPath (S : Set E) (x y : E) where
  curve : ℝ → E
  continuousOn : ContinuousOn curve (Icc 0 1)
  source : curve 0 = x
  target : curve 1 = y
  mapsTo : MapsTo curve (Icc 0 1) S
  exceptions : Finset ℝ
  smoothAt : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ exceptions → ContDiffAt ℝ ∞ curve t

def PiecewiseSmoothPathIn (S : Set E) (x y : E) : Prop :=
  Nonempty (PiecewiseSmoothPath S x y)

theorem PiecewiseSmoothPathIn.mem {S : Set E} {x y : E}
    (h : PiecewiseSmoothPathIn S x y) : x ∈ S ∧ y ∈ S := by
  obtain ⟨p⟩ := h
  exact ⟨p.source ▸ p.mapsTo (by norm_num), p.target ▸ p.mapsTo (by norm_num)⟩

theorem PiecewiseSmoothPathIn.refl {S : Set E} {x : E} (hx : x ∈ S) :
    PiecewiseSmoothPathIn S x x := by
  refine ⟨⟨fun _ => x, continuousOn_const, rfl, rfl, fun _ _ => hx, ∅, ?_⟩⟩
  exact fun _ _ _ => contDiffAt_const

theorem PiecewiseSmoothPathIn.mono {S T : Set E} {x y : E}
    (h : PiecewiseSmoothPathIn S x y) (hST : S ⊆ T) : PiecewiseSmoothPathIn T x y := by
  obtain ⟨p⟩ := h
  exact ⟨{ p with mapsTo := fun _ ht => hST (p.mapsTo ht) }⟩

theorem PiecewiseSmoothPathIn.map {S : Set E} {T : Set F} {x y : E}
    (h : PiecewiseSmoothPathIn S x y) {G : E → F}
    (hG : ContDiffOn ℝ ∞ G S) (hGT : MapsTo G S T) :
    PiecewiseSmoothPathIn T (G x) (G y) := by
  obtain ⟨p⟩ := h
  refine ⟨⟨G ∘ p.curve, hG.continuousOn.comp p.continuousOn p.mapsTo,
    by simp [p.source], by simp [p.target], hGT.comp p.mapsTo, p.exceptions, ?_⟩⟩
  intro t ht he
  have hpt : p.curve t ∈ S := p.mapsTo ⟨ht.1.le, ht.2.le⟩
  have hc := (hG (p.curve t) hpt).comp t (p.smoothAt t ht he).contDiffWithinAt p.mapsTo
  exact hc.contDiffAt (Icc_mem_nhds ht.1 ht.2)

theorem PiecewiseSmoothPathIn.symm {S : Set E} {x y : E}
    (h : PiecewiseSmoothPathIn S x y) : PiecewiseSmoothPathIn S y x := by
  classical
  obtain ⟨p⟩ := h
  have hm : MapsTo (fun t : ℝ => 1-t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    change 0 ≤ 1-t ∧ 1-t ≤ 1
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨⟨fun t => p.curve (1-t), p.continuousOn.comp
    (continuous_const.sub continuous_id).continuousOn hm,
    by simpa using p.target, by simpa using p.source,
    p.mapsTo.comp hm, p.exceptions.image (fun t => 1-t), ?_⟩⟩
  intro t ht he
  have ht' : 1-t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have he' : 1-t ∉ p.exceptions := by
    intro he'
    exact he (Finset.mem_image.mpr ⟨1-t, he', by ring⟩)
  exact (p.smoothAt (1-t) ht' he').comp t (contDiffAt_const.sub contDiffAt_id)

theorem PiecewiseSmoothPathIn.segment {S : Set E} (hS : Convex ℝ S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) : PiecewiseSmoothPathIn S x y := by
  refine ⟨⟨fun t => (1-t) • x + t • y,
    ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const)).continuousOn,
    by simp, by simp, ?_, ∅, ?_⟩⟩
  · intro t ht
    exact hS hx hy (by linarith [ht.2]) ht.1 (by ring)
  · intro t _ _
    exact ((contDiffAt_const.sub contDiffAt_id).smul contDiffAt_const).add
      (contDiffAt_id.smul contDiffAt_const)

theorem PiecewiseSmoothPathIn.joinedIn {S : Set E} {x y : E}
    (h : PiecewiseSmoothPathIn S x y) : JoinedIn S x y := by
  obtain ⟨p⟩ := h
  refine ⟨⟨⟨fun t => p.curve t, p.continuousOn.restrict⟩, p.source, p.target⟩, ?_⟩
  intro t
  exact p.mapsTo t.property

end RealAlgebraicGeometry
end BfgsVerification
