import BfgsVerification.ParametricFixedPoint
import Mathlib.Analysis.Analytic.Basic

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.ParametricFixedPoint

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Analytic data yield a fixed point graph smooth on one actual open
neighborhood, not just separate finite-order germs at the base. -/
theorem exists_smooth_fixedPoint_graph {Φ : S×E → E} (P : S →L[ℝ] E) (C : E →L[ℝ] E)
    (hC : ‖C‖<1) (h0 : Φ 0=0) (hΦ : AnalyticAt ℝ Φ 0)
    (hd : HasFDerivAt Φ (P.coprod C) 0) :
    ∃ g : S → E, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ g 0=0 ∧
      ContDiffOn ℝ ∞ g V ∧
      HasFDerivAt g ((oneSubEquiv C hC).symm.toContinuousLinearMap.comp P) 0 ∧
      (∀ a∈V, Φ (a,g a)=g a) ∧
      ∀ᶠ p : S×E in 𝓝 0, Φ p=p.2 → p.2=g p.1 := by
  obtain ⟨g,hg0,hgc,hgd,hge,hgu⟩ := exists_smooth_fixedPoint P C hC h0
    (n := ω) (by simp) (hΦ.contDiffAt (n := ω)) hd
  obtain ⟨U,hU,hgcU⟩ := hgc.contDiffOn (m := ∞) (by simp) (by intro _; rfl)
  obtain ⟨V,hV,hVopen,hV0⟩ := mem_nhds_iff.mp (inter_mem hU hge)
  exact ⟨g,V,hVopen,hV0,hg0,hgcU.mono (fun _ hx => (hV hx).1),hgd,
    fun _ hx => (hV hx).2,hgu⟩

end BfgsVerification.ParametricFixedPoint
