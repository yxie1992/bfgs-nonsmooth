import BfgsVerification.LShapeSpectrum
import BfgsVerification.LReturnOrbitCore
import BfgsVerification.LNormalizedOracle

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LReturnStableOrbit
open SeedOrbit LNormalizedReturn LShapeDerivative LShapeSpectrum LShapeSpectralAlgebra

theorem source_positive_return_orbit (μ : ℝ) (V : Set State) (hV : V∈𝓝 seed) :
    ∃ w : ℕ → State, (∀ n, w n∈V) ∧ Tendsto w atTop (𝓝 seed) ∧ 0<scale (w 0) ∧
      ∀ n, w (n+1)=returnMap μ (w n) := by
  obtain ⟨ls,lu,hs,hu,hsroot,huroot,hfactor⟩ := source_shape_roots
  have hr := tight_ratio root_tight_box.1 root_tight_box.2
  have hs0 : 0 < ls := by linarith [hs.1]
  have hsr : ls < seedRatio := by linarith [hs.2,hr.1]
  have hu1 : 1 < lu := by linarith [hu.1]
  have hr2 : 2 < 1/seedRatio := (lt_div_iff₀ source_ratio_pos_lt_one.1).mpr (by linarith [hr.2])
  rw [one_div] at hr2
  have hua : lu < seedRatio⁻¹ := by linarith [hu.2]
  apply LReturnOrbitCore.positive_orbit_of_shape_roots μ hs0 hsr hu1 hua source_jacobian_offdiag_positive.ne'
  · dsimp [characteristic] at hsroot
    nlinarith
  · dsimp [characteristic] at huroot
    nlinarith
  · exact hV

theorem source_oracle_orbit (μ c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂)
    (V : Set State) (hV : V∈𝓝 seed) :
    ∃ w : ℕ → State, (∀ n, w n∈V) ∧ Tendsto w atTop (𝓝 seed) ∧
      (∀ n, 0<scale (w n)) ∧
      (∀ n, LNormalizedOracle.Conditions μ c₁ c₂ (w n)) ∧
      ∀ n, w (n+1)=returnMap μ (w n) := by
  obtain ⟨U,hU,hs,hcond,hA⟩ := LNormalizedOracle.oracle_neighborhood μ hc₁ hc₁' hc₂
  obtain ⟨w,hw,ht,h0,hrec⟩ := source_positive_return_orbit μ (V∩U)
    (Filter.inter_mem hV (hU.mem_nhds hs))
  have hpos : ∀ n, 0<scale (w n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n hn =>
      rw [hrec,return_scale]
      exact mul_pos hn (hcond (w n) (hw n).2).regular.2.1
  exact ⟨w,fun n => (hw n).1,ht,hpos,fun n => hcond (w n) (hw n).2,hrec⟩

end BfgsVerification.LReturnStableOrbit
