import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped Topology ZeroAtInfty
open Set Filter
namespace BfgsVerification.LocalStableOrbit

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

abbrev Sequence (S U : Type*) [NormedAddCommGroup S] [NormedAddCommGroup U] := C₀(ℕ, S×U)

theorem sequence_tendsto (w : Sequence S U) : Tendsto w atTop (𝓝 0) := by
  simpa only [cocompact_eq_atTop] using zero_at_infty w

theorem sequence_norm_apply (w : Sequence S U) (n : ℕ) : ‖w n‖≤‖w‖ :=
  w.toBCF.norm_coe_le_norm n

theorem sequence_norm_le {w : Sequence S U} {R : ℝ} (hR : 0≤R) :
    ‖w‖≤R ↔ ∀ n, ‖w n‖≤R :=
  BoundedContinuousFunction.norm_le hR

def stablePart (A : S →L[ℝ] S) (N : S×U → S×U) (a : S) (w : Sequence S U) : ℕ → S
  | 0 => a
  | n+1 => A (w n).1+(N (w n)).1

def sequenceMap (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) (w : Sequence S U) : Sequence S U where
  toFun n := (stablePart A N a w n, B ((w (n+1)).2-(N (w n)).2))
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    have hw := sequence_tendsto w
    have hNw : Tendsto (fun n => N (w n)) atTop (𝓝 0) := by
      simpa only [hN0] using hN.tendsto.comp hw
    have hws : Tendsto (fun n => (w n).1) atTop (𝓝 (0 : S)) := continuous_fst.continuousAt.tendsto.comp hw
    have hNs : Tendsto (fun n => (N (w n)).1) atTop (𝓝 (0 : S)) := continuous_fst.continuousAt.tendsto.comp hNw
    have hNu : Tendsto (fun n => (N (w n)).2) atTop (𝓝 (0 : U)) := continuous_snd.continuousAt.tendsto.comp hNw
    have hs : Tendsto (fun n => stablePart A N a w (n+1)) atTop (𝓝 0) := by
      simpa only [map_zero, zero_add] using (A.continuous.tendsto 0 |>.comp hws).add hNs
    have hs' : Tendsto (stablePart A N a w) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mp hs
    have hu : Tendsto (fun n => B ((w (n+1)).2-(N (w n)).2)) atTop (𝓝 0) := by
      have hshift : Tendsto (fun n => w (n+1)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hw
      have hwu : Tendsto (fun n => (w (n+1)).2) atTop (𝓝 (0 : U)) := continuous_snd.continuousAt.tendsto.comp hshift
      have hd : Tendsto (fun n => (w (n+1)).2-(N (w n)).2) atTop (𝓝 (0 : U)) := by
        simpa only [sub_self] using hwu.sub hNu
      simpa only [map_zero] using B.continuous.tendsto 0 |>.comp hd
    exact hs'.prodMk_nhds hu

theorem sequenceMap_fst_zero (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) (w : Sequence S U) :
    (sequenceMap A B N a hN hN0 w 0).1=a := rfl

theorem sequenceMap_fst_succ (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) (w : Sequence S U) (n : ℕ) :
    (sequenceMap A B N a hN hN0 w (n+1)).1=A (w n).1+(N (w n)).1 := rfl

theorem sequenceMap_snd (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) (w : Sequence S U) (n : ℕ) :
    (sequenceMap A B N a hN hN0 w n).2=B ((w (n+1)).2-(N (w n)).2) := rfl

end BfgsVerification.LocalStableOrbit
