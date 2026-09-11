import BfgsVerification.LinearStableSubspace
import BfgsVerification.LBlockBasis
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U X : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem chart_isEmbedding (P : X) (E : (S×U) ≃L[ℝ] X) {h : S → U} {V : Set S}
    (hc : ContDiffOn ℝ ∞ h V) :
    Topology.IsEmbedding (fun a : V => chart P E h a) := by
  have hf : Continuous (fun a : V => chart P E h a) :=
    continuousOn_iff_continuous_restrict.mp (chart_contDiffOn P E hc).continuousOn
  have hg : Continuous (fun x : X => (E.symm (x-P)).1) :=
    continuous_fst.comp (E.symm.continuous.comp (continuous_id.sub continuous_const))
  have he : (fun x : X => (E.symm (x-P)).1) ∘ (fun a : V => chart P E h a)=
      (fun a : V => (a : S)) := by
    funext a
    exact chart_inverse P E h a
  exact Topology.IsEmbedding.of_comp hf hg (he ▸ Topology.IsEmbedding.subtypeVal)

theorem stable_inclusion_injective (E : (S×U) ≃L[ℝ] X) :
    Function.Injective (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S U)) := by
  intro a b hab
  have he : (a,(0 : U))=(b,0) := E.injective hab
  exact congrArg Prod.fst he

theorem stable_inclusion_dimension [FiniteDimensional ℝ S] (E : (S×U) ≃L[ℝ] X) :
    Module.finrank ℝ
      (LinearMap.range (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S U)).toLinearMap)=
      Module.finrank ℝ S :=
  LinearMap.finrank_range_of_inj (stable_inclusion_injective E)

theorem stable_inclusion_range (F : X →L[ℝ] X) (E : (S×U) ≃L[ℝ] X)
    (A : S →L[ℝ] S) (L : U ≃L[ℝ] U) (hA : ‖A‖<1) (hL : ‖L.symm.toContinuousLinearMap‖<1)
    (hc : F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap)) :
    (LinearMap.range (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S U)).toLinearMap : Set X)=
      linearStableSet F := by
  rw [stable_set_eq_range F E A L hA hL hc]
  rfl

end BfgsVerification.AnalyticStableGraph
