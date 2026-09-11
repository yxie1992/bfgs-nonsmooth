import BfgsVerification.StableGraphCoordinates
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open scoped Topology ZeroAtInfty BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U X : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The actual stable set of the derivative, using its genuine linear powers. -/
def linearStableSet (F : X →L[ℝ] X) : Set X :=
  {v | Tendsto (fun n : ℕ => (F^n) v) atTop (𝓝 0)}

theorem conjugate_power (F : X →L[ℝ] X) (E : (S×U) ≃L[ℝ] X)
    (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (hc : F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap))
    (z : S×U) (n : ℕ) : (F^n) (E z)=E ((A^n) z.1,(L.toContinuousLinearMap^n) z.2) := by
  have he (q : S×U) : F (E q)=E (A q.1,L q.2) :=
    congrArg (fun Q : (S×U) →L[ℝ] X => Q q) hc
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [pow_succ',ContinuousLinearMap.mul_apply,hn,he,ContinuousLinearEquiv.coe_coe]

theorem stable_set_eq_range (F : X →L[ℝ] X) (E : (S×U) ≃L[ℝ] X)
    (A : S →L[ℝ] S) (L : U ≃L[ℝ] U) (hA : ‖A‖<1) (hL : ‖L.symm.toContinuousLinearMap‖<1)
    (hc : F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap)) :
    linearStableSet F=Set.range (fun a : S => E (a,0)) := by
  ext v
  constructor
  · intro hv
    have ht : Tendsto (fun n : ℕ => E.symm ((F^n) v)) atTop (𝓝 0) := by
      simpa only [map_zero] using E.symm.continuous.continuousAt.tendsto.comp hv
    let w : LocalStableOrbit.Sequence S U :=
      { toFun := fun n => E.symm ((F^n) v)
        continuous_toFun := continuous_of_discreteTopology
        zero_at_infty' := by simpa only [cocompact_eq_atTop] using ht }
    have hrec (n : ℕ) : (w n).2=L.symm (w (n+1)).2 := by
      have he := conjugate_power F E A L hc (E.symm v) n
      have he' := conjugate_power F E A L hc (E.symm v) (n+1)
      rw [E.apply_symm_apply] at he he'
      change (E.symm ((F^n) v)).2=L.symm (E.symm ((F^(n+1)) v)).2
      rw [he,he',E.symm_apply_apply,E.symm_apply_apply]
      simp only [pow_succ',ContinuousLinearMap.mul_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
    have hu := bounded_backward_orbit_zero L.symm.toContinuousLinearMap hL w.toBCF hrec 0
    have hu0 : (E.symm v).2=0 := by simpa [w] using hu
    refine ⟨(E.symm v).1,?_⟩
    change E ((E.symm v).1,0)=v
    rw [← hu0,Prod.mk.eta,E.apply_symm_apply]
  · rintro ⟨a,rfl⟩
    have htA : Tendsto (fun n : ℕ => (A^n) a) atTop (𝓝 0) := by
      have ht := (ContinuousLinearMap.apply ℝ S a : (S →L[ℝ] S) →L[ℝ] S).continuous.continuousAt.tendsto.comp
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hA)
      simpa using ht
    have ht : Tendsto (fun n : ℕ => ((A^n) a,(0 : U))) atTop (𝓝 0) :=
      htA.prodMk_nhds tendsto_const_nhds
    have hE : Tendsto (fun n : ℕ => E ((A^n) a,0)) atTop (𝓝 0) := by
      simpa only [map_zero] using E.continuous.continuousAt.tendsto.comp ht
    simpa only [linearStableSet,Set.mem_setOf_eq,conjugate_power F E A L hc,map_zero] using hE

end BfgsVerification.AnalyticStableGraph
