import BfgsVerification.LBlockConjugacy

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LBlockSplitting
set_option maxHeartbeats 1000000

/-- The actual strict derivative and its verified coordinate splitting construct
an actual local orbit with positive initial physical scale. -/
theorem positive_orbit_of_splitting {T : State → State} {P : State} {F : State →L[ℝ] State}
    (hfix : T P=P) (hderiv : HasStrictFDerivAt T F P) (hP : P 4=0)
    (E : Coordinates ≃L[ℝ] State) (hscale : ∀ w, E w 4=w.1 1)
    (A : Vec 2 →L[ℝ] Vec 2) (L : Vec 3 ≃L[ℝ] Vec 3)
    (hA : ‖A‖<1) (hL : ‖L.symm.toContinuousLinearMap‖<1)
    (hconj : F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap))
    (V : Set State) (hV : V∈𝓝 P) :
    ∃ w : ℕ → State, (∀ n, w n∈V) ∧ Tendsto w atTop (𝓝 P) ∧ 0<w 0 4 ∧
      ∀ n, w (n+1)=T (w n) := by
  let D := A.prodMap L.toContinuousLinearMap
  let S : Coordinates → Coordinates := fun w => E.symm (T (P+E w)-P)
  have hS0 : S 0=0 := by simp [S,hfix]
  have hin : HasStrictFDerivAt (fun w : Coordinates => P+E w) E.toContinuousLinearMap 0 :=
    E.toContinuousLinearMap.hasStrictFDerivAt.const_add P
  have hderiv' : HasStrictFDerivAt T F (P+E 0) := by simpa using hderiv
  have hmid := (hderiv'.comp 0 hin).sub_const P
  have hout := E.symm.toContinuousLinearMap.hasStrictFDerivAt.comp 0 hmid
  have heq : E.symm.toContinuousLinearMap.comp (F.comp E.toContinuousLinearMap)=D := by
    apply ContinuousLinearMap.ext
    intro w
    have hh := congrArg (fun Q : Coordinates →L[ℝ] State => Q w) hconj
    change F (E w)=E (D w) at hh
    change E.symm (F (E w))=D w
    rw [hh,E.symm_apply_apply]
  have hS : HasStrictFDerivAt S D 0 := by simpa only [heq] using hout
  have hV' : {w : Coordinates | P+E w∈V}∈𝓝 0 := by
    have hh : Tendsto (fun w : Coordinates => P+E w) (𝓝 0) (𝓝 P) := by
      simpa using (continuous_const.add E.continuous).continuousAt.tendsto (x:=0)
    exact hh hV
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hV'
  have he : (0 : ℝ)<(ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ) ![0,1] := by norm_num
  obtain ⟨z,hz,ht,hpos,hne,hrec⟩ := LocalStableOrbit.positive_stable_direction A L S
    hS0 hS hA hL (ContinuousLinearMap.proj 1) ![0,1] he (half_pos heps)
  refine ⟨fun n => P+E (z n),?_,?_,?_,?_⟩
  · intro n
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    exact (hz n).trans_lt (half_lt_self heps)
  · have hh : Tendsto (fun w : Coordinates => P+E w) (𝓝 0) (𝓝 P) := by
      simpa using (continuous_const.add E.continuous).continuousAt.tendsto (x:=0)
    exact hh.comp ht
  · simpa [Pi.add_apply,hP,hscale] using hpos
  · intro n
    dsimp only
    rw [hrec]
    change P+E (E.symm (T (P+E (z n))-P))=T (P+E (z n))
    rw [E.apply_symm_apply]
    abel

end BfgsVerification.LBlockSplitting
