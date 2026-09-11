import BfgsVerification.FixedPointLinearization

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.ParametricFixedPoint

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual parameter dependence of a local fixed point, with its derivative
and local uniqueness derived by the inverse function theorem. -/
theorem exists_smooth_fixedPoint {Φ : S×E → E} (P : S →L[ℝ] E) (C : E →L[ℝ] E)
    (hC : ‖C‖<1) (h0 : Φ 0=0) {n : WithTop ℕ∞} (hn : 1≤n)
    (hΦ : ContDiffAt ℝ n Φ 0) (hd : HasFDerivAt Φ (P.coprod C) 0) :
    ∃ g : S → E, g 0=0 ∧ ContDiffAt ℝ n g 0 ∧
      HasFDerivAt g ((oneSubEquiv C hC).symm.toContinuousLinearMap.comp P) 0 ∧
      (∀ᶠ a in 𝓝 (0 : S), Φ (a,g a)=g a) ∧
      ∀ᶠ p : S×E in 𝓝 0, Φ p=p.2 → p.2=g p.1 := by
  let D := triangularEquiv P (oneSubEquiv C hC)
  have hGd : HasFDerivAt (residualMap Φ) D.toContinuousLinearMap 0 := residualMap_hasFDerivAt P C hC hd
  have hGc := residualMap_contDiffAt hΦ
  have hG0 : residualMap Φ 0=0 := residualMap_zero h0
  let I := hGc.localInverse hGd hn
  have hI0 : I 0=0 := by simpa only [hG0] using hGc.localInverse_apply_image hGd hn
  have hIc : ContDiffAt ℝ n I 0 := by simpa only [hG0] using hGc.to_localInverse hGd hn
  have hId : HasFDerivAt I D.symm.toContinuousLinearMap 0 := by
    simpa only [hG0] using (hGc.hasStrictFDerivAt' hGd hn).to_localInverse.hasFDerivAt
  have hIr : ∀ᶠ p : S×E in 𝓝 0, residualMap Φ (I p)=p := by
    simpa only [hG0] using (hGc.hasStrictFDerivAt' hGd hn).eventually_right_inverse
  have hIl : ∀ᶠ p : S×E in 𝓝 0, I (residualMap Φ p)=p :=
    (hGc.hasStrictFDerivAt' hGd hn).eventually_left_inverse
  let g : S → E := fun a => (I (a,0)).2
  refine ⟨g,?_,?_,?_,?_,?_⟩
  · change (I (0,0)).2=0
    exact congrArg Prod.snd hI0
  · have hi : ContDiffAt ℝ n (fun a : S => (a,(0 : E))) (0 : S) :=
      (ContinuousLinearMap.inl ℝ S E).contDiff.contDiffAt
    exact (hIc.comp (f := fun a : S => (a,(0 : E))) (0 : S) hi).snd
  · have hi : HasFDerivAt (fun a : S => (a,(0 : E))) (ContinuousLinearMap.inl ℝ S E) (0 : S) :=
      (ContinuousLinearMap.inl ℝ S E).hasFDerivAt
    have hg := (hId.comp (f := fun a : S => (a,(0 : E))) (0 : S) hi).snd
    apply hg.congr_fderiv
    apply ContinuousLinearMap.ext
    intro a
    change (D.symm (a,0)).2=(oneSubEquiv C hC).symm (P a)
    simp [D,triangularEquiv_symm_apply]
  · filter_upwards [((ContinuousLinearMap.inl ℝ S E).continuous.tendsto 0).eventually hIr] with a ha
    have hfst := congrArg Prod.fst ha
    have hsnd := congrArg Prod.snd ha
    change (I (a,0)).1=a at hfst
    change (I (a,0)).2-Φ (I (a,0))=0 at hsnd
    have he : I (a,0)=(a,g a) := Prod.ext hfst rfl
    rw [he] at hsnd
    exact (sub_eq_zero.mp hsnd).symm
  · filter_upwards [hIl] with p hp hfix
    have he : residualMap Φ p=(p.1,0) := by simp [residualMap,hfix]
    rw [he] at hp
    exact (congrArg Prod.snd hp).symm

end BfgsVerification.ParametricFixedPoint
