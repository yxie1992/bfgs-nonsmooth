import BfgsVerification.NormalSpikeVariableTangent
import BfgsVerification.FixedNormalSourceWrappers

noncomputable section
open scoped Topology NNReal
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal CenteredSmoothSublinear

def variableRegion {n : ℕ} (c : Vec n) : Set (Vec n) := {x | |dot c x| < 1/2}

theorem variableRegion_open {n : ℕ} (c : Vec n) : IsOpen (variableRegion c) := by
  apply isOpen_lt _ continuous_const
  unfold dot
  fun_prop

theorem variableRegion_zero {n : ℕ} (c : Vec n) : (0 : Vec n) ∈ variableRegion c := by
  simp [variableRegion, dot]

theorem variableRegion_positive {n : ℕ} {c x : Vec n} (hx : x ∈ variableRegion c) :
    0 < 1+dot c x := by
  change |dot c x| < 1/2 at hx
  have hh := (abs_lt.mp hx).1
  linarith

theorem variableRegion_convex {n : ℕ} (c : Vec n) : Convex ℝ (variableRegion c) := by
  have hI : Convex ℝ (Ioo (-1/2 : ℝ) (1/2)) := convex_Ioo _ _
  have hh := hI.linear_preimage (gradientFunctional c).toLinearMap
  convert hh using 1
  ext x
  simp only [variableRegion, mem_setOf_eq, mem_preimage, mem_Ioo,
    ContinuousLinearMap.coe_coe, gradientFunctional_apply, abs_lt]
  norm_num

theorem variableTangent_lipschitz {n : ℕ} (a c : Vec n) :
    ∃ L : ℝ≥0, LipschitzWith L (variableTangent a c) := by
  let P : Vec n →L[ℝ] Vec n := (tangentMap a).toContinuousLinearMap
  let C : ℝ →L[ℝ] Vec n := (ContinuousLinearMap.id ℝ ℝ).smulRight c
  have hnorm : LipschitzWith 1 (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  have hh := P.lipschitz.add (C.lipschitz.comp (hnorm.comp (gradientFunctional a).lipschitz))
  refine ⟨‖P‖₊ + ‖C‖₊ * (1 * ‖gradientFunctional a‖₊), ?_⟩
  convert hh using 1
  ext x
  simp only [variableTangent, Function.comp_apply, gradientFunctional_apply]
  rfl

theorem variableObjective_contDiffAt_regular {n : ℕ} (a c x : Vec n)
    (hw : 0 < 1+dot c x) (hx : dot a x ≠ 0) :
    ContDiffAt ℝ 3 (variableObjective a c) x := by
  have hl (b : Vec n) : ContDiff ℝ 3 (dot b) := by
    convert (gradientFunctional b).contDiff using 1
    exact funext (fun y => (gradientFunctional_apply b y).symm)
  have hp : ContDiffAt ℝ 3 (fun y => (1+dot c y)*dot a y) x :=
    ((contDiff_const.add (hl c)).mul (hl a)).contDiffAt
  have habs0 : ContDiffAt ℝ 3 (abs : ℝ → ℝ) ((1+dot c x)*dot a x) :=
    contDiffAt_abs (mul_ne_zero hw.ne' hx)
  have habs : ContDiffAt ℝ 3 (fun y : Vec n => |(1+dot c y)*dot a y|) x := by
    convert habs0.comp x hp using 1
  have hr : ContDiffAt ℝ 3 sourcePrimitive (dot a x) :=
    sourcePrimitive_contDiffOn_off_zero.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  exact (quadratic_contDiff.contDiffAt.add habs).add (hr.comp x (hl a).contDiffAt)

theorem variableObjective_regular_locallyC11 {n : ℕ} (a c : Vec n) :
    LocallyC11On (regularRegion (variableRegion c) a 0 {0}) (variableObjective a c) := by
  let V := regularRegion (variableRegion c) a 0 {0}
  have hV : IsOpen V := isOpen_regularRegion (variableRegion_open c) a 0 isClosed_singleton
  have hd (x : Vec n) (hx : x ∈ V) : ContDiffAt ℝ 3 (variableObjective a c) x := by
    apply variableObjective_contDiffAt_regular a c x (variableRegion_positive hx.1)
    simpa only [normalCoordinate, sub_zero, mem_setOf_eq, mem_singleton_iff] using hx.2
  refine ⟨fun x hx => ((hd x hx).differentiableAt (by decide)).differentiableWithinAt, ?_⟩
  intro x hx
  have hf : ContDiffAt ℝ 1 (fderiv ℝ (variableObjective a c)) x := (hd x hx).fderiv_right (by decide)
  obtain ⟨K, t, ht, hLip⟩ := hf.exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hLip⟩

theorem variableObjective_local_fullBFGS {n : ℕ} {a c : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (hcnorm : Real.sqrt (sqNorm c) < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n (variableObjective a c),
      variableObjective a c (R.x 0) < ε →
        Tendsto (fun k => variableObjective a c (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hs := variableObjective_strongConvex ha hc (Real.sqrt_nonneg (sqNorm c))
    (Real.sq_sqrt (sqNorm_nonneg c))
  have hcF := variableObjective_convex ha hc (Real.sqrt_nonneg (sqNorm c))
    (Real.sq_sqrt (sqNorm_nonneg c)) hcnorm.le
  obtain ⟨L, hL⟩ := variableTangent_lipschitz a c
  have hr := local_hyperplane_convergence_basin hcF (0 : Vec n)
    (variableObjective_minimum a c) (variableObjective_unique_minimum a c)
    (variableRegion_open c) (variableRegion_zero c) (sub_pos.mpr hcnorm)
    (hs.subset (subset_univ _) (variableRegion_convex c)) ha 0 (by simp [dot])
    (fun x hx g hg => variable_support_tangent ha hc (variableRegion_positive hx) hg)
    hL.lipschitzOnWith (variableObjective_regular_locallyC11 a c)
  simpa only [variableObjective_zero, zero_add] using hr

end BfgsVerification.NormalSpike
