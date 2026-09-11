import BfgsVerification.NormalSpikeObjective
import BfgsVerification.InwardRadial

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

def positiveGradient {n : ℕ} (a x : Vec n) : Vec n := x + (1+seriesMass (dot a x)) • a

theorem quadratic_hasFDerivAt {n : ℕ} (x : Vec n) :
    HasFDerivAt quadratic (gradientFunctional x) x := by
  have hc (i : Fin n) : HasFDerivAt (fun z : Vec n => (z i)^2)
      ((2*x i) • (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ)) x := by
    have hi : HasFDerivAt (fun z : Vec n => z i) (ContinuousLinearMap.proj i) x :=
      (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).hasFDerivAt
    convert hi.mul hi using 1
    · ext z; exact pow_two (z i)
    · ext z; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  have hd := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => hc i)).const_mul (1/2 : ℝ)
  convert hd using 1
  ext z
  simp only [gradientFunctional_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalPenalty_hasDerivAt_pos {v : ℝ} (hv : 0 < v) :
    HasDerivAt normalPenalty (1+seriesMass v) v :=
  (hasDerivAt_abs_pos hv).add (sourcePrimitive_hasDerivAt v)

theorem objective_hasFDerivAt_pos {n : ℕ} (a x : Vec n) (hv : 0 < dot a x) :
    HasFDerivAt (objective a) (gradientFunctional (positiveGradient a x)) x := by
  have hl : HasFDerivAt (dot a) (gradientFunctional a) x := by
    convert (gradientFunctional a).hasFDerivAt (x := x) using 1
    exact funext (fun y => (gradientFunctional_apply a y).symm)
  have hp := (normalPenalty_hasDerivAt_pos hv).comp_hasFDerivAt x hl
  have hd := (quadratic_hasFDerivAt x).add hp
  convert hd using 1
  ext z
  simp only [positiveGradient, gradientFunctional_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, dot, Pi.add_apply, Pi.smul_apply,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem radial_gradient_difference {n : ℕ} (a x : Vec n) (t : ℝ) :
    dot (positiveGradient a x - positiveGradient a ((1-t) • x)) x =
      t * sqNorm x + (seriesMass (dot a x)-seriesMass ((1-t)*dot a x))*dot a x := by
  simp only [positiveGradient, dot_smul_right]
  generalize seriesMass (dot a x) = m0
  generalize seriesMass ((1-t)*dot a x) = m1
  unfold dot sqNorm
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem radial_gradient_difference_hasDerivAt {n : ℕ} (a x : Vec n) (hv : 0 < dot a x) :
    HasDerivAt (fun t : ℝ => dot (positiveGradient a x - positiveGradient a ((1-t) • x)) x)
      (sqNorm x + (dot a x)^2 * density (dot a x)) 0 := by
  have harg : HasDerivAt (fun t : ℝ => (1-t)*dot a x) (-dot a x) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).mul_const (dot a x)) using 1 <;> simp <;> ring
  have hm : HasDerivAt seriesMass (density (dot a x)) ((1-(0 : ℝ))*dot a x) := by
    simpa only [sub_zero, one_mul] using seriesMass_hasDerivAt_pos hv
  have hmass := hm.comp 0 harg
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (sqNorm x)).add
    (((hasDerivAt_const (0 : ℝ) (seriesMass (dot a x))).sub hmass).mul_const (dot a x))
  convert hd using 1
  · ext t
    exact radial_gradient_difference a x t
  · ring

end BfgsVerification.NormalSpike
