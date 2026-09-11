import BfgsVerification.NormalSpikeVariableNonsplit
import BfgsVerification.NormalSpikeGradient

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal

def variableTangent {n : ℕ} (a c x : Vec n) : Vec n :=
  tangentProjection a x + |dot a x| • c

theorem supporting_ray_derivative_eq {n : ℕ} {F : Vec n → ℝ} {x g v : Vec n}
    (hg : Homogeneous.Supports F x g) {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => F (x+t • v)) d 0) : dot g v = d := by
  have hm : IsLocalMin (fun t : ℝ => F (x+t • v)-t*dot g v) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hs := hg (x+t • v)
    simp only [add_sub_cancel_left, dot_smul_right] at hs
    simp only [zero_smul, add_zero, zero_mul, sub_zero]
    linarith
  have he := hm.hasDerivAt_eq_zero (hd.sub ((hasDerivAt_id (0 : ℝ)).mul_const (dot g v)))
  linarith

theorem variable_tangent_ray_hasDerivAt {n : ℕ} (a c x v : Vec n)
    (hw : 0 < 1+dot c x) (hv : dot a v = 0) :
    HasDerivAt (fun t : ℝ => variableObjective a c (x+t • v))
      (dot x v+|dot a x| *dot c v) 0 := by
  have hpath : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [one_smul, zero_add, id_eq] using (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hq : HasDerivAt (fun t : ℝ => quadratic (x+t • v)) (dot x v) 0 := by
    simpa only [zero_smul, add_zero, gradientFunctional_apply] using
      (quadratic_hasFDerivAt x).comp_hasDerivAt_of_eq 0 hpath (by simp)
  have haff : HasDerivAt (fun t : ℝ => (1+dot c x+t*dot c v)*|dot a x|)
      (|dot a x| *dot c v) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (1+dot c x)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (dot c v))).mul_const |dot a x| using 1 <;> ring
  have hh := (hq.add haff).add_const (sourcePrimitive (dot a x))
  apply hh.congr_of_eventuallyEq
  have hw' : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+dot c x+t*dot c v := by
    have hcont : ContinuousAt (fun t : ℝ => 1+dot c x+t*dot c v) 0 := by fun_prop
    exact hcont.eventually_const_lt (by simpa using hw)
  filter_upwards [hw'] with t ht
  simp only [variableObjective, dot_add_smul, hv, mul_zero, add_zero, abs_mul, ← add_assoc, abs_of_pos ht]

theorem dot_tangentProjection_self {n : ℕ} {a : Vec n} (ha : sqNorm a = 1) (p : Vec n) :
    dot p (tangentProjection a p) = sqNorm (tangentProjection a p) := by
  have hpy := tangentProjection_pythagorean ha p
  change p ⬝ᵥ (p-dot a p • a) = _
  rw [dotProduct_sub, dotProduct_smul]
  have hpa : p ⬝ᵥ a = dot a p := dotProduct_comm _ _
  have hpp : p ⬝ᵥ p = sqNorm p := by simp only [dotProduct, sqNorm, pow_two]
  rw [hpa, hpp]
  simp only [smul_eq_mul]
  nlinarith

theorem variable_support_tangent {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) {x g : Vec n} (hw : 0 < 1+dot c x)
    (hg : Homogeneous.Supports (variableObjective a c) x g) :
    tangentProjection a g = variableTangent a c x := by
  let p : Vec n := g-(x+|dot a x| • c)
  let v : Vec n := tangentProjection a p
  have hv : dot a v = 0 := tangentProjection_normal_zero ha p
  have hd := supporting_ray_derivative_eq hg (variable_tangent_ray_hasDerivAt a c x v hw hv)
  have hpv : dot p v = 0 := by
    change (g-(x+|dot a x| • c)) ⬝ᵥ v = 0
    rw [sub_dotProduct, add_dotProduct, smul_dotProduct]
    change dot g v - (dot x v + |dot a x| *dot c v) = 0
    linarith
  have hp0 : tangentProjection a p = 0 := by
    apply (CertificateGeometry.sqNorm_eq_zero_iff _).mp
    exact (dot_tangentProjection_self ha p).symm.trans hpv
  have hmap : tangentProjection a p = tangentProjection a g-
      (tangentProjection a x+|dot a x| • tangentProjection a c) := by
    change tangentMap a (g-(x+|dot a x| • c)) = _
    rw [map_sub, map_add, map_smul]
    rfl
  rw [hmap, tangentProjection_eq_self hc] at hp0
  exact sub_eq_zero.mp hp0

end BfgsVerification.NormalSpike
