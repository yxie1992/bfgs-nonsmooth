import BfgsVerification.AlgebraicSeedDeterministicTrace
import BfgsVerification.BFGSGradientScaling

/-! Conditional transfer interface. The actual D objective must discharge every
value and derivative field from its proved local affine plateaus. -/
noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.SeedEmbedding
open SeedOrbit

def point (p : Vec 2) (t : ℝ) (k : ℕ) : Vec 2 := p+t • orbitPoint k
def gradient (t : ℝ) (k : ℕ) : Vec 2 := t • orbitGradient k

structure Data (F : Vec 2 → ℝ) (p : Vec 2) (t A : ℝ) : Prop where
  convex : ConvexOn ℝ univ F
  values : ∀ k, F (point p t k)=A+t^2*objective seedC seedD (orbitPoint k)
  derivatives : ∀ k, HasFDerivAt F (gradientFunctional (gradient t k)) (point p t k)

theorem point_step (p : Vec 2) (t : ℝ) (k : ℕ) :
    point p t (k+1)=point p t k+bfgsStep (orbitMetric k) (gradient t k) (orbitLength k) := by
  simp only [point, gradient, orbit_step, bfgsStep_scale_gradient, smul_add]
  abel

theorem metric_update {t : ℝ} (ht : t ≠ 0) (k : ℕ) :
    orbitMetric (k+1)=inverseBFGS (orbitMetric k)
      (bfgsStep (orbitMetric k) (gradient t k) (orbitLength k)) (gradient t (k+1)-gradient t k) := by
  simp only [gradient, bfgsStep_scale_gradient, ← smul_sub,
    inverseBFGS_scale_secant_pair _ _ _ ht]
  exact orbit_update k

theorem strict_accept {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : Data F p t A) (ht : 0 < t) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) :
    F (point p t (k+1)) < F (point p t k)+
      c₁*dot (gradient t k) (bfgsStep (orbitMetric k) (gradient t k) (orbitLength k)) ∧
    c₂*dot (gradient t k) (bfgsStep (orbitMetric k) (gradient t k) (orbitLength k)) <
      dot (gradient t (k+1)) (bfgsStep (orbitMetric k) (gradient t k) (orbitLength k)) := by
  obtain ⟨ha, hw⟩ := orbit_strict_accept hc₁ hc₁' hc₂ k
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  constructor
  · rw [h.values, h.values]
    simp only [gradient, bfgsStep_scale_gradient, PlanarUpdate.dot_scale_left, dot_smul_right]
    nlinarith [mul_lt_mul_of_pos_left ha ht2]
  · simp only [gradient, bfgsStep_scale_gradient, PlanarUpdate.dot_scale_left, dot_smul_right]
    nlinarith [mul_lt_mul_of_pos_left hw ht2]

def run {F : Vec 2 → ℝ} {p : Vec 2} {t A : ℝ} (h : Data F p t A) (ht : 0 < t)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    AdmissibleBFGSRun 2 F where
  convex := h.convex
  x := point p t
  H := orbitMetric
  g := gradient t
  α := orbitLength
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).initial_posDef
  alpha_pos k := source_length_pos (phase k)
  gradient_nonzero k := smul_ne_zero ht.ne' (source_gradient_nonzero (phase k))
  hasGradient := h.derivatives
  step := point_step p t
  update := metric_update ht.ne'
  armijo k := (strict_accept h ht hc₁ hc₁' (hc₁.trans hc) k).1.le
  weak_wolfe k := (strict_accept h ht hc₁ hc₁' (hc₁.trans hc) k).2.le

theorem point_tendsto (p : Vec 2) (t : ℝ) : Tendsto (point p t) atTop (𝓝 p) := by
  simpa only [smul_zero, add_zero] using
    (tendsto_const_nhds.add (tendsto_const_nhds.smul orbitPoint_tendsto) :
      Tendsto (fun k => p+t • orbitPoint k) atTop (𝓝 (p+t • (0 : Vec 2))))

theorem values_tendsto {F : Vec 2 → ℝ} {p : Vec 2} {t A : ℝ} (h : Data F p t A) :
    Tendsto (fun k => F (point p t k)) atTop (𝓝 A) := by
  simp_rw [h.values]
  simpa only [mul_zero, add_zero] using
    tendsto_const_nhds.add (tendsto_const_nhds.mul orbit_value_tendsto)

theorem center_value {F : Vec 2 → ℝ} {p : Vec 2} {t A : ℝ} (h : Data F p t A) : F p=A := by
  exact tendsto_nhds_unique
    ((convex_continuous h.convex).continuousAt.tendsto.comp (point_tendsto p t)) (values_tendsto h)

theorem center_nonstationary {F : Vec 2 → ℝ} {p : Vec 2} {t A : ℝ}
    (h : Data F p t A) (hbelow : ∃ z, F z<A) :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F p := by
  intro hs
  obtain ⟨z, hz⟩ := hbelow
  have hh := hs z
  rw [center_value h] at hh
  norm_num [dot] at hh
  linarith

end BfgsVerification.SeedEmbedding
