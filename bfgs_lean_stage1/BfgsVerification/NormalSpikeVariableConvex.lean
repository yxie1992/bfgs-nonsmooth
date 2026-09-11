import BfgsVerification.NormalSpikeObjective
import BfgsVerification.EuclideanEstimates

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal

def variableObjective {n : ℕ} (a c x : Vec n) : ℝ :=
  quadratic x + |(1 + dot c x) * dot a x| + sourcePrimitive (dot a x)

def couplingQuadratic {n : ℕ} (a c : Vec n) (γ σ : ℝ) (x : Vec n) : ℝ :=
  (γ/2)*sqNorm x + σ*dot c x*dot a x

theorem tangent_dot {n : ℕ} {a c : Vec n} (hc : dot a c = 0) (x : Vec n) :
    dot c (tangentProjection a x) = dot c x := by
  have hca : c ⬝ᵥ a = 0 := by simpa only [dot, dotProduct_comm] using hc
  change c ⬝ᵥ (x - dot a x • a) = c ⬝ᵥ x
  rw [dotProduct_sub, dotProduct_smul, hca, smul_zero, sub_zero]

theorem cross_term_bound {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) {γ : ℝ} (hγ : 0 ≤ γ) (hγsq : γ^2 = sqNorm c) (x : Vec n) :
    2 * |dot c x * dot a x| ≤ γ * sqNorm x := by
  have hp := tangentProjection_pythagorean ha x
  have hcs := dot_sq_le_sqNorm_mul_sqNorm c (tangentProjection a x)
  rw [tangent_dot hc, ← hγsq] at hcs
  by_cases hz : γ = 0
  · subst γ
    have hc0 : c = 0 := (CertificateGeometry.sqNorm_eq_zero_iff c).mp (by simpa using hγsq.symm)
    simp [hc0, dot]
  have hgp : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hz)
  have hs := sq_nonneg (|dot c x| - γ * |dot a x|)
  rw [abs_mul]
  have hA : |dot c x|^2 = (dot c x)^2 := sq_abs _
  have hB : |dot a x|^2 = (dot a x)^2 := sq_abs _
  have hh : γ * (2 * (|dot c x| * |dot a x|)) ≤ γ * (γ * sqNorm x) := by
    nlinarith
  exact (mul_le_mul_left hgp).mp hh

theorem couplingQuadratic_nonneg {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) {γ σ : ℝ} (hγ : 0 ≤ γ) (hγsq : γ^2 = sqNorm c)
    (hσ : |σ| ≤ 1) (x : Vec n) : 0 ≤ couplingQuadratic a c γ σ x := by
  have hb := cross_term_bound ha hc hγ hγsq x
  have hm : |σ * (dot c x * dot a x)| ≤ |dot c x * dot a x| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hσ
  have hl := neg_abs_le (σ * (dot c x * dot a x))
  dsimp [couplingQuadratic]
  nlinarith

theorem couplingQuadratic_combination {n : ℕ} (a c : Vec n) (γ σ : ℝ) (x y : Vec n) (t : ℝ) :
    couplingQuadratic a c γ σ ((1-t) • x + t • y) =
      (1-t)*couplingQuadratic a c γ σ x + t*couplingQuadratic a c γ σ y -
        t*(1-t)*couplingQuadratic a c γ σ (y-x) := by
  simp only [couplingQuadratic, sqNorm_convex_combination]
  change _ + σ * (c ⬝ᵥ ((1-t) • x + t • y)) * (a ⬝ᵥ ((1-t) • x + t • y)) =
    _ - t*(1-t)*(_ + σ * (c ⬝ᵥ (y-x)) * (a ⬝ᵥ (y-x)))
  simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
  unfold dot dotProduct
  ring

theorem couplingQuadratic_convex {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) {γ σ : ℝ} (hγ : 0 ≤ γ) (hγsq : γ^2 = sqNorm c)
    (hσ : |σ| ≤ 1) : ConvexOn ℝ univ (couplingQuadratic a c γ σ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  have he : p = 1-q := by linarith
  simp only [smul_eq_mul]
  rw [he, couplingQuadratic_combination]
  have hn := couplingQuadratic_nonneg ha hc hγ hγsq hσ (y-x)
  have hterm := mul_nonneg (mul_nonneg hq hp) hn
  rw [he] at hterm
  linarith

theorem normalLinear_convex {n : ℕ} (a : Vec n) (σ : ℝ) :
    ConvexOn ℝ univ (fun x => σ * dot a x) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  change σ * (a ⬝ᵥ (p • x + q • y)) ≤ p * (σ * dot a x) + q * (σ * dot a y)
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  change σ * (p * dot a x + q * dot a y) ≤ p * (σ * dot a x) + q * (σ * dot a y)
  apply le_of_eq
  ring

theorem variableObjective_strongConvex {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) {γ : ℝ} (hγ : 0 ≤ γ) (hγsq : γ^2 = sqNorm c) :
    EuclideanStrongConvexOn univ (1-γ) (variableObjective a c) := by
  have hr : ConvexOn ℝ univ (fun x => sourcePrimitive (dot a x)) := by
    simpa only [normalCoordinate, sub_zero] using convex_normal_composite sourcePrimitive_convex a 0
  have hbranch (σ : ℝ) (hσ : |σ| ≤ 1) :
      ConvexOn ℝ univ (fun x => couplingQuadratic a c γ σ x + σ * dot a x + sourcePrimitive (dot a x)) :=
    ((couplingQuadratic_convex ha hc hγ hγsq hσ).add (normalLinear_convex a σ)).add hr
  have hh := (hbranch 1 (by norm_num)).sup (hbranch (-1) (by norm_num))
  unfold EuclideanStrongConvexOn
  convert hh using 1
  ext x
  simp only [Pi.sup_apply, sup_eq_max, EuclideanStrongConvexOn, variableObjective,
    couplingQuadratic, quadratic]
  rw [abs_eq_max_neg]
  by_cases h : 0 ≤ (1+dot c x)*dot a x
  · rw [max_eq_left (by linarith)]
    rw [max_eq_left (by nlinarith)]
    ring
  · rw [max_eq_right (by linarith)]
    rw [max_eq_right (by nlinarith)]
    ring

theorem variableObjective_convex {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) {γ : ℝ} (hγ : 0 ≤ γ) (hγsq : γ^2 = sqNorm c) (hγ1 : γ ≤ 1) :
    ConvexOn ℝ univ (variableObjective a c) := by
  have hs := variableObjective_strongConvex ha hc hγ hγsq
  have hq : ConvexOn ℝ univ (fun x : Vec n => (1-γ) * quadratic x) :=
    quadratic_convex.smul (by linarith)
  convert hs.add hq using 1
  ext x
  dsimp [quadratic]
  ring

theorem variableObjective_zero {n : ℕ} (a c : Vec n) : variableObjective a c 0 = 0 := by
  simp [variableObjective, quadratic, sqNorm, dot, sourcePrimitive]

theorem variableObjective_lower_bound {n : ℕ} (a c x : Vec n) :
    (1/2 : ℝ) * sqNorm x ≤ variableObjective a c x := by
  have hr : 0 ≤ sourcePrimitive (dot a x) := by rw [← seriesPrimitive_eq_source]; exact seriesPrimitive_nonneg _
  dsimp [variableObjective, quadratic]
  linarith [abs_nonneg ((1+dot c x)*dot a x)]

theorem variableObjective_minimum {n : ℕ} (a c x : Vec n) :
    variableObjective a c 0 ≤ variableObjective a c x := by
  rw [variableObjective_zero]
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (sqNorm_nonneg x)).trans (variableObjective_lower_bound a c x)

theorem variableObjective_unique_minimum {n : ℕ} (a c x : Vec n)
    (hx : variableObjective a c x = variableObjective a c 0) : x = 0 := by
  rw [variableObjective_zero] at hx
  have hb := variableObjective_lower_bound a c x
  rw [hx] at hb
  exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp (by nlinarith [sqNorm_nonneg x])

end BfgsVerification.NormalSpike
