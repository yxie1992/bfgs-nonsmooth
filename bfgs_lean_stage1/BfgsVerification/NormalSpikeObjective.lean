import BfgsVerification.NormalSpikeTargets
import BfgsVerification.FixedNormalFullComposite

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open FixedNormal

theorem scalar_locallyC11_of_contDiffOn {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) : ScalarLocallyC11On U f := by
  refine ⟨hf.differentiableOn (by norm_num), ?_⟩
  intro x hx
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := (hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hLip⟩ := hd.exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hLip⟩

theorem sourcePrimitive_locallyC11_off_zero : ScalarLocallyC11On ({0}ᶜ : Set ℝ) sourcePrimitive :=
  scalar_locallyC11_of_contDiffOn isClosed_singleton.isOpen_compl
    (sourcePrimitive_contDiffOn_off_zero.of_le (by decide))

def normalPenalty (v : ℝ) : ℝ := |v| + sourcePrimitive v

theorem normalPenalty_convex : ConvexOn ℝ univ normalPenalty := by
  have ha : ConvexOn ℝ univ (fun v : ℝ => |v|) := by
    simpa only [Real.norm_eq_abs] using (convexOn_univ_norm : ConvexOn ℝ univ (norm : ℝ → ℝ))
  exact ha.add sourcePrimitive_convex

theorem normalPenalty_nonneg (v : ℝ) : 0 ≤ normalPenalty v := by
  unfold normalPenalty
  rw [← seriesPrimitive_eq_source]
  exact add_nonneg (abs_nonneg v) (seriesPrimitive_nonneg v)

theorem normalPenalty_zero : normalPenalty 0 = 0 := by
  simp only [normalPenalty, abs_zero, zero_add, sourcePrimitive, lt_self_iff_false, if_false]

theorem normalPenalty_locallyC11_off_zero : ScalarLocallyC11On ({0}ᶜ : Set ℝ) normalPenalty := by
  apply scalar_locallyC11_of_contDiffOn isClosed_singleton.isOpen_compl
  exact (contDiffOn_abs (fun _ h => h)).add (sourcePrimitive_contDiffOn_off_zero.of_le (by decide))

def quadratic {n : ℕ} (x : Vec n) : ℝ := (1/2 : ℝ)*sqNorm x
def objective {n : ℕ} (a : Vec n) (x : Vec n) : ℝ := quadratic x + normalPenalty (dot a x)

theorem quadratic_contDiff {n : ℕ} : ContDiff ℝ 3 (@quadratic n) := by
  unfold quadratic sqNorm
  apply contDiff_const.mul
  exact ContDiff.sum (fun i _ => (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).contDiff.pow 2)

theorem quadratic_convex {n : ℕ} : ConvexOn ℝ univ (@quadratic n) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have he : a = 1-b := by linarith
  have hs := sqNorm_convex_combination x y b
  have hp := mul_nonneg (mul_nonneg hb ha) (sqNorm_nonneg (y-x))
  simp only [quadratic, smul_eq_mul]
  rw [he, hs]
  rw [he] at hp
  nlinarith

theorem quadratic_locallyC11 {n : ℕ} : CenteredSmoothSublinear.LocallyC11On univ (@quadratic n) := by
  refine ⟨(quadratic_contDiff.differentiable (by decide)).differentiableOn, ?_⟩
  intro x _
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (@quadratic n)) x := quadratic_contDiff.contDiffAt.fderiv_right (by decide)
  obtain ⟨K, t, ht, hLip⟩ := hd.exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hLip⟩

theorem objective_convex {n : ℕ} (a : Vec n) : ConvexOn ℝ univ (objective a) := by
  have hp := convex_normal_composite normalPenalty_convex a 0
  simpa only [normalCoordinate, sub_zero] using quadratic_convex.add hp

theorem objective_strongConvex {n : ℕ} (a : Vec n) :
    EuclideanStrongConvexOn univ 1 (objective a) := by
  have hp := convex_normal_composite normalPenalty_convex a 0
  simpa only [EuclideanStrongConvexOn, objective, quadratic, normalCoordinate, sub_zero,
    add_sub_cancel_left] using hp

theorem objective_zero {n : ℕ} (a : Vec n) : objective a 0 = 0 := by
  simp [objective, quadratic, sqNorm, dot, normalPenalty_zero]

theorem objective_lower_bound {n : ℕ} (a x : Vec n) : (1/2 : ℝ)*sqNorm x ≤ objective a x := by
  unfold objective quadratic
  linarith [normalPenalty_nonneg (dot a x)]

theorem objective_minimum {n : ℕ} (a : Vec n) (x : Vec n) : objective a 0 ≤ objective a x := by
  rw [objective_zero]
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (sqNorm_nonneg x)).trans (objective_lower_bound a x)

theorem objective_unique_minimum {n : ℕ} (a x : Vec n)
    (hx : objective a x = objective a 0) : x = 0 := by
  rw [objective_zero] at hx
  have hb := objective_lower_bound a x
  rw [hx] at hb
  exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp (by nlinarith [sqNorm_nonneg x])

theorem objective_sublevel_compact {n : ℕ} (a : Vec n) (c : ℝ) :
    IsCompact {x | objective a x ≤ c} :=
  Localization.sublevel_compact (objective_convex a) 0 (objective_minimum a) (objective_unique_minimum a) c

theorem objective_fullBFGS_convergence {n : ℕ} (a : Vec n) (ha : sqNorm a = 1)
    (R : AdmissibleBFGSRun n (objective a)) :
    Tendsto (fun k => objective a (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hr := R.strongly_convex_composite_convergence isOpen_univ
    (objective_sublevel_compact a (objective a (R.x 0))) (subset_univ _)
    quadratic_convex quadratic_locallyC11 normalPenalty_convex normalPenalty_locallyC11_off_zero
    ha 0 (by norm_num : (0 : ℝ) < 1) (objective_strongConvex a)
    (fun x _ => by simp only [objective, normalCoordinate, sub_zero]) 0
    (objective_minimum a) (objective_unique_minimum a) (by simp [dot])
  simpa only [objective_zero] using hr

end BfgsVerification.NormalSpike
