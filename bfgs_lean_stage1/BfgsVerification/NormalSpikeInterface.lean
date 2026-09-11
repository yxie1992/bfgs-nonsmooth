import BfgsVerification.NormalSpikeSamples

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

theorem objective_coercive {n : ℕ} (a : Vec n) :
    Tendsto (objective a) (cocompact (Vec n)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(objective_sublevel_compact a b).compl_mem_cocompact] with x hx
  have hn : ¬ objective a x ≤ b := hx
  exact (lt_of_not_ge hn).le

theorem normal_coordinate (n : ℕ) (x : Vec (n+2)) : dot (normal n) x = x 0 := by
  simp [normal, dot, Pi.single_apply]

theorem printed_objective_split (n : ℕ) (v : ℝ) (u : Vec (n+1)) :
    objective (normal n) (Fin.cons v u) = (1/2 : ℝ)*sqNorm u+(1/2 : ℝ)*v^2+|v|+sourcePrimitive v := by
  rw [objective, quadratic, normal_coordinate, Fin.cons_zero, normalPenalty]
  have hs : sqNorm (Fin.cons v u) = v^2+sqNorm u := by
    simp only [sqNorm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hs]
  ring

theorem objective_support_on_interface {n : ℕ} (a x : Vec n) (hx : dot a x = 0)
    (σ : ℝ) (hσ : |σ| ≤ 1) : Homogeneous.Supports (objective a) x (x+σ • a) := by
  intro z
  have hq := convex_supporting_inequality quadratic_convex (quadratic_hasFDerivAt x) z
  have hpen : σ * dot a z ≤ normalPenalty (dot a z) := by
    calc
      _ ≤ |σ*dot a z| := le_abs_self _
      _ = |σ| * |dot a z| := abs_mul _ _
      _ ≤ 1 * |dot a z| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      _ ≤ normalPenalty (dot a z) := by
        unfold normalPenalty
        rw [← seriesPrimitive_eq_source]
        linarith [seriesPrimitive_nonneg (dot a z)]
  have he : dot (x+σ • a) (z-x) = dot x (z-x)+σ*(dot a z-dot a x) := by
    change (x+σ • a) ⬝ᵥ (z-x) = x ⬝ᵥ (z-x)+σ*(a ⬝ᵥ z-a ⬝ᵥ x)
    simp only [add_dotProduct, smul_dotProduct, dotProduct_sub, smul_eq_mul]
    ring
  rw [he, hx, sub_zero]
  simp only [objective, hx, normalPenalty_zero, add_zero]
  linarith

theorem objective_not_differentiable_on_interface {n : ℕ} (a : Vec n) (ha : sqNorm a = 1)
    (x : Vec n) (hx : dot a x = 0) : ¬ DifferentiableAt ℝ (objective a) x := by
  intro hd
  have hg := hasFDerivAt_coordinateGradient hd
  have hp := supporting_vector_eq_gradient (objective_support_on_interface a x hx 1 (by norm_num)) hg
  have hm := supporting_vector_eq_gradient (objective_support_on_interface a x hx (-1) (by norm_num)) hg
  have he := hp.trans hm.symm
  have ha0 : a = 0 := by
    ext i
    have hi := congrArg (fun z : Vec n => z i) he
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_mul, Pi.zero_apply] at hi ⊢
    linarith
  rw [ha0] at ha
  simpa [sqNorm] using ha

theorem objective_differentiable_off_interface {n : ℕ} (a x : Vec n) (hx : dot a x ≠ 0) :
    DifferentiableAt ℝ (objective a) x := by
  have hh := (normalPenalty_locallyC11_off_zero.1 (dot a x) hx).differentiableAt
    (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hl : HasFDerivAt (dot a) (gradientFunctional a) x := by
    convert (gradientFunctional a).hasFDerivAt (x := x) using 1
    exact funext (fun y => (gradientFunctional_apply a y).symm)
  exact (quadratic_hasFDerivAt x).differentiableAt.add (hh.comp x hl.differentiableAt)

theorem objective_differentiable_iff {n : ℕ} (a : Vec n) (ha : sqNorm a = 1) (x : Vec n) :
    DifferentiableAt ℝ (objective a) x ↔ dot a x ≠ 0 := by
  constructor
  · intro hd hx
    exact objective_not_differentiable_on_interface a ha x hx hd
  · exact objective_differentiable_off_interface a x

theorem objective_support_tangent {n : ℕ} (a : Vec n) (ha : sqNorm a = 1)
    (x g : Vec n) (hg : Homogeneous.Supports (objective a) x g) :
    tangentProjection a g = tangentProjection a x :=
  composite_support_projection normalPenalty_convex isOpen_univ ha 0
    (fun y _ => by simp only [objective, normalCoordinate, sub_zero]) (mem_univ x) hg
    (quadratic_hasFDerivAt x)

theorem normal_tangent_coordinate (n : ℕ) (x : Vec (n+2)) (i : Fin (n+2)) :
    tangentProjection (normal n) x i = if i=0 then 0 else x i := by
  simp only [tangentProjection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [normal_coordinate]
  simp only [normal, Pi.single_apply]
  split_ifs with h
  · subst i
    simp
  · simp [h]

theorem normal_tangent_lipschitz (n : ℕ) : LipschitzWith 1 (tangentProjection (normal n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-z))).mpr
  intro i
  simp only [Pi.sub_apply, normal_tangent_coordinate]
  split_ifs
  · simp [norm_nonneg]
  · exact norm_le_pi_norm (x-z) i

end BfgsVerification.NormalSpike
