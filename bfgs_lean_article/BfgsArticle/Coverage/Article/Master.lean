import BfgsVerification.AlgebraicSeedCoercive
import BfgsVerification.CenteredSmoothCalculus
import BfgsVerification.UnexcitedMetric

/-!
# Lean coverage of `paper/master.tex`

The claims of the abstract restate results proved in the sections; they are
classified in `editorial/lean_coverage/register/A_master.json`. This module holds
the Lean witness for the correction M7 of `A/master/prose/003` (15 October 2026: the centered
theorem needs the compact initial sublevel inside the representation region, which the abstract
now says), and a supporting example for the note of `A/master/prose/005` (the local results
assume a unique minimizer).
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsCoverage.Article.Master
open BfgsVerification

/-- The coercive cap `Ḡ(u,v)=max{u,-u-v/8,c_∘u+d_∘v,v-17}` of Corollary
`art:failure_polyhedral`, as a formula. -/
theorem cap_formula (x : Vec 2) :
    SeedOrbit.coerciveObjective x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1) (x 1 - 17)) := by
  have hb : ∀ i : Fin 4, SeedOrbit.coerciveFamily.branch i x =
      (![x 0, -x 0 - x 1 / 8, SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1, x 1 - 17] : Fin 4 → ℝ) i := by
    intro i
    fin_cases i <;>
      simp [MaxAffine.Family.branch, SeedOrbit.coerciveFamily, dot, Fin.sum_univ_two,
        SeedCycle.g0, SeedCycle.g1, SeedCycle.g2] <;> ring
  have hle : ∀ i, SeedOrbit.coerciveFamily.branch i x ≤ SeedOrbit.coerciveObjective x :=
    fun i => SeedOrbit.coerciveFamily.branch_le i x
  obtain ⟨i, hi⟩ := SeedOrbit.coerciveFamily.exists_active x
  apply le_antisymm
  · change SeedOrbit.coerciveFamily.objective x ≤ _
    rw [← hi, hb i]
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    have h3 := hle 3
    rw [hb] at h0 h1 h2 h3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    exact max_le (max_le h0 h1) (max_le h2 h3)

/-- The sublinear part `γ(r)=max{r_1,-r_1-r_2/8,r_2}` of the cap at its minimizer. -/
def capGauge (r : Vec 2) : ℝ := max (max (r 0) (-r 0 - r 1 / 8)) (r 1)

/-- `γ ≥ 0`: the weights `8/17, 8/17, 1/17` combine its three linear pieces to zero. -/
theorem capGauge_nonneg (r : Vec 2) : 0 ≤ capGauge r := by
  have ha := le_max_left (max (r 0) (-r 0 - r 1 / 8)) (r 1)
  have hb := le_max_right (max (r 0) (-r 0 - r 1 / 8)) (r 1)
  have hc := le_max_left (r 0) (-r 0 - r 1 / 8)
  have hd := le_max_right (r 0) (-r 0 - r 1 / 8)
  simp only [capGauge]
  linarith

/-- Item `A/master/prose/003` (`paper/master.tex:42-45`), witness for its correction M7 (until
15 October 2026 the abstract said only "applies in arbitrary dimension on compact initial
sublevels"): Theorem
`art:centered` needs the compact initial sublevel to lie in the region `U` of the
centered representation. The coercive cap `Ḡ` of Corollary `art:failure_polyhedral`
is finite and convex with minimizer `x_*=(-1,16)`; on the open convex set
`U={x : ‖x-x_*‖_∞<1}` it equals `ψ(x)+γ(x-x_*)` with `ψ ≡ -1` (convex, locally
`C^{1,1}`) and `γ(r)=max{r_1,-r_1-r_2/8,r_2}` (finite, convex, positively homogeneous
of degree one). Yet the admissible run of Corollary `art:failure_polyhedral` has a
compact initial sublevel, not contained in `U`, and `Ḡ(x_k)` does not tend to
`Ḡ(x_*)`. -/
theorem centered_representation_needs_containment :
    ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (U : Set (Vec 2)) (ψ γ : Vec 2 → ℝ),
      ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧
      IsOpen U ∧ Convex ℝ U ∧ xstar ∈ U ∧
      ConvexOn ℝ U ψ ∧ CenteredSmoothSublinear.LocallyC11On U ψ ∧
      ConvexOn ℝ univ γ ∧ Homogeneous.PositiveDegreeOne γ ∧
      (∀ x ∈ U, F x = ψ x + γ (x - xstar)) ∧
      ∃ R : AdmissibleBFGSRun 2 F,
        IsCompact {x | F x ≤ F (R.x 0)} ∧ ¬ ({x | F x ≤ F (R.x 0)} ⊆ U) ∧
        ¬ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
  have hc₁ : (0 : ℝ) < 1 / 4 := by norm_num
  have hc₁' : (1 / 4 : ℝ) ≤ 1 / 3 := by norm_num
  have hc : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hc₂ : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨hcomp, hval, hlow, -, -, -, hvlim, hpos, -⟩ :=
    SeedOrbit.actual_coercive_deterministic_failure hc₁ hc₁' hc hc₂
  obtain ⟨⟨hc0, hc1⟩, ⟨hd0, hd1⟩⟩ := SeedOrbit.root_tight_box
  have hconvγ : ConvexOn ℝ univ capGauge := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hx0 : x 0 ≤ capGauge x := (le_max_left _ _).trans (le_max_left _ _)
    have hx1 : -x 0 - x 1 / 8 ≤ capGauge x := (le_max_right _ _).trans (le_max_left _ _)
    have hx2 : x 1 ≤ capGauge x := le_max_right _ _
    have hy0 : y 0 ≤ capGauge y := (le_max_left _ _).trans (le_max_left _ _)
    have hy1 : -y 0 - y 1 / 8 ≤ capGauge y := (le_max_right _ _).trans (le_max_left _ _)
    have hy2 : y 1 ≤ capGauge y := le_max_right _ _
    simp only [capGauge, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx0 hx1 hx2 hy0 hy1 hy2 ⊢
    refine max_le (max_le ?_ ?_) ?_
    · nlinarith [mul_le_mul_of_nonneg_left hx0 ha, mul_le_mul_of_nonneg_left hy0 hb]
    · nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
    · nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
  have hhomγ : Homogeneous.PositiveDegreeOne capGauge := by
    intro t ht r
    simp only [capGauge, Pi.smul_apply, smul_eq_mul]
    rw [show -(t * r 0) - t * r 1 / 8 = t * (-r 0 - r 1 / 8) by ring, mul_max_of_nonneg _ _ ht,
      mul_max_of_nonneg _ _ ht]
  have hrep : ∀ x ∈ Metric.ball SeedOrbit.coerciveOptimizer 1,
      SeedOrbit.coerciveObjective x = -1 + capGauge (x - SeedOrbit.coerciveOptimizer) := by
    intro x hx
    rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hx
    have h0 := hx 0
    have h1 := hx 1
    simp only [SeedOrbit.coerciveOptimizer, Real.dist_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, abs_lt] at h0 h1
    have hg := capGauge_nonneg (x - SeedOrbit.coerciveOptimizer)
    rw [cap_formula]
    simp only [capGauge, SeedOrbit.coerciveOptimizer, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] at hg ⊢
    set M := max (max (x 0) (-x 0 - x 1 / 8)) (x 1 - 17) with hM
    have hMγ : M = -1 + max (max (x 0 - -1) (-(x 0 - -1) - (x 1 - 16) / 8)) (x 1 - 16) := by
      apply le_antisymm
      · have ha := le_max_left (max (x 0 - -1) (-(x 0 - -1) - (x 1 - 16) / 8)) (x 1 - 16)
        have hb := le_max_right (max (x 0 - -1) (-(x 0 - -1) - (x 1 - 16) / 8)) (x 1 - 16)
        have hc' := le_max_left (x 0 - -1) (-(x 0 - -1) - (x 1 - 16) / 8)
        have hd' := le_max_right (x 0 - -1) (-(x 0 - -1) - (x 1 - 16) / 8)
        refine max_le (max_le ?_ ?_) ?_ <;> linarith
      · have ha := le_max_left (max (x 0) (-x 0 - x 1 / 8)) (x 1 - 17)
        have hb := le_max_right (max (x 0) (-x 0 - x 1 / 8)) (x 1 - 17)
        have hc' := le_max_left (x 0) (-x 0 - x 1 / 8)
        have hd' := le_max_right (x 0) (-x 0 - x 1 / 8)
        have hmax : max (max (x 0 - -1) (-(x 0 - -1) - (x 1 - 16) / 8)) (x 1 - 16) ≤ M + 1 := by
          refine max_le (max_le ?_ ?_) ?_ <;> linarith
        linarith
    have hthird : SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1 ≤ M := by
      have hx0 : x 0 ≤ 0 := by linarith
      have hx1 : 15 ≤ x 1 := by linarith
      dsimp only [SeedOrbit.seedC, SeedOrbit.seedD]
      have hcpos : 0 ≤ AlgebraicSeed.root 0 := by linarith
      have hdneg : AlgebraicSeed.root 1 ≤ -1 := by linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hcpos hx0,
        mul_le_mul_of_nonneg_right hdneg (by linarith : (0 : ℝ) ≤ x 1)]
    rw [← hMγ]
    apply le_antisymm
    · exact max_le (le_max_left _ _) (max_le hthird (le_max_right _ _))
    · exact max_le (le_max_left _ _) ((le_max_right _ (x 1 - 17)).trans (le_max_right _ _))
  refine ⟨SeedOrbit.coerciveObjective, SeedOrbit.coerciveOptimizer,
    Metric.ball SeedOrbit.coerciveOptimizer 1, fun _ => -1, capGauge,
    (SeedOrbit.coerciveRun (1 / 4) (1 / 2) hc₁ hc₁' hc hc₂).convex,
    fun x => hval ▸ hlow x, Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self one_pos,
    convexOn_const _ (convex_ball _ _), ⟨differentiableOn_const _, ?_⟩, hconvγ, hhomγ, hrep,
    SeedOrbit.coerciveRun (1 / 4) (1 / 2) hc₁ hc₁' hc hc₂, hcomp _, fun hsub => ?_, fun h => ?_⟩
  · rw [fderiv_const]
    exact (LocallyLipschitz.const 0).locallyLipschitzOn
  · have h0 : (0 : Vec 2) ∈ {x | SeedOrbit.coerciveObjective x ≤
        SeedOrbit.coerciveObjective ((SeedOrbit.coerciveRun (1 / 4) (1 / 2) hc₁ hc₁' hc hc₂).x 0)} := by
      have hz : SeedOrbit.coerciveObjective 0 = 0 := by
        rw [cap_formula]
        norm_num
      simp only [mem_setOf_eq, hz]
      exact (hpos 0).le
    have hb := hsub h0
    rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hb
    have := hb 1
    norm_num [SeedOrbit.coerciveOptimizer, Real.dist_eq] at this
  · rw [hval] at h
    exact absurd (tendsto_nhds_unique hvlim h) (by norm_num)

/-! ## Local results need the unique minimizer -/

/-- The planar function `F(u,v)=|v|`, the maximum of the linear branches `v` and `-v`. -/
def absV (x : Vec 2) : ℝ := |x 1|

theorem absV_convex : ConvexOn ℝ univ absV := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  simp only [absV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * x 1 + b * y 1| ≤ |a * x 1| + |b * y 1| := abs_add _ _
    _ = a * |x 1| + b * |y 1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- Off the line `v=0`, `|v|` has the gradient `(0, sign v)`. -/
theorem absV_hasGradient {x : Vec 2} (hx : x 1 ≠ 0) :
    HasFDerivAt absV (gradientFunctional ![0, Real.sign (x 1)]) x := by
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := x)
  show HasFDerivAt (fun y : Vec 2 => |y 1|) _ x
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hh := h1.abs_of_neg (by simpa using hneg)
    convert hh using 1
    ext z
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two, Real.sign_of_neg hneg]
  · have hh := h1.abs_of_pos (by simpa using hpos)
    convert hh using 1
    ext z
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two, Real.sign_of_pos hpos]

/-- The library's explicit admissible run `UnexcitedMetric.run` on `u^2+|v|` with
`A = 1`, `ρ = 1/2`, `c₁ = 1/4`, `c₂ = 1/2` and initial height `v₀`: its iterates are
`(0, (-1/2)^k v₀)`. -/
def axisRun (v₀ : ℝ) (hv : 0 < v₀) : AdmissibleBFGSRun 2 UnexcitedMetric.objective :=
  UnexcitedMetric.run 1 v₀ (1 / 2) (1 / 4) (1 / 2) one_pos hv (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem axisRun_x (v₀ : ℝ) (hv : 0 < v₀) (k : ℕ) :
    (axisRun v₀ hv).x k =
      ![0, UnexcitedMetric.sign k * UnexcitedMetric.radius (1 / 2) v₀ k] := rfl

theorem axisRun_g (v₀ : ℝ) (hv : 0 < v₀) (k : ℕ) :
    (axisRun v₀ hv).g k = ![0, UnexcitedMetric.sign k] := rfl

/-- `axisRun` translated by `(u₀,0)`, as an admissible run of `|v|`: the same matrices,
gradients and steps, since `|v|` does not depend on `u`. -/
def absVRun (u₀ v₀ : ℝ) (hv : 0 < v₀) : AdmissibleBFGSRun 2 absV where
  convex := absV_convex
  x k := (axisRun v₀ hv).x k + ![u₀, 0]
  H := (axisRun v₀ hv).H
  g := (axisRun v₀ hv).g
  α := (axisRun v₀ hv).α
  c₁ := (axisRun v₀ hv).c₁
  c₂ := (axisRun v₀ hv).c₂
  c₁_pos := (axisRun v₀ hv).c₁_pos
  c₁_lt_c₂ := (axisRun v₀ hv).c₁_lt_c₂
  c₂_lt_one := (axisRun v₀ hv).c₂_lt_one
  initial_posDef := (axisRun v₀ hv).initial_posDef
  alpha_pos := (axisRun v₀ hv).alpha_pos
  gradient_nonzero := (axisRun v₀ hv).gradient_nonzero
  hasGradient k := by
    have hr : 0 < UnexcitedMetric.radius (1 / 2) v₀ k :=
      UnexcitedMetric.radius_pos (by norm_num) hv k
    have hs : UnexcitedMetric.sign k = 1 ∨ UnexcitedMetric.sign k = -1 :=
      (sq_eq_one_iff).mp (UnexcitedMetric.sign_sq k)
    have hcoord : ((axisRun v₀ hv).x k + ![u₀, 0]) 1 =
        UnexcitedMetric.sign k * UnexcitedMetric.radius (1 / 2) v₀ k := by
      simp [axisRun_x]
    have hne : ((axisRun v₀ hv).x k + ![u₀, 0]) 1 ≠ 0 := by
      rw [hcoord]
      rcases hs with hs | hs <;> rw [hs]
      · rw [one_mul]
        exact hr.ne'
      · rw [neg_one_mul]
        exact neg_ne_zero.mpr hr.ne'
    have h := absV_hasGradient hne
    rw [hcoord] at h
    rw [axisRun_g]
    rcases hs with hs | hs
    · rw [hs, one_mul, Real.sign_of_pos hr] at h
      rw [hs]
      exact h
    · rw [hs, neg_one_mul, Real.sign_of_neg (neg_neg_of_pos hr)] at h
      rw [hs]
      exact h
  step k := by
    rw [(axisRun v₀ hv).step k]
    abel
  update := (axisRun v₀ hv).update
  armijo k := by
    have e : ∀ j, absV ((axisRun v₀ hv).x j + ![u₀, 0]) =
        UnexcitedMetric.objective ((axisRun v₀ hv).x j) := by
      intro j
      simp [absV, axisRun_x, UnexcitedMetric.objective]
    rw [e, e]
    exact (axisRun v₀ hv).armijo k
  weak_wolfe := (axisRun v₀ hv).weak_wolfe

/-- Item `A/master/prose/005` (`paper/master.tex:47-48`), supporting example for its note (also
cited by the note of the introduction's `A/introduction/prose/036`): the local results assume
a unique minimizer, and their conclusion `x_k → x_*` needs it. `F(u,v)=|v|` is a finite convex
maximum of the linear (hence smooth and convex) branches `v`, `-v`; it equals `v` on the closed
half-plane `v ≥ 0` and `-v` on `v ≤ 0` (a finite polyhedral partition of `ℝ²` with smooth pieces,
and `|v| = 0 + |v|` is a smooth convex loss plus a polyhedral term); at the minimizer `0`
both branches are active with affinely independent gradients `(0,1)`, `(0,-1)` and positive
balancing weights `1/2, 1/2`. The minimizer is not unique: for every `ε>0` an admissible run
starts within `ε` of `0` with `F(x_0) ≤ F(0)+ε` and does not converge to `0` (it converges to
the other minimizer `(ε/2,0)`). -/
theorem local_results_need_unique_minimizer :
    (∀ x : Vec 2, absV x = max (x 1) (-x 1)) ∧
      (∀ x : Vec 2, (0 ≤ x 1 → absV x = x 1) ∧ (x 1 ≤ 0 → absV x = -x 1)) ∧
      AffineIndependent ℝ (![![0, 1], ![0, -1]] : Fin 2 → Vec 2) ∧
      (1 / 2 : ℝ) • (![0, 1] : Vec 2) + (1 / 2 : ℝ) • ![0, -1] = 0 ∧
      (∀ x, absV 0 ≤ absV x) ∧ absV ![1, 0] = absV 0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : AdmissibleBFGSRun 2 absV,
        absV (R.x 0) ≤ absV 0 + ε ∧ ‖R.x 0‖ ≤ ε ∧ ¬ Tendsto R.x atTop (𝓝 0) := by
  have h0 : absV 0 = 0 := by simp [absV]
  refine ⟨fun x => abs_eq_max_neg, fun x => ⟨fun h => abs_of_nonneg h, fun h => abs_of_nonpos h⟩,
    affineIndependent_of_ne ℝ (fun h => by
      have h1 := congrFun h 1
      norm_num at h1), by
      ext i
      fin_cases i <;> norm_num, fun x => h0 ▸ abs_nonneg _, by simp [absV], fun ε hε => ?_⟩
  have hv : 0 < ε / 2 := by positivity
  refine ⟨absVRun (ε / 2) (ε / 2) hv, ?_, ?_, fun h => ?_⟩
  · show absV ((axisRun (ε / 2) hv).x 0 + ![ε / 2, 0]) ≤ absV 0 + ε
    rw [h0]
    simp [absV, axisRun_x, UnexcitedMetric.sign, UnexcitedMetric.radius, abs_of_pos hv]
    linarith
  · show ‖(axisRun (ε / 2) hv).x 0 + ![ε / 2, 0]‖ ≤ ε
    refine (pi_norm_le_iff_of_nonneg hε.le).mpr fun i => ?_
    fin_cases i <;>
      simp [axisRun_x, UnexcitedMetric.sign, UnexcitedMetric.radius, abs_of_pos hv,
        abs_of_pos hε] <;> linarith
  · have hlim : Tendsto (fun k => (axisRun (ε / 2) hv).x k + ![ε / 2, 0]) atTop
        (𝓝 (0 + ![ε / 2, 0])) :=
      (UnexcitedMetric.literal_point_limit (ρ := 1 / 2) (v₀ := ε / 2) (by norm_num)
        (by norm_num)).add_const _
    have he := tendsto_nhds_unique hlim h
    have := congrFun he 0
    simp at this
    linarith

end BfgsCoverage.Article.Master
