import BfgsVerification.ObjectiveDefinitions
import BfgsVerification.PositiveUpdate
import BfgsVerification.ConvexAnalysis
import BfgsVerification.ConvexDifferentiability
import BfgsVerification.PlanarQuadraticConvergence
import BfgsVerification.PlanarQuadraticPairs

/-!
# Existence of admissible full-BFGS runs

The structure `AdmissibleBFGSRun n F` (`BfgsVerification.ObjectiveDefinitions`) specifies an
infinite admissible full-BFGS run (Definition `art:admissible`) but does not assert that one
exists: a statement quantified over all such runs of an objective could be vacuous. This module
proves a general existence theorem and applies it to the three-branch objective of Theorem
`art:nonradial-example` (`paper/sections/local.tex:367-382`), for which no admissible run had
been exhibited. So the first conclusion of that theorem (Lean:
`BfgsCoverage.Article.Local.nonradial_example`) is not vacuous: for every $H_0\succ0$ and all
$0<c_1<c_2<1$ there is an infinite admissible run with $F(x_0)<1/100$.

## General results (`BfgsVerification.AdmissibleRunExistence`)

Hypotheses on $F:\R^n\to\R$: convex, bounded below, and differentiable at all but countably many
points of every line through a point where $F$ is differentiable.

* `exists_wolfe_step`: at a point $x$ where $F$ has gradient $g\ne0$, for every $H\succ0$ and all
  $0<c_1<c_2<1$, some length $\alpha>0$, with step $s=-\alpha Hg$ (`bfgsStep H g α`), reaches a
  point $x+s$ where $F$ is differentiable, with gradient $g'$, and both the Armijo and the weak
  Wolfe conditions hold strictly.
  Proof: $\varphi(t)=F(x+tp)$ with $p=-Hg$ is convex with $\varphi'(0)=g^Tp<0$. The secant slope
  $\sigma(t)=(\varphi(t)-\varphi(0))/t$ is continuous on $(0,\infty)$, tends to
  $\varphi'(0)<c_2\varphi'(0)$ as $t\to0^+$, and exceeds $c_1\varphi'(0)$ for large $t$ because
  $F$ is bounded below. By the intermediate value theorem and continuity, $\sigma$ lies in
  $(c_2\varphi'(0),c_1\varphi'(0))$ on an open interval, which contains a point of
  differentiability (a countable set has dense complement). There $\sigma(t)<c_1\varphi'(0)$ is
  strict Armijo, and the convex supporting inequality at $x+tp$ gives
  $\nabla F(x+tp)^Tp\ge\sigma(t)>c_2\varphi'(0)$, strict weak Wolfe.
* `exists_admissible_run`: if moreover no point of differentiability has gradient zero, then from
  every point of differentiability $x_0$, every $H_0\succ0$ and all $0<c_1<c_2<1$ there is an
  infinite admissible run. It is built by recursion on states $(x,H,g)$ with $H\succ0$ and
  $g=\nabla F(x)$, each step chosen by `exists_wolfe_step`; the update stays positive definite
  because weak Wolfe gives $y^Ts\ge(1-c_2)\alpha g^THg>0$ (`curvature_pos_of_weakWolfe`,
  `inverseBFGS_posDef`).
* `quadratic_zeros_finite`: a real quadratic polynomial with a nonzero coefficient has finitely
  many zeros.

## Theorem `art:nonradial-example` (`BfgsVerification.PlanarQuadraticExample`)

The objective is the library's `objective` $=\max(f_0,f_1,f_2)$ with branches `branch`
$f_0=u+u^2+v^2/2$, $f_1=v+u^2/2+3v^2/2$, $f_2=-u-v+3u^2/2+v^2$. It is convex
(`objective_convex`) and nonnegative (`objective_nonneg`).

* `winner_two_hasGradient`, `differentiableAt_of_branch_ne`: $F$ is differentiable wherever the
  three branch values are pairwise distinct (then one branch is strictly active).
* `tie_curves`, `tie_line_finite`, `nondifferentiable_line_finite`: every line meets each tie
  set $\{f_i=f_j\}$, $i\ne j$, in finitely many points (the tie curves
  $(u+1)^2/2-(v+1/2)^2=1/4$, $(u-2)^2+(v-1)^2=5$ and $(v+2)^2/2-(u-1/2)^2=7/4$ are two
  nondegenerate hyperbolas and a circle and contain no line), so $F$ is differentiable at all but
  finitely many points of every line.
* `gradient_ne_zero_of_hasFDerivAt`: no point of differentiability has gradient zero (such a point
  would be the unique minimizer $0$, where $F-f_0\ge0$ vanishes, which forces the gradient
  $\nabla f_0(0)=(1,0)$).
* `objective_run_hypotheses`, `objective_exists_admissible_run`: the hypotheses of the general
  theorem, hence admissible runs from every point of differentiability.
* `exists_admissible_run`, `nonradial_example_nonvacuous`: in the form of
  `BfgsCoverage.Article.Local.nonradial_example` (branches and objective as variables `f`, `F`
  with their defining equations `hf`, `hF`): for every $H_0\succ0$ and all $0<c_1<c_2<1$ there is
  an admissible run starting at $x_0=(1/1000,0)$, where only $f_0$ is active and
  $F(x_0)=1001/10^6<1/100$; by `fullBFGS_explicit_basin` its values and iterates converge to
  zero.
-/

noncomputable section
open Set Filter Topology

namespace BfgsVerification.AdmissibleRunExistence

variable {n : ℕ}

/-- Existence of an accepted line-search step. Let $F:\R^n\to\R$ be convex and bounded below, and
differentiable at all but countably many points of every line through a point of
differentiability (`hline`). If $F$ has gradient $g\ne0$ at $x$, $H\succ0$ and $0<c_1<c_2<1$,
then there are $\alpha>0$ and $g'$ such that, with $s=-\alpha Hg$ (`bfgsStep H g α`), $F$ has
gradient $g'$ at $x+s$, the Armijo condition holds strictly, $F(x+s)<F(x)+c_1g^Ts$, and the weak
Wolfe condition holds strictly, $c_2g^Ts<g'^Ts$ (so the conditions of `AdmissibleBFGSRun` hold). -/
theorem exists_wolfe_step {F : Vec n → ℝ} (hconv : ConvexOn ℝ univ F)
    (hbdd : BddBelow (range F))
    (hline : ∀ x p : Vec n, DifferentiableAt ℝ F x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)}.Countable)
    {x g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) x) (hg0 : g ≠ 0)
    {H : Mat n} (hH : H.PosDef) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ g' : Vec n,
      HasFDerivAt F (gradientFunctional g') (x + bfgsStep H g α) ∧
      F (x + bfgsStep H g α) < F x + c₁ * dot g (bfgsStep H g α) ∧
      c₂ * dot g (bfgsStep H g α) < dot g' (bfgsStep H g α) := by
  set p : Vec n := -H.mulVec g with hp_def
  have hq : 0 < metricEnergy H g := metricEnergy_pos hH hg0
  have hD : dot g p = -metricEnergy H g := by
    have h := dot_bfgsStep H g 1
    simp only [bfgsStep, neg_smul, one_smul, one_mul] at h
    simpa only [hp_def] using h
  have hDneg : dot g p < 0 := by rw [hD]; linarith
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hDneg
    simp [dot] at hDneg
  have hstep : ∀ t : ℝ, bfgsStep H g t = t • p := by
    intro t
    simp only [bfgsStep, hp_def, neg_smul, smul_neg]
  set D : ℝ := dot g p with hD_def
  set φ : ℝ → ℝ := fun t => F (x + t • p) with hφ_def
  have hφ0 : φ 0 = F x := by simp [hφ_def]
  have hφc : Continuous φ :=
    (convex_continuous hconv).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hφd : HasDerivAt φ D 0 := by
    have hl : HasDerivAt (fun t : ℝ => x + t • p) p 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add x
    have h := hg.comp_hasDerivAt_of_eq 0 hl (by simp)
    simpa [hD_def] using h
  set σ : ℝ → ℝ := fun t => (φ t - φ 0) / t with hσ_def
  have hLU : c₂ * D < c₁ * D := by nlinarith
  have hDL : D < c₂ * D := by nlinarith
  have hU0 : c₁ * D < 0 := by nlinarith
  -- for small lengths the secant slope is below `c₂ D`
  obtain ⟨t₀, ht₀, hσt₀⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ σ t₀ < c₂ * D := by
    have h1 := hφd.tendsto_slope_zero_right
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (φ (0 + t) - φ 0) < c₂ * D :=
      h1.eventually (gt_mem_nhds hDL)
    have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, hlt⟩ := (h3.and h2).exists
    refine ⟨t, ht, ?_⟩
    simpa [hσ_def, div_eq_inv_mul, smul_eq_mul] using hlt
  -- for large lengths the secant slope is above `c₁ D`, since `F` is bounded below
  obtain ⟨m, hm⟩ := hbdd
  have hmF : ∀ y, m ≤ F y := fun y => hm ⟨y, rfl⟩
  have hφm : 0 ≤ φ 0 - m := by rw [hφ0]; linarith [hmF x]
  set T : ℝ := t₀ + 1 + (φ 0 - m) / (-(c₁ * D)) with hT_def
  have hdivnn : 0 ≤ (φ 0 - m) / (-(c₁ * D)) := div_nonneg hφm (by linarith)
  have hT : t₀ < T := by rw [hT_def]; linarith
  have hTpos : 0 < T := ht₀.trans hT
  have hσT : c₁ * D < σ T := by
    show c₁ * D < (φ T - φ 0) / T
    rw [lt_div_iff₀ hTpos]
    have hne : c₁ * D ≠ 0 := hU0.ne
    have hUT : c₁ * D * T = c₁ * D * (t₀ + 1) - (φ 0 - m) := by
      rw [hT_def, mul_add, mul_div_assoc', div_neg, mul_comm (c₁ * D) (φ 0 - m), mul_div_assoc,
        div_self hne]
      ring
    have hm' : m ≤ φ T := hmF _
    nlinarith
  -- intermediate value theorem
  have hσcont : ContinuousOn σ (Icc t₀ T) := by
    apply ContinuousOn.div (hφc.continuousOn.sub continuousOn_const) continuousOn_id
    intro t ht
    exact (ht₀.trans_le ht.1).ne'
  obtain ⟨t₁, ht₁, hσt₁⟩ : ∃ t₁ ∈ Icc t₀ T, σ t₁ = (c₂ * D + c₁ * D) / 2 :=
    intermediate_value_Icc hT.le hσcont ⟨by linarith, by linarith⟩
  have ht₁pos : 0 < t₁ := ht₀.trans_le ht₁.1
  have hσat : ContinuousAt σ t₁ :=
    ((hφc.continuousAt).sub continuousAt_const).div continuousAt_id ht₁pos.ne'
  have hV : {t : ℝ | 0 < t ∧ c₂ * D < σ t ∧ σ t < c₁ * D} ∈ 𝓝 t₁ := by
    have h1 : ∀ᶠ t in 𝓝 t₁, σ t ∈ Ioo (c₂ * D) (c₁ * D) :=
      hσat.eventually (Ioo_mem_nhds (by rw [hσt₁]; linarith) (by rw [hσt₁]; linarith))
    have h2 : ∀ᶠ t in 𝓝 t₁, 0 < t := lt_mem_nhds ht₁pos
    filter_upwards [h1, h2] with t h1 h2
    exact ⟨h2, h1.1, h1.2⟩
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
  -- a point of differentiability in the interval
  obtain ⟨t, htS, htI⟩ :=
    ((hline x p hg.differentiableAt hp0).dense_compl ℝ).exists_between (hlu.1.trans hlu.2)
  have hdiff : DifferentiableAt ℝ F (x + t • p) := by
    simpa using htS
  obtain ⟨htpos, hLt, htU⟩ := hsub htI
  have hg' := hasFDerivAt_coordinateGradient hdiff
  refine ⟨t, htpos, coordinateGradient F (x + t • p), ?_, ?_, ?_⟩
  · rw [hstep]
    exact hg'
  · rw [hstep, dot_smul_right, ← hD_def]
    have h : φ t - φ 0 < c₁ * D * t := (div_lt_iff₀ htpos).mp htU
    rw [hφ0] at h
    change F (x + t • p) - F x < c₁ * D * t at h
    nlinarith
  · rw [hstep, dot_smul_right, dot_smul_right, ← hD_def]
    have hs := convex_supporting_inequality hconv hg' x
    have hx : x - (x + t • p) = (-t) • p := by
      rw [neg_smul]; abel
    rw [hx, dot_smul_right] at hs
    have h : c₂ * D * t < φ t - φ 0 := (lt_div_iff₀ htpos).mp hLt
    rw [hφ0] at h
    change c₂ * D * t < F (x + t • p) - F x at h
    nlinarith

/-- Existence of infinite admissible full-BFGS runs. Let $F:\R^n\to\R$ satisfy the hypotheses of
`exists_wolfe_step` (convex, bounded below, differentiable at all but countably many points of
every line through a point of differentiability), and suppose that no point of differentiability
has gradient zero (`hstat`; for convex $F$: $F$ is differentiable at none of its minimizers). Then
for every point $x_0$ where $F$ has gradient $g_0$, every $H_0\succ0$ and all $0<c_1<c_2<1$ there
is an infinite admissible run `R : AdmissibleBFGSRun n F` with $x_0$, $g_0$, $H_0$, $c_1$, $c_2$
as initial point, initial gradient, initial matrix and constants. -/
theorem exists_admissible_run {F : Vec n → ℝ} (hconv : ConvexOn ℝ univ F)
    (hbdd : BddBelow (range F))
    (hline : ∀ x p : Vec n, DifferentiableAt ℝ F x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)}.Countable)
    (hstat : ∀ y g, HasFDerivAt F (gradientFunctional g) y → g ≠ 0)
    {x₀ g₀ : Vec n} (hg₀ : HasFDerivAt F (gradientFunctional g₀) x₀) {H₀ : Mat n}
    (hH₀ : H₀.PosDef) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun n F,
      R.x 0 = x₀ ∧ R.g 0 = g₀ ∧ R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ := by
  -- states: point, matrix, gradient, with the invariant `H ≻ 0` and `g = ∇F(x)`
  let S := {s : Vec n × Mat n × Vec n //
    s.2.1.PosDef ∧ HasFDerivAt F (gradientFunctional s.2.2) s.1}
  have hnext : ∀ s : S, ∃ α : ℝ, 0 < α ∧ ∃ g' : Vec n,
      HasFDerivAt F (gradientFunctional g') (s.1.1 + bfgsStep s.1.2.1 s.1.2.2 α) ∧
      F (s.1.1 + bfgsStep s.1.2.1 s.1.2.2 α) <
        F s.1.1 + c₁ * dot s.1.2.2 (bfgsStep s.1.2.1 s.1.2.2 α) ∧
      c₂ * dot s.1.2.2 (bfgsStep s.1.2.1 s.1.2.2 α) <
        dot g' (bfgsStep s.1.2.1 s.1.2.2 α) :=
    fun s => exists_wolfe_step hconv hbdd hline s.2.2 (hstat _ _ s.2.2) s.2.1 hc₁ hc₁₂ hc₂
  choose α hα g' hg' harm hwolfe using hnext
  let next : S → S := fun s =>
    ⟨(s.1.1 + bfgsStep s.1.2.1 s.1.2.2 (α s),
      inverseBFGS s.1.2.1 (bfgsStep s.1.2.1 s.1.2.2 (α s)) (g' s - s.1.2.2), g' s),
      inverseBFGS_posDef s.2.1 _ _ (curvature_pos_of_weakWolfe s.2.1 (hstat _ _ s.2.2) (g' s)
        (hα s) hc₂ (hwolfe s).le),
      hg' s⟩
  let seq : ℕ → S := fun k => Nat.rec (motive := fun _ => S) ⟨(x₀, H₀, g₀), hH₀, hg₀⟩
    (fun _ s => next s) k
  exact ⟨{ convex := hconv
           x := fun k => (seq k).1.1
           H := fun k => (seq k).1.2.1
           g := fun k => (seq k).1.2.2
           α := fun k => α (seq k)
           c₁ := c₁
           c₂ := c₂
           c₁_pos := hc₁
           c₁_lt_c₂ := hc₁₂
           c₂_lt_one := hc₂
           initial_posDef := hH₀
           alpha_pos := fun k => hα (seq k)
           gradient_nonzero := fun k => hstat _ _ (seq k).2.2
           hasGradient := fun k => (seq k).2.2
           step := fun _ => rfl
           update := fun _ => rfl
           armijo := fun k => (harm (seq k)).le
           weak_wolfe := fun k => (hwolfe (seq k)).le }, rfl, rfl, rfl, rfl, rfl⟩

/-- A real quadratic $at^2+bt+c$ whose coefficients are not all zero has finitely many zeros. -/
theorem quadratic_zeros_finite {a b c : ℝ} (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    {t : ℝ | a * t ^ 2 + b * t + c = 0}.Finite := by
  let P : Polynomial ℝ :=
    Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c
  have hP : P ≠ 0 := by
    intro hP0
    apply h
    have h2 := congrArg (fun Q => Polynomial.coeff Q 2) hP0
    have h1 := congrArg (fun Q => Polynomial.coeff Q 1) hP0
    have h0 := congrArg (fun Q => Polynomial.coeff Q 0) hP0
    simp [P] at h2 h1 h0
    exact ⟨h2, h1, h0⟩
  refine (Polynomial.finite_setOf_isRoot hP).subset ?_
  intro t ht
  simp only [mem_setOf_eq] at ht
  simp [P, Polynomial.IsRoot, ht]

end BfgsVerification.AdmissibleRunExistence

namespace BfgsVerification.PlanarQuadraticExample

/-- Where $f_2$ is strictly active ($f_0(x)<f_2(x)$ and $f_1(x)<f_2(x)$), $F$ has gradient
$\nabla f_2(x)$ at $x$ (the case of $f_2$, next to the library's `winner_zero_hasGradient` and
`winner_one_hasGradient`). -/
theorem winner_two_hasGradient {x : Vec 2} (h0 : branch 0 x < branch 2 x)
    (h1 : branch 1 x < branch 2 x) :
    HasFDerivAt objective (gradientFunctional (gradient 2 x)) x := by
  have hc (i : Fin 3) := (branch_contDiff (N := 0) i).continuous.continuousAt (x := x)
  have he : objective =ᶠ[𝓝 x] branch 2 := by
    filter_upwards [(hc 0).eventually_lt (hc 2) h0, (hc 1).eventually_lt (hc 2) h1] with z hz0 hz1
    rw [objective, max_eq_right hz1.le, max_eq_right hz0.le]
  exact (branch_hasGradient 2 x).congr_of_eventuallyEq he

/-- $F$ is differentiable at every point where the three branch values $f_0(x)$, $f_1(x)$,
$f_2(x)$ are pairwise distinct (exactly one branch is active there). -/
theorem differentiableAt_of_branch_ne {x : Vec 2} (h01 : branch 0 x ≠ branch 1 x)
    (h02 : branch 0 x ≠ branch 2 x) (h12 : branch 1 x ≠ branch 2 x) :
    DifferentiableAt ℝ objective x := by
  rcases lt_or_gt_of_ne h01 with h01 | h01 <;> rcases lt_or_gt_of_ne h02 with h02 | h02 <;>
    rcases lt_or_gt_of_ne h12 with h12 | h12
  all_goals first
    | exact (winner_zero_hasGradient (by linarith) (by linarith)).differentiableAt
    | exact (winner_one_hasGradient (by linarith) (by linarith)).differentiableAt
    | exact (winner_two_hasGradient (by linarith) (by linarith)).differentiableAt

/-- The branch values on the line $x+tp$, in the coordinates $u=x_0+tp_0$, $v=x_1+tp_1$. -/
theorem branch_line (x p : Vec 2) (t : ℝ) :
    branch 0 (x + t • p) = (x 0 + t * p 0) + (x 0 + t * p 0) ^ 2 + (x 1 + t * p 1) ^ 2 / 2 ∧
    branch 1 (x + t • p) = (x 1 + t * p 1) + (x 0 + t * p 0) ^ 2 / 2 +
      3 * (x 1 + t * p 1) ^ 2 / 2 ∧
    branch 2 (x + t • p) = -(x 0 + t * p 0) - (x 1 + t * p 1) + 3 * (x 0 + t * p 0) ^ 2 / 2 +
      (x 1 + t * p 1) ^ 2 := by
  simp [branch]

/-- A nonzero vector $p\in\R^2$ has $p_0^2+p_1^2>0$. -/
theorem direction_sq_pos {p : Vec 2} (hp : p ≠ 0) : 0 < p 0 ^ 2 + p 1 ^ 2 := by
  by_contra hle
  apply hp
  have h0 : p 0 ^ 2 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  have h1 : p 1 ^ 2 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- The three tie curves: $f_0=f_1$ is the hyperbola $(u+1)^2/2-(v+1/2)^2=1/4$, $f_0=f_2$ is the
circle $(u-2)^2+(v-1)^2=5$, and $f_1=f_2$ is the hyperbola $(v+2)^2/2-(u-1/2)^2=7/4$
($u=x_0$, $v=x_1$). -/
theorem tie_curves (x : Vec 2) :
    (branch 0 x = branch 1 x ↔ (x 0 + 1) ^ 2 / 2 - (x 1 + 1 / 2) ^ 2 = 1 / 4) ∧
    (branch 0 x = branch 2 x ↔ (x 0 - 2) ^ 2 + (x 1 - 1) ^ 2 = 5) ∧
    (branch 1 x = branch 2 x ↔ (x 1 + 2) ^ 2 / 2 - (x 0 - 1 / 2) ^ 2 = 7 / 4) := by
  have h0 : branch 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 := by simp [branch]
  have h1 : branch 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 := by simp [branch]
  have h2 : branch 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2 := by simp [branch]
  rw [h0, h1, h2]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · linear_combination h
  · linear_combination h
  · linear_combination (-2) * h
  · linear_combination (-1 / 2) * h
  · linear_combination h
  · linear_combination h

/-- Every line $x+tp$ ($p\ne0$) meets each tie set $\{f_i=f_j\}$, $i\ne j$, in finitely many
points: along the line $f_i-f_j$ is a quadratic in $t$ whose coefficients do not all vanish, since
no line lies in one of the tie curves of `tie_curves` (two nondegenerate hyperbolas and a
circle). -/
theorem tie_line_finite {i j : Fin 3} (hij : i ≠ j) (x : Vec 2) {p : Vec 2} (hp : p ≠ 0) :
    {t : ℝ | branch i (x + t • p) = branch j (x + t • p)}.Finite := by
  have hp2 := direction_sq_pos hp
  have h01 : {t : ℝ | branch 0 (x + t • p) = branch 1 (x + t • p)}.Finite := by
    refine (AdmissibleRunExistence.quadratic_zeros_finite
      (a := p 0 ^ 2 / 2 - p 1 ^ 2) (b := p 0 - p 1 + x 0 * p 0 - 2 * x 1 * p 1)
      (c := x 0 - x 1 + x 0 ^ 2 / 2 - x 1 ^ 2) ?_).subset ?_
    · rintro ⟨hA, hB, hC⟩
      have hb : p 1 ^ 2 = 0 := by
        linear_combination (p 0 * (1 + x 0) + p 1 * (1 + 2 * x 1)) * hB -
          2 * (1 + x 0) ^ 2 * hA - 4 * p 1 ^ 2 * hC
      nlinarith
    · intro t ht
      simp only [mem_setOf_eq, (branch_line x p t).1, (branch_line x p t).2.1] at ht ⊢
      linear_combination ht
  have h02 : {t : ℝ | branch 0 (x + t • p) = branch 2 (x + t • p)}.Finite := by
    refine (AdmissibleRunExistence.quadratic_zeros_finite
      (a := -(p 0 ^ 2 + p 1 ^ 2) / 2) (b := 2 * p 0 + p 1 - x 0 * p 0 - x 1 * p 1)
      (c := 2 * x 0 + x 1 - x 0 ^ 2 / 2 - x 1 ^ 2 / 2) ?_).subset ?_
    · rintro ⟨hA, -, -⟩
      linarith
    · intro t ht
      simp only [mem_setOf_eq, (branch_line x p t).1, (branch_line x p t).2.2] at ht ⊢
      linear_combination ht
  have h12 : {t : ℝ | branch 1 (x + t • p) = branch 2 (x + t • p)}.Finite := by
    refine (AdmissibleRunExistence.quadratic_zeros_finite
      (a := -p 0 ^ 2 + p 1 ^ 2 / 2) (b := p 0 + 2 * p 1 - 2 * x 0 * p 0 + x 1 * p 1)
      (c := x 0 + 2 * x 1 - x 0 ^ 2 + x 1 ^ 2 / 2) ?_).subset ?_
    · rintro ⟨hA, hB, hC⟩
      have ha : 7 * p 0 ^ 2 = 0 := by
        linear_combination (p 1 * (2 + x 1) - p 0 * (1 - 2 * x 0)) * hB -
          2 * (2 + x 1) ^ 2 * hA - 4 * p 0 ^ 2 * hC
      nlinarith
    · intro t ht
      simp only [mem_setOf_eq, (branch_line x p t).2.1, (branch_line x p t).2.2] at ht ⊢
      linear_combination ht
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01
    | exact h02
    | exact h12
    | exact h01.subset fun _ ht => Eq.symm ht
    | exact h02.subset fun _ ht => Eq.symm ht
    | exact h12.subset fun _ ht => Eq.symm ht

/-- On every line $x+tp$ ($p\ne0$), $F$ is differentiable at all but finitely many points: the
exceptions lie in the finite tie sets of `tie_line_finite`. -/
theorem nondifferentiable_line_finite (x p : Vec 2) (hp : p ≠ 0) :
    {t : ℝ | ¬ DifferentiableAt ℝ objective (x + t • p)}.Finite := by
  refine (((tie_line_finite (i := 0) (j := 1) (by decide) x hp).union
    (tie_line_finite (i := 0) (j := 2) (by decide) x hp)).union
    (tie_line_finite (i := 1) (j := 2) (by decide) x hp)).subset ?_
  intro t ht
  by_contra hn
  simp only [mem_union, mem_setOf_eq, not_or] at hn
  exact ht (differentiableAt_of_branch_ne hn.1.1 hn.1.2 hn.2)

/-- No point of differentiability of $F$ has gradient zero: such a point would minimize the convex
$F$, hence be $0$, the unique minimizer; but $F-f_0\ge0$ vanishes at $0$, so $F$ would have the
gradient $\nabla f_0(0)=(1,0)\ne0$ there. -/
theorem gradient_ne_zero_of_hasFDerivAt {y g : Vec 2}
    (h : HasFDerivAt objective (gradientFunctional g) y) : g ≠ 0 := by
  rintro rfl
  have hmin : ∀ z, objective y ≤ objective z := by
    intro z
    have hs := convex_supporting_inequality objective_convex h z
    simp [dot] at hs
    linarith
  have hy : y = 0 :=
    objective_unique_zero y (le_antisymm (objective_zero ▸ hmin 0) (objective_nonneg y))
  subst hy
  have hloc : IsLocalMin (fun z => objective z - branch 0 z) 0 := by
    refine Filter.Eventually.of_forall fun z => ?_
    have h00 : branch 0 0 = 0 := by simp [branch]
    have hz := branch_le_objective 0 z
    simp only [objective_zero, h00, sub_zero]
    linarith
  have h0 := hloc.hasFDerivAt_eq_zero (h.sub (branch_hasGradient 0 0))
  have he := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L ![1, 0]) h0
  rw [initial_gradients.1] at he
  simp [dot, Fin.sum_univ_two] at he

/-- The objective of Theorem `art:nonradial-example` satisfies the hypotheses of
`AdmissibleRunExistence.exists_admissible_run`, the line condition in a stronger form: it is
convex, bounded below, differentiable at all but finitely many points of every line, and no point
of differentiability has gradient zero. -/
theorem objective_run_hypotheses :
    ConvexOn ℝ univ objective ∧ BddBelow (range objective) ∧
      (∀ x p : Vec 2, p ≠ 0 → {t : ℝ | ¬ DifferentiableAt ℝ objective (x + t • p)}.Finite) ∧
      ∀ y g, HasFDerivAt objective (gradientFunctional g) y → g ≠ 0 :=
  ⟨objective_convex, ⟨0, by rintro _ ⟨x, rfl⟩; exact objective_nonneg x⟩,
    nondifferentiable_line_finite, fun _ _ h => gradient_ne_zero_of_hasFDerivAt h⟩

/-- Admissible runs of the objective of Theorem `art:nonradial-example` exist from every point of
differentiability $x_0$, for every $H_0\succ0$ and all $0<c_1<c_2<1$. -/
theorem objective_exists_admissible_run {x₀ : Vec 2} (hx₀ : DifferentiableAt ℝ objective x₀)
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 objective, R.x 0 = x₀ ∧ R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ := by
  obtain ⟨hconv, hbdd, hline, hstat⟩ := objective_run_hypotheses
  obtain ⟨R, hx, -, hH, h1, h2⟩ := AdmissibleRunExistence.exists_admissible_run hconv hbdd
    (fun x p _ hp => (hline x p hp).countable) hstat (hasFDerivAt_coordinateGradient hx₀) hH₀
    hc₁ hc₁₂ hc₂
  exact ⟨R, hx, hH, h1, h2⟩

/-- The starting point $x_0=(1/1000,0)$: only $f_0$ is active there
($f_1(x_0)<f_0(x_0)$, $f_2(x_0)<f_0(x_0)$), so $F$ has gradient $\nabla f_0(x_0)$ at $x_0$, and
$F(x_0)<1/100$. -/
theorem start_point_facts :
    branch 1 ![1 / 1000, 0] < branch 0 ![1 / 1000, 0] ∧
      branch 2 ![1 / 1000, 0] < branch 0 ![1 / 1000, 0] ∧
      HasFDerivAt objective (gradientFunctional (gradient 0 ![1 / 1000, 0])) ![1 / 1000, 0] ∧
      objective ![1 / 1000, 0] < 1 / 100 := by
  have h1 : branch 1 ![1 / 1000, 0] < branch 0 ![1 / 1000, 0] := by norm_num [branch]
  have h2 : branch 2 ![1 / 1000, 0] < branch 0 ![1 / 1000, 0] := by
    norm_num [branch, Matrix.cons_val_two]
  refine ⟨h1, h2, winner_zero_hasGradient h1 h2, ?_⟩
  rw [winner_zero_value h1.le h2.le]
  norm_num [branch]

/-- The branches and objective of Theorem `art:nonradial-example`, given as variables with their
defining equations (`hf`, `hF`, as in `BfgsCoverage.Article.Local.nonradial_example`), are the
library's `branch` and `objective`. -/
theorem eq_branch_objective (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    f = branch ∧ F = objective := by
  have hfe : f = branch := by
    funext i x
    fin_cases i
    · simp [branch, (hf x).1]
    · simp [branch, (hf x).2.1]
    · simp [branch, (hf x).2.2]
  refine ⟨hfe, ?_⟩
  funext x
  rw [hF x, hfe]
  rfl

/-- Admissible runs exist for Theorem `art:nonradial-example`: for
$f_0=u+u^2+\frac12v^2$, $f_1=v+\frac12u^2+\frac32v^2$, $f_2=-u-v+\frac32u^2+v^2$ and
$F=\max_if_i$, for every $H_0\succ0$ and all $0<c_1<c_2<1$ there is an infinite admissible
full-BFGS run with initial matrix $H_0$, constants $c_1$, $c_2$ and $F(x_0)<1/100$ (it starts at
$x_0=(1/1000,0)$). -/
theorem exists_admissible_run (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x)))
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 F, R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ F (R.x 0) < 1 / 100 := by
  obtain ⟨-, rfl⟩ := eq_branch_objective f hf F hF
  obtain ⟨-, -, hg, hv⟩ := start_point_facts
  obtain ⟨R, hx, hH, h1, h2⟩ :=
    objective_exists_admissible_run hg.differentiableAt H₀ hH₀ hc₁ hc₁₂ hc₂
  exact ⟨R, hH, h1, h2, by rw [hx]; exact hv⟩

/-- Non-vacuity of the first conclusion of Theorem `art:nonradial-example`
(`BfgsCoverage.Article.Local.nonradial_example`): for the objective of the theorem, every
$H_0\succ0$ and all $0<c_1<c_2<1$, some infinite admissible run with initial matrix $H_0$,
constants $c_1$, $c_2$ and $F(x_0)<1/100$ exists, and its values and iterates converge to zero
(by `fullBFGS_explicit_basin`). -/
theorem nonradial_example_nonvacuous (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x)))
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 F, R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ F (R.x 0) < 1 / 100 ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨R, hH, h1, h2, h0⟩ := exists_admissible_run f hf F hF H₀ hH₀ c₁ c₂ hc₁ hc₁₂ hc₂
  obtain ⟨-, rfl⟩ := eq_branch_objective f hf F hF
  exact ⟨R, hH, h1, h2, h0, fullBFGS_explicit_basin R h0⟩

end BfgsVerification.PlanarQuadraticExample
