import BfgsArticle.Coverage.Companion.Ch02M
import BfgsArticle.Coverage.Companion.Ch03T
import BfgsArticle.Coverage.Companion.Ch06F
import BfgsArticle.Coverage.Companion.Ch08A
import BfgsArticle.Coverage.Companion.Ch09C
import BfgsArticle.Coverage.Companion.Ch12D
import BfgsArticle.Coverage.Companion.Ch13L
import BfgsArticle.Coverage.Article.Master
import BfgsArticle.Coverage.Article.Verification
import BfgsVerification.HomogeneousConsequences
import BfgsVerification.RidgeConvergence
import BfgsVerification.SemialgebraicGraphs
import BfgsVerification.TransportedCertificateConvergence

/-!
# Lean coverage: `companion/chapters/01_I.tex`

Chapter 1 of the companion ("Scope, quantifiers and the result map", label `comp:I`). Register:
`editorial/lean_coverage/register/C_01_I.json`. The chapter summarizes the whole companion: most
of its sentences restate chapter results and are `SAME_AS` the items of the chapter registers
(`C_02_M.json` … `C_13_L.json`), never a `DISCREPANCY` item. This module states the sentences that
specialize, combine or weaken chapter results (it imports the finished chapter coverage modules,
the wave-3 exception of rule 6 of `editorial/lean_coverage/README.md`) and the open questions of
the closing list (line 347) that no chapter states.

## Reading of the chapter

* Runs are the library's `AdmissibleBFGSRun` (`run_definition`): a finite convex objective,
  actual gradients at the accepted iterates, the unmodified inverse update, fixed constants
  $0<c_1<c_2<1$. "Positive theorems quantify over all such infinite runs" (line 47).
* The specified implementation of N1 and N3 is the strict unit-first search
  `DeterministicLineSearch.fromMetric` of Chapter 12, that of N2 the non-strict search
  `NonStrictLineSearch.fromMetric` of Chapter 13, both for every trial budget $N\ge5$ (on these
  runs the two take the same decisions, `Ch13L.strict_margins_same_decisions`).
* N1 is Theorem `D:main` with the additions of the summary (`n1_local_failure`): globally
  Lipschitz branch Hessians, coercivity, the accepted lengths, the trial counts and the uniform
  smallness of all queries. N2 is the first paragraph of Theorem `L:thm:local`
  (`n2_local_failure`, `n2_four_branch_version`). Both are stated for the named objectives of
  Chapters 12 and 13 (the maximum of `DEmbedding.branch`, and `LUniform.smoothObjective`, the
  maximum of `LUniform.smoothBranch`), which `n1_n2_comparison` compares.
* P1 (lines 141-149) is read literally: the visibility condition is required only at the first
  points of small eligible pairs of the band (`pairwise_certificate_convergence`), a weaker
  hypothesis than that of Theorem 3.1.
* P5 (lines 218-220) is read with global hypotheses (`p5_cluster`). The explicit supersession
  (lines 230-236) is the library's `RidgeSupersession` (`ridge_supersession`,
  `ridge_tie_determinant`).
* "Semialgebraic" objectives are `RealAlgebraicGeometry.IsSemialgebraicObjective` (a
  semialgebraic graph).

## Corrected discrepancies (15 October 2026, see the register)

* Line 103 (`C/01_I/prose/023`, recurrence of M8 and M30): "The individual branches are not twice
  differentiable at the accumulation point" now reads "Three of the four branches are not twice
  differentiable at the minimizer"; the fourth is a quadratic
  (`Ch13L.branch_regularity_at_minimizer`).
* Line 103 (`C/01_I/prose/024`, recurrence of M12): "…but a countably piecewise-affine nonsmooth
  component rather than finitely many smooth branches", false when read literally ("has no
  representation by finitely many smooth branches": the step version is also a maximum of ten
  globally $C^{1,1}$, uniformly strongly convex branches, the sketch of
  `C/13_L/theorem/L:thm:local`), now reads "…wherever it exists; it is constructed from a countably
  piecewise-affine nonsmooth component rather than from four smooth branches"
  (`Ch13L.local_failure`, `Ch13L.step_decomposition`).
* Line 153 (`C/01_I/prose/048`, recurrence of M24): "RS is the radial specialization
  $W(x)=(x-x_*)(x-x_*)^T$" now reads "RS implies the radial specialization …": RS gives the radial
  specialization of the transported condition (`Ch03T.rs_covered`) but is strictly stronger than
  it (`Ch03T.s_not_exactly_rs`).
* Wording points W31-W38 and W40-W43 were applied on the same day (see the register notes).

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/001`-`disp/003`, prose `006` | 29-45 | `run_definition` |
| `disp/004` | 49-53 | `three_conclusions_distinct` |
| prose `009`, `013` | 55-57 | `compact_value_distance`, `no_acceptable_point_no_run` |
| prose `016` (`disp/005`, `disp/006`) | 71-85 | `n1_local_failure` |
| prose `020` (`disp/007`), `022` | 95-103 | `n2_local_failure`, `n2_four_branch_version` |
| prose `028`, `029` | 107 | `n1_n2_comparison` |
| prose `032`, `143` | 115, 349 | `n3_polyhedral_semialgebraic` |
| prose `035`, `037` | 123 | `qmu_branches`, `qmu_local_basin` |
| prose `041` (`disp/010`, `disp/011`) | 141-149 | `pairwise_certificate_convergence`, `pairwise_visibility_values` |
| prose `055` | 169 | `smooth_subspace_trace_linear` |
| prose `074` | 218-220 | `p5_cluster` |
| prose `082` (`disp/016`), `083` (proof) | 230-236 | `ridge_supersession`, `ridge_tie_determinant` |
| prose `110` | 289 | `compact_theorem_cannot_replace` |
| `disp/019`, prose `116` | 299-310 | `principal_minor_run`, `retired_headlines` |
| prose `127` | 333 | `semialgebraic_values_gap` |
| prose `137`, `138`, `140` (OPEN) | 347 | `C2StronglyConvexLocalTheorem`, `GenericOrPositiveMeasureFailure` (with `failingStarts`), `NonuniqueIterateConvergence` |

The other open items of line 347 are `Ch08A.GeneralDimensionalConjecture` (prose `136`) and
`Ch07H.ZeroValueIterateQuestion` (prose `141`, also prose `109` at line 289). All other items are
`SAME_AS` chapter items, `PART_OF`, `DEFINITION` or `NON_CLAIM` in the register. The `example`s at
the end show that the hypotheses of `ridge_supersession`, `p5_cluster`,
`no_acceptable_point_no_run`, `compact_value_distance`, `smooth_subspace_trace_linear` and
`pairwise_certificate_convergence` can hold.
-/

noncomputable section
open Set Filter Matrix BfgsVerification
open scoped Topology

namespace BfgsCoverage.Companion.Ch01I

/-! ## Section 1.1: algorithm, quantifiers and notions of convergence -/

/-- Item `C/01_I/disp/001` (`companion/chapters/01_I.tex:29-32`), Item `C/01_I/disp/002`
(`companion/chapters/01_I.tex:34-38`), Item `C/01_I/prose/006` (`companion/chapters/01_I.tex:40`)
and Item `C/01_I/disp/003` (`companion/chapters/01_I.tex:42-45`): the definition of an infinite
admissible run of ordinary full BFGS.

"The algorithm is ordinary full BFGS in finite-dimensional Euclidean space:
\[ g_k=\nabla F(x_k),\qquad s_k=-\alpha_kH_kg_k,\qquad y_k=g_{k+1}-g_k,\qquad H_0\succ0, \]
\[ H_{k+1}=\Bigl(I-\frac{s_ky_k^T}{y_k^Ts_k}\Bigr)H_k\Bigl(I-\frac{y_ks_k^T}{y_k^Ts_k}\Bigr)
   +\frac{s_ks_k^T}{y_k^Ts_k}. \]
An infinite admissible run has nonzero gradients at differentiable accepted iterates, positive
lengths, and fixed Armijo--weak-Wolfe constants $0<c_1<c_2<1$:
\[ F(x_{k+1})\le F(x_k)+c_1g_k^Ts_k,\qquad g_{k+1}^Ts_k\ge c_2g_k^Ts_k. \]"

The definition is the library structure `AdmissibleBFGSRun n F` (the objective is finite and
convex, a field of the structure); `BfgsCoverage.Article.Energy.admissible_iff` shows that its data
are exactly the data satisfying these conditions. Every admissible run satisfies them: $x_k$ is a
differentiable point with $g_k=\nabla F(x_k)\ne0$ (`HasFDerivAt`), $\alpha_k>0$,
$s_k=-\alpha_kH_kg_k$ (`R.displacement k`), $x_{k+1}=x_k+s_k$, $y_k=g_{k+1}-g_k$
(`R.gradientChange k`), the inverse update with $y_k^Ts_k$, which is positive (so
`(dot y s)⁻¹` is $1/(y_k^Ts_k)$), $H_0\succ0$, the fixed constants and both line-search
inequalities. -/
theorem run_definition {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    ConvexOn ℝ univ F ∧ (R.H 0).PosDef ∧ (0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1) ∧
    ∀ k, HasFDerivAt F (gradientFunctional (R.g k)) (R.x k) ∧ R.g k ≠ 0 ∧ 0 < R.α k ∧
      R.displacement k = -R.α k • (R.H k *ᵥ R.g k) ∧ R.x (k + 1) = R.x k + R.displacement k ∧
      R.gradientChange k = R.g (k + 1) - R.g k ∧
      R.H (k + 1) =
        (1 - (dot (R.gradientChange k) (R.displacement k))⁻¹ •
            outer (R.displacement k) (R.gradientChange k)) * R.H k *
          (1 - (dot (R.gradientChange k) (R.displacement k))⁻¹ •
            outer (R.gradientChange k) (R.displacement k)) +
        (dot (R.gradientChange k) (R.displacement k))⁻¹ •
          outer (R.displacement k) (R.displacement k) ∧
      0 < dot (R.gradientChange k) (R.displacement k) ∧
      F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (R.g k) (R.displacement k) ∧
      dot (R.g (k + 1)) (R.displacement k) ≥ R.c₂ * dot (R.g k) (R.displacement k) := by
  refine ⟨R.convex, R.initial_posDef, ⟨R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩, fun k => ?_⟩
  obtain ⟨hgrad, hs, hstep, hy⟩ := Ch03T.run_display R k
  obtain ⟨-, hupd⟩ := Ch03T.update_display R
  obtain ⟨-, hls⟩ := Ch03T.line_search_display R
  obtain ⟨-, hU, hcurv, hpos⟩ := hupd k
  rw [hcurv] at hU hpos
  exact ⟨hgrad, R.gradient_nonzero k, R.alpha_pos k, hs, hstep, hy, hU, hpos, (hls k).1, (hls k).2⟩

/-- The function $F(u,v)=\sqrt{u^2+v^2}-v$ on $\mathbb R^2$: the Euclidean norm minus the second
coordinate. -/
def normMinusV (x : Vec 2) : ℝ := ‖euclideanVector x‖ - x 1

theorem euclid_sq_two (x : Vec 2) : ‖euclideanVector x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [euclideanVector, Fin.sum_univ_two, sq_abs]

theorem coord_le_euclid (x : Vec 2) (i : Fin 2) : |x i| ≤ ‖euclideanVector x‖ := by
  have h := euclid_sq_two x
  have hn := norm_nonneg (euclideanVector x)
  apply abs_le_of_sq_le_sq _ hn
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem normMinusV_nonneg (x : Vec 2) : 0 ≤ normMinusV x := by
  have h := coord_le_euclid x 1
  unfold normMinusV
  linarith [le_abs_self (x 1)]

theorem normMinusV_zero_coord {x : Vec 2} (hx : normMinusV x = 0) : x 0 = 0 := by
  have h := euclid_sq_two x
  unfold normMinusV at hx
  have he : ‖euclideanVector x‖ = x 1 := by linarith
  rw [he] at h
  nlinarith [sq_nonneg (x 0)]

/-- Item `C/01_I/disp/004` (`companion/chapters/01_I.tex:51-53`), with line 49: "Three conclusions
must remain distinct:
\[ F(x_k)\to F_*;\qquad \operatorname{dist}(x_k,X_*)\to0;\qquad x_k\to x_*. \]"

Read as: the three conclusions are different statements (none of the stronger ones follows from
the weaker one in general, for finite convex objectives with attained minimum). (a) For the finite
convex $F(u,v)=\sqrt{u^2+v^2}-v$ (minimum $0$, attained on the ray $u=0\le v$) the points
$x_k=(1,k)$ have $F(x_k)\to F_*$, but their Euclidean distance to $X_*=\arg\min F$ stays at least
$1$. (b) For $F(u,v)=|v|$ the points $x_k=(k,0)$ lie in $X_*$ (distance $0$), but the sequence
does not converge. -/
theorem three_conclusions_distinct :
    (∃ (F : Vec 2 → ℝ) (x : ℕ → Vec 2), ConvexOn ℝ univ F ∧ (∀ y, F 0 ≤ F y) ∧
      Tendsto (fun k => F (x k)) atTop (𝓝 (F 0)) ∧
      ∀ k, 1 ≤ euclideanSolutionDistance F (x k)) ∧
    (∃ (F : Vec 2 → ℝ) (x : ℕ → Vec 2), ConvexOn ℝ univ F ∧ (∀ y, F 0 ≤ F y) ∧
      Tendsto (fun k => euclideanSolutionDistance F (x k)) atTop (𝓝 0) ∧
      ¬ ∃ xs : Vec 2, Tendsto x atTop (𝓝 xs)) := by
  refine ⟨⟨normMinusV, fun k => ![1, (k : ℝ)], ?_, ?_, ?_, ?_⟩,
    ⟨fun x => |x 1|, fun k => ![(k : ℝ), 0], ?_, ?_, ?_, ?_⟩⟩
  · -- convexity: a norm minus a linear function
    have hnorm : ConvexOn ℝ univ (fun x : Vec 2 => ‖euclideanVector x‖) := by
      have hl : IsLinearMap ℝ (euclideanVector : Vec 2 → EuclideanSpace ℝ (Fin 2)) :=
        ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      exact (convexOn_norm convex_univ).comp_linearMap (hl.mk' _)
    have hlin : ConcaveOn ℝ univ (fun x : Vec 2 => x 1) :=
      ⟨convex_univ, fun x _ y _ a b _ _ _ => by simp⟩
    exact hnorm.sub hlin
  · intro y
    have h0 : normMinusV 0 = 0 := by simp [normMinusV, euclideanVector]
    rw [h0]
    exact normMinusV_nonneg y
  · have h0 : normMinusV 0 = 0 := by simp [normMinusV, euclideanVector]
    rw [h0]
    have hval : ∀ k : ℕ, normMinusV ![1, (k : ℝ)] = Real.sqrt (1 + (k : ℝ) ^ 2) - k := by
      intro k
      rw [normMinusV, EuclideanSpace.norm_eq]
      simp [euclideanVector, Fin.sum_univ_two]
    have hup : ∀ k : ℕ, 1 ≤ k → Real.sqrt (1 + (k : ℝ) ^ 2) - k ≤ 1 / (2 * k) := by
      intro k hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hsq : Real.sqrt (1 + (k : ℝ) ^ 2) ≤ k + 1 / (2 * k) := by
        rw [Real.sqrt_le_left (by positivity)]
        have : (k + 1 / (2 * k) : ℝ) ^ 2 = k ^ 2 + 1 + 1 / (4 * k ^ 2) := by
          field_simp
          ring
        rw [this]
        have : (0 : ℝ) ≤ 1 / (4 * k ^ 2) := by positivity
        linarith
      linarith
    have hlow : ∀ k : ℕ, 0 ≤ Real.sqrt (1 + (k : ℝ) ^ 2) - k := by
      intro k
      have := normMinusV_nonneg ![1, (k : ℝ)]
      rwa [hval] at this
    have hlim : Tendsto (fun k : ℕ => 1 / (2 * (k : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at h
      refine h.congr fun k => ?_
      rw [one_div_mul_one_div]
    simp only [hval]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall hlow) ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hup k hk
  · intro k
    have hne : (euclideanVector '' argmin normMinusV).Nonempty :=
      ⟨euclideanVector 0, 0, fun y => by
        have h0 : normMinusV 0 = 0 := by simp [normMinusV, euclideanVector]
        rw [h0]
        exact normMinusV_nonneg y, rfl⟩
    unfold euclideanSolutionDistance
    rw [Metric.le_infDist hne]
    rintro _ ⟨y, hy, rfl⟩
    have h0 : normMinusV 0 = 0 := by simp [normMinusV, euclideanVector]
    have hy0 : normMinusV y = 0 := le_antisymm (by rw [← h0]; exact hy 0) (normMinusV_nonneg y)
    have hc := normMinusV_zero_coord hy0
    rw [dist_eq_norm]
    change 1 ≤ ‖euclideanVector (![1, (k : ℝ)] - y)‖
    have h := coord_le_euclid (![1, (k : ℝ)] - y) 0
    simp only [Pi.sub_apply, Matrix.cons_val_zero, hc, sub_zero, abs_one] at h
    exact h
  · have h := (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ))).comp_linearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
    simpa [Function.comp_def, Real.norm_eq_abs] using h
  · intro y
    simp
  · have h : ∀ k : ℕ, euclideanSolutionDistance (fun x : Vec 2 => |x 1|) ![(k : ℝ), 0] = 0 := by
      intro k
      unfold euclideanSolutionDistance
      apply Metric.infDist_zero_of_mem
      refine ⟨![(k : ℝ), 0], fun y => ?_, rfl⟩
      simp
    simp only [h]
    exact tendsto_const_nhds
  · rintro ⟨xs, hxs⟩
    have h0 : Tendsto (fun k : ℕ => (![(k : ℝ), 0] : Vec 2) 0) atTop (𝓝 (xs 0)) :=
      (continuous_apply 0).continuousAt.tendsto.comp hxs
    simp only [Matrix.cons_val_zero] at h0
    exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop _ h0

/-- Item `C/01_I/prose/009` (`companion/chapters/01_I.tex:55`): "On a compact sublevel,
objective convergence implies distance to the solution set tends to zero. Uniqueness then gives
whole-sequence convergence."

For a finite convex $F$ with minimizer $x_*$ and a compact sublevel $\{F\le b\}$, every sequence in
it with $F(x_k)\to F_*=F(x_*)$ has Euclidean distance to $X_*=\arg\min F$ tending to zero, and
$x_k\to x_*$ when $x_*$ is the unique minimizer. (Any sequence, in particular the iterates of every
admissible run starting in the sublevel, which stay there by Armijo.) -/
theorem compact_value_distance {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ y, F xstar ≤ F y) (b : ℝ) (hK : IsCompact {x | F x ≤ b}) (x : ℕ → Vec n)
    (hx : ∀ k, F (x k) ≤ b) (hval : Tendsto (fun k => F (x k)) atTop (𝓝 (F xstar))) :
    Tendsto (fun k => euclideanSolutionDistance F (x k)) atTop (𝓝 0) ∧
      ((∀ y, F y = F xstar → y = xstar) → Tendsto x atTop (𝓝 xstar)) := by
  have hc : Continuous F := convex_continuous hF
  refine ⟨euclidean_distance_to_argmin_of_values hc xstar hmin hK hx hval, fun huniq => ?_⟩
  have h := distance_to_argmin_of_values hc xstar hmin hK hx hval
  have harg : argmin F = {xstar} := by
    ext y
    simp only [argmin, mem_setOf_eq, mem_singleton_iff]
    exact ⟨fun hy => huniq y (le_antisymm (hy xstar) (hmin y)), fun hy => hy ▸ hmin⟩
  rw [harg] at h
  simp only [Metric.infDist_singleton] at h
  exact tendsto_iff_dist_tendsto_zero.mpr h

/-- Item `C/01_I/prose/013` (`companion/chapters/01_I.tex:57`): "A ray with no differentiable
acceptable point is not an infinite admissible run."

At a differentiable point $x$ with gradient $g$ and a matrix $H$, suppose that no length
$\alpha>0$ gives a differentiable point $x+\alpha p$, $p=-Hg$ (`bfgsStep H g α`), satisfying
Armijo and weak Wolfe with the constants $c_1,c_2$. Then no admissible run with these constants
passes through the state $(x,H)$: the accepted point of an admissible run is such a point. -/
theorem no_acceptable_point_no_run {n : ℕ} (F : Vec n → ℝ) (c₁ c₂ : ℝ) (x : Vec n) (H : Mat n)
    (g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hnone : ∀ α : ℝ, 0 < α → ∀ g' : Vec n,
      HasFDerivAt F (gradientFunctional g') (x + bfgsStep H g α) →
      ¬ (F (x + bfgsStep H g α) ≤ F x + c₁ * dot g (bfgsStep H g α) ∧
        c₂ * dot g (bfgsStep H g α) ≤ dot g' (bfgsStep H g α))) :
    ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ → ∀ k, ¬ (R.x k = x ∧ R.H k = H) := by
  rintro R rfl rfl k ⟨hx, hH⟩
  have hR := R.hasGradient k
  rw [hx] at hR
  have hgeq : R.g k = g := by
    have hfun := hR.unique hg
    funext i
    have := congrArg (fun L : Vec n →L[ℝ] ℝ => L (Pi.single i 1)) hfun
    simpa [gradientFunctional_apply, dot, Pi.single_apply] using this
  apply hnone (R.α k) (R.alpha_pos k) (R.g (k + 1))
  · have h1 := R.hasGradient (k + 1)
    rwa [R.step k, hx, hH, hgeq] at h1
  · have ha := R.armijo k
    have hw := R.weak_wolfe k
    rw [R.step k, hx, hH, hgeq] at ha
    rw [hH, hgeq] at hw
    exact ⟨ha, hw⟩

/-! ## Section 1.2: the negative results (N1, N2, N3) -/

open SeedOrbit DScalarGeometric in
/-- Item `C/01_I/prose/016` (`companion/chapters/01_I.tex:71-85`), the N1 summary, with its
displays Item `C/01_I/disp/005` (`companion/chapters/01_I.tex:73-76`) and Item `C/01_I/disp/006`
(`companion/chapters/01_I.tex:80-83`).

"There is one fixed coercive $F:\mathbb R^2\to\mathbb R$, with a unique nonsmooth minimizer at
zero, of the form
\[ F=\max_{0\le i\le3}f_i,\qquad f_i\in C^{2,1}(\mathbb R^2),\qquad 0\preceq\nabla^2f_i\preceq64I. \]
Every branch Hessian is globally Lipschitz. With the fixed initialization $H_0=I$, a sequence of
bad starts approaches the minimizer. The actual deterministic unit-first weak-Wolfe
doubling/bisection search produces nonstationary converged limits:
\[ x_0^{(j)}\to0,\qquad x_k^{(j)}\to p_j\ne0,\qquad F(x_k^{(j)})\downarrow F(p_j)>0,\qquad
   0\notin\partial F(p_j). \]
The same objective, starts, and trial decisions work for every fixed $0<c_1\le1/3$,
$c_1<c_2<1$. Every accepted and rejected query is differentiable. Accepted lengths repeat
$1,1/4,1/16$, with at most five trials per iteration. The entire query trajectory can remain in an
arbitrarily small neighborhood of the true minimizer. Initial objective gaps also tend to zero."

Lean form (Theorem `D:main` of Chapter 12, `Ch12D.main`, with the additions of the summary),
stated for the named objective that witnesses "There is one fixed coercive $F$": the maximum of the
four branches `DEmbedding.branch` of Chapter 12, the branches compared in `n1_n2_comparison`.
$C^{2,1}$: convex, $C^2$, with a Hessian (`RadialHessian.matrix`) that is globally Lipschitz
(Euclidean operator norm against the Euclidean distance). Coercive: $F\to\infty$ along the
cocompact filter. The specified search is the strict unit-first bracketing search
`DeterministicLineSearch.fromMetric` (any trial budget $N\ge5$); the iterates `x n k`, matrices
`H n k` (with `H n 0 = I`), gradients `g n k`, lengths `α n k`, trial lists `hist n k` (all trial
lengths in order, the last one accepted: the trial decisions) and limits `p n` are chosen before
the pair $(c_1,c_2)$, and for every admissible pair and every $n\ge1$ the run with these data is
an `AdmissibleBFGSRun` produced by the search. The queries of step $k$ are the iterate and the
trial points `x n k + a • bfgsStep (H n k) (g n k) 1` $=x_k-aH_kg_k$, `a ∈ hist n k`. The initial
objective gap is $F(x_0^{(n)})-F_*$, $F_*=F(0)$. -/
theorem n1_local_failure :
    (∀ i, ConvexOn ℝ univ (DEmbedding.branch i) ∧ ContDiff ℝ 2 (DEmbedding.branch i) ∧
      ∃ L : ℝ, ∀ x y : Vec 2,
        FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch i) x -
          RadialHessian.matrix (DEmbedding.branch i) y) ≤ L * ‖euclideanVector (x - y)‖) ∧
      (∀ i x, (RadialHessian.matrix (DEmbedding.branch i) x).PosSemidef ∧
        ((64 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (DEmbedding.branch i) x).PosSemidef) ∧
      ∀ F : Vec 2 → ℝ,
        (∀ x, F x = Finset.univ.sup' Finset.univ_nonempty (fun i => DEmbedding.branch i x)) →
        Tendsto F (cocompact (Vec 2)) atTop ∧
        (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F (0 : Vec 2) ∧
        ∃ (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (g : ℕ → ℕ → Vec 2) (α : ℕ → ℕ → ℝ)
          (hist : ℕ → ℕ → List ℝ) (p : ℕ → Vec 2),
          Tendsto (fun n => x n 0) atTop (𝓝 0) ∧
          Tendsto (fun n => F (x n 0) - F 0) atTop (𝓝 0) ∧
          (∀ n, H n 0 = 1) ∧
          (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 → ∀ n, 1 ≤ n →
            ∃ R : AdmissibleBFGSRun 2 F, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
              R.x = x n ∧ R.H = H n ∧ R.g = g n ∧ R.α = α n ∧
              ∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric F (x n k) (H n k) c₁ c₂ N =
                (some (α n k), hist n k)) ∧
          (∀ n, 1 ≤ n →
            Tendsto (x n) atTop (𝓝 (p n)) ∧ p n ≠ 0 ∧
            (∀ k, F (x n (k + 1)) < F (x n k)) ∧
            Tendsto (fun k => F (x n k)) atTop (𝓝 (F (p n))) ∧ 0 < F (p n) ∧
            (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (p n) ∧
            (∀ k, DifferentiableAt ℝ F (x n k) ∧
              ∀ a ∈ hist n k, DifferentiableAt ℝ F (x n k + a • bfgsStep (H n k) (g n k) 1)) ∧
            (∀ k, (hist n k).length ≤ 5) ∧
            ∀ m, α n (3 * m) = 1 ∧ α n (3 * m + 1) = 1/4 ∧ α n (3 * m + 2) = 1/16) ∧
          ∀ V ∈ 𝓝 (0 : Vec 2), ∀ᶠ n in atTop, ∀ k, x n k ∈ V ∧
            ∀ a ∈ hist n k, x n k + a • bfgsStep (H n k) (g n k) 1 ∈ V := by
  refine ⟨fun i => ⟨DEmbedding.branch_convex i, DEmbedding.branch_contDiff i,
    60000, DEmbedding.branch_hessian_lipschitz i⟩, DEmbedding.branch_hessian_bounds, ?_⟩
  intro F hF
  have hFe : F = DEmbedding.objective := funext hF
  subst hFe
  have hruns : ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 → ∀ n, 1 ≤ n →
      ∃ R : AdmissibleBFGSRun 2 DEmbedding.objective, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
        R.x = (fun k => SeedEmbedding.point (DEmbedding.center n) ((scale n) ^ 2) k) ∧
        R.H = (fun k => orbitMetric k) ∧ R.g = (fun k => SeedEmbedding.gradient ((scale n) ^ 2) k) ∧
        R.α = (fun k => orbitLength k) ∧
        ∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric DEmbedding.objective
          (SeedEmbedding.point (DEmbedding.center n) ((scale n) ^ 2) k) (orbitMetric k) c₁ c₂ N =
            (some (orbitLength k), trialHistory (phase k)) := by
    intro c₁ c₂ hc₁ hc₁' hc hc₂ n hn
    refine ⟨DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro k N hN
    exact Ch12D.fromMetric_fuel_mono (DEmbedding.run_search hn hc₁ hc₁' hc hc₂ k) hN
  have hc : (0 : ℝ) < 1 / 10 ^ 4 ∧ (1 / 10 ^ 4 : ℝ) ≤ 1/3 ∧ (1 / 10 ^ 4 : ℝ) < 1 / 2 ∧
      (1 / 2 : ℝ) < 1 := by
    norm_num
  refine ⟨?_, fun x => ?_, fun x hx => ?_, DEmbedding.objective_not_differentiable_zero, ?_⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [(DEmbedding.objective_sublevels_compact b).compl_mem_cocompact] with x hx
    simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
    exact hx.le
  · rw [DEmbedding.objective_zero]
    exact DEmbedding.objective_nonnegative x
  · rw [DEmbedding.objective_zero] at hx
    exact DEmbedding.objective_unique_zero hx
  refine ⟨fun n k => SeedEmbedding.point (DEmbedding.center n) ((scale n) ^ 2) k,
    fun _ k => orbitMetric k, fun n k => SeedEmbedding.gradient ((scale n) ^ 2) k,
    fun _ k => orbitLength k, fun _ k => trialHistory (phase k), DEmbedding.center,
    DEmbedding.initial_points_tendsto, ?_, fun _ => ?_, hruns, fun n hn => ?_, ?_⟩
  · have h := DEmbedding.initial_values_tendsto
    rw [DEmbedding.objective_zero]
    simpa only [sub_zero] using h
  · change (1 : ℝ) • (1 : Mat 2) = 1
    simp
  · refine ⟨SeedEmbedding.point_tendsto _ _, DEmbedding.center_ne_zero n,
      DEmbedding.run_value_strict_decrease hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2,
      DEmbedding.run_value_tendsto hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2, DEmbedding.center_positive n,
      DEmbedding.center_nonstationary n, fun k => ⟨?_, fun a ha => ?_⟩,
      fun k => trialHistory_length_le (phase k), fun m => ?_⟩
    · exact ((DEmbedding.run hn _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).hasGradient k).differentiableAt
    · obtain ⟨q, hq, rfl⟩ := BfgsCoverage.Article.Failure.mem_trialHistory ha
      exact (DEmbedding.run_all_trials_differentiable hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 k q
        hq).differentiableAt
    · obtain ⟨-, -, -, h0, h1, h2⟩ :=
        Ch12D.accepted_lengths _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 n hn m
      exact ⟨h0, h1, h2⟩
  · intro V hV
    filter_upwards [DEmbedding.trajectories_uniformly_small hV] with n hn k
    refine ⟨hn.1 k, fun a ha => ?_⟩
    obtain ⟨q, hq, rfl⟩ := BfgsCoverage.Article.Failure.mem_trialHistory ha
    rw [SeedEmbedding.translated_trial]
    exact hn.2 k q hq

/-- Item `C/01_I/prose/020` (`companion/chapters/01_I.tex:95-101`), the N2 summary, with its
display Item `C/01_I/disp/007` (`companion/chapters/01_I.tex:97-99`).

"There is also a strongly convex finite objective, with a unique nonsmooth minimizer and compact
sublevels, such that
\[ 0<\mu I\preceq\nabla^2F(x)\preceq LI \]
wherever its classical Hessian exists, yet the same specified deterministic implementation admits
bad starts arbitrarily close to the minimizer."

Lean form: the first paragraph of Theorem `L:thm:local` of Chapter 13 (`Ch13L.local_failure`;
the last clause of that theorem was corrected on 15 October 2026, M12), stated for the named
objective that witnesses "There is also a strongly convex finite objective": the four-branch
objective `LUniform.smoothObjective` of Chapter 13 (`F` is a variable with its defining equation),
the objective compared in `n1_n2_comparison`. Strongly convex in the Euclidean sense; the Hessian
exists at $x$: $F$ is differentiable near $x$ and its derivative is differentiable at $x$; the
bounds are stated with the quadratic form of `RadialHessian.matrix F x`. The implementation is the
specified unit-first search with the non-strict tests (`NonStrictLineSearch.fromMetric`, any budget
$N\ge5$); on these runs the strict tests of Chapter 12 take the same decisions
(`Ch13L.strict_margins_same_decisions`). The bad starts $x_0^{(n)}\to0$ (with $H_0=I$) and the
runs, the same for every $0<c_1\le1/3$, $c_1<c_2<1$, converge to nonstationary points $p_n$
(so not to the minimizer $0$), with differentiable trial points that stay uniformly near
zero. -/
theorem n2_local_failure (F : Vec 2 → ℝ) (hF : F = LUniform.smoothObjective) :
      (∃ κ : ℝ, 0 < κ ∧ FixedNormal.EuclideanStrongConvexOn univ κ F) ∧
      (∀ a : ℝ, IsCompact {x | F x ≤ a}) ∧
      (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F (0 : Vec 2) ∧
      (∃ μl Lu : ℝ, 0 < μl ∧ μl ≤ Lu ∧ ∀ x : Vec 2,
        (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) → DifferentiableAt ℝ (fderiv ℝ F) x →
        (RadialHessian.matrix F x).IsSymm ∧ ∀ v,
          μl * sqNorm v ≤ dot v ((RadialHessian.matrix F x).mulVec v) ∧
          dot v ((RadialHessian.matrix F x).mulVec v) ≤ Lu * sqNorm v) ∧
      ∃ (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (p : ℕ → Vec 2),
        Tendsto (fun n => x n 0) atTop (𝓝 0) ∧ (∀ n, H n 0 = 1) ∧
        (∀ n, Tendsto (x n) atTop (𝓝 (p n))) ∧
        (∀ n, (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (p n)) ∧
        Tendsto p atTop (𝓝 0) ∧
        (∀ n k, ∀ a ∈ SeedOrbit.trialHistory (SeedOrbit.phase k),
          DifferentiableAt ℝ F (x n k + a • bfgsStep (H n k) (coordinateGradient F (x n k)) 1)) ∧
        (∀ U ∈ 𝓝 (0 : Vec 2), ∃ N : ℕ, ∀ n ≥ N, ∀ k, ∀ a ∈ SeedOrbit.trialHistory (SeedOrbit.phase k),
          x n k + a • bfgsStep (H n k) (coordinateGradient F (x n k)) 1 ∈ U) ∧
        ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
          ∃ R : ℕ → AdmissibleBFGSRun 2 F, ∀ n,
            (R n).c₁ = c₁ ∧ (R n).c₂ = c₂ ∧ (R n).x = x n ∧ (R n).H = H n ∧
            ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric F ((R n).x k) ((R n).H k) c₁ c₂ N =
              (some ((R n).α k), SeedOrbit.trialHistory (SeedOrbit.phase k)) := by
  subst hF
  obtain ⟨hκ, horder, hgeom, -, -, hhess, -, htarget, -⟩ := LUniform.uniformSmoothLocalFailure
  obtain ⟨-, hstrong, hF0, hlower, hzero, hcompact, -, hnonsmooth⟩ := hgeom
  refine ⟨⟨LUniform.lowerConstant, hκ, hstrong⟩, hcompact, fun y => ?_, fun y hy => ?_,
    hnonsmooth, ⟨LUniform.lowerConstant, LUniform.upperConstant, hκ, horder, hhess⟩,
    Ch13L.runs_of_uniform htarget⟩
  · rw [hF0]
    exact (mul_nonneg (div_nonneg hκ.le (by norm_num)) (sqNorm_nonneg y)).trans (hlower y)
  · rw [hF0] at hy
    exact hzero y hy

/-- Item `C/01_I/prose/022` (`companion/chapters/01_I.tex:103`): "One version is a maximum of
four globally $C^{1,1}$, uniformly strongly convex, gradient-Lipschitz branches."

The objective of `n2_local_failure`, `LUniform.smoothObjective` (`F` is a variable with its
defining equation), is the maximum of the four branches `LUniform.smoothBranch` (the branches
compared in `n1_n2_comparison`), which are $C^1$ with one common strong-convexity modulus
(Euclidean) and one common Euclidean Lipschitz constant of their gradients (globally $C^{1,1}$). -/
theorem n2_four_branch_version (F : Vec 2 → ℝ) (hF : F = LUniform.smoothObjective) :
    (∀ x, F x = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => LUniform.smoothBranch i x)) ∧
    (∀ i, ContDiff ℝ 1 (LUniform.smoothBranch i)) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ i, FixedNormal.EuclideanStrongConvexOn univ κ (LUniform.smoothBranch i)) ∧
    ∃ L : ℝ, ∀ i y z, ‖euclideanVector (coordinateGradient (LUniform.smoothBranch i) y -
      coordinateGradient (LUniform.smoothBranch i) z)‖ ≤ L * ‖euclideanVector (y - z)‖ := by
  subst hF
  obtain ⟨hκ, -, -, hbranch, hmax, -, -, -, -⟩ := LUniform.uniformSmoothLocalFailure
  refine ⟨hmax, fun i => (hbranch i).1, ⟨LUniform.lowerConstant, hκ, fun i => (hbranch i).2.1⟩,
    LUniform.upperConstant, fun i y z => ?_⟩
  rw [DeterministicLineSearch.actual_coordinateGradient ((hbranch i).2.2.1 y),
    DeterministicLineSearch.actual_coordinateGradient ((hbranch i).2.2.1 z)]
  exact BfgsCoverage.Article.LowerCurvature.euclid_le_of_sqNorm_le LUniform.upperConstant_pos.le
    ((hbranch i).2.2.2 y z)

/-- Items `C/01_I/prose/028` (`companion/chapters/01_I.tex:107`) and
`C/01_I/prose/029` (`companion/chapters/01_I.tex:107-107`): "N1 has more branch differentiability
and no uniform positive lower curvature. N2 has positive lower curvature and less
differentiability at the accumulation point. Neither is constructed from finitely many uniformly
strongly convex $C^2$ branches through the optimizer, so neither proves local failure for that
class." (Wording point W41 applied on 15 October 2026; before "Neither proves local failure for a
finite maximum of uniformly strongly convex $C^2$ branches through the optimizer.")

N1 (the objective of `n1_local_failure`, the maximum of the branches `DEmbedding.branch`): all four
branches are
$C^2$ (even $C^{2,1}$), and no branch has uniform positive lower curvature: for no $\mu>0$ is
$\nabla^2f_i\succeq\mu I$ everywhere, and no branch is $\mu$-strongly convex. N2 (the four-branch
objective of `n2_local_failure`, `LUniform.smoothObjective`, the maximum of
`LUniform.smoothBranch`): positive lower curvature $\nabla^2F\succeq\mu I$ wherever its Hessian
exists, with uniformly strongly convex branches, but the first three of its four branches are not
twice differentiable at $0$, where the bad starts accumulate, so they are not $C^2$. Hence neither
construction is a finite maximum of uniformly strongly convex $C^2$ branches: the branches of N1
are not uniformly strongly convex and those of N2 are not all $C^2$ (the step version of N2 is
built from a countable polyhedral part, not from smooth branches); local failure for that class is
the open question of `BfgsCoverage.Article.Verification.C2StronglyConvexLocalFailure`. The last
sentence speaks of the constructed branch representations, as Chapter 13 reads its own sentence
(`C/13_L/prose/011`); that the objectives admit no other representation by finitely many uniformly
strongly convex $C^2$ branches is not claimed. -/
theorem n1_n2_comparison :
    (∀ i : Fin 4, ContDiff ℝ 2 (DEmbedding.branch i)) ∧
    (∀ i : Fin 4, ¬ ∃ μ : ℝ, 0 < μ ∧ ∀ x : Vec 2,
      (RadialHessian.matrix (DEmbedding.branch i) x - μ • (1 : Mat 2)).PosSemidef) ∧
    (∀ (i : Fin 4) (μ : ℝ), 0 < μ →
      ¬ FixedNormal.EuclideanStrongConvexOn univ μ (DEmbedding.branch i)) ∧
    (∀ x, LUniform.smoothObjective x =
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => LUniform.smoothBranch i x)) ∧
    (∃ μ : ℝ, 0 < μ ∧
      (∀ i, FixedNormal.EuclideanStrongConvexOn univ μ (LUniform.smoothBranch i)) ∧
      ∀ x : Vec 2, (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ LUniform.smoothObjective z) →
        DifferentiableAt ℝ (fderiv ℝ LUniform.smoothObjective) x →
        ∀ v, μ * sqNorm v ≤ dot v ((RadialHessian.matrix LUniform.smoothObjective x).mulVec v)) ∧
    (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch i.castSucc)) (0 : Vec 2)) ∧
    (∀ i : Fin 3, ¬ ContDiff ℝ 2 (LUniform.smoothBranch i.castSucc)) := by
  obtain ⟨-, -, hcurv, hstrong⟩ := Ch12D.not_analytic
  obtain ⟨hκ, -, -, hbranch, hmax, hhess, -, -, -⟩ := LUniform.uniformSmoothLocalFailure
  obtain ⟨hnd, hnc⟩ := Ch13L.not_four_C2_branches
  exact ⟨DEmbedding.branch_contDiff, hcurv, fun i μ hμ => (hstrong i μ hμ).1, hmax,
    ⟨LUniform.lowerConstant, hκ, fun i => (hbranch i).2.1, fun x hx hd v => ((hhess x hx hd).2 v).1⟩,
    hnd, hnc⟩

/-- Polynomial form of an affine function. -/
def affinePoly {n : ℕ} (a : Vec n) (c : ℝ) : MvPolynomial (Fin n) ℝ :=
  (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) + MvPolynomial.C c

theorem affinePoly_eval {n : ℕ} (a : Vec n) (c : ℝ) (x : Vec n) :
    MvPolynomial.eval x (affinePoly a c) = dot a x + c := by
  simp [affinePoly, dot, map_sum]

/-- A finite maximum of affine functions is a semialgebraic objective (its graph is
semialgebraic). -/
theorem max_affine_semialgebraic {n m : ℕ} (a : Fin m → Vec n) (c : Fin m → ℝ) (F : Vec n → ℝ)
    (hF : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + c i) (F x)) :
    RealAlgebraicGeometry.IsSemialgebraicObjective F := by
  apply RealAlgebraicGeometry.finite_polynomial_max_semialgebraic
    (fun i => affinePoly (a i) (c i)) F
  intro x
  simpa only [affinePoly_eval] using hF x

/-- Item `C/01_I/prose/032` (`companion/chapters/01_I.tex:115`): "This retains global failure
in the finite polyhedral and semialgebraic class." Also Item `C/01_I/prose/143`
(`companion/chapters/01_I.tex:349`): "The blanket question is not answered by calling all
semialgebraic functions safe: global failure already occurs for affine maxima."

The coercive function $\overline G(u,v)=\max\{u,-u-v/8,cu+dv,v-17\}$ of Section 12.3.1 (a variable
with its defining equation) is a finite maximum of affine functions (finite polyhedral) and a
semialgebraic objective (its graph is defined by a Boolean polynomial formula), it is coercive
with the unique minimizer $(-1,16)$, and for every $0<c_1\le1/3$, $c_1<c_2<1$ the run of the
specified strict search from $z_0$ with $H_0=I$ converges to the nonstationary point $0$
(`Ch12D.coercive_failure`, `Ch12D.coercive_minimizer`). -/
theorem n3_polyhedral_semialgebraic (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x = max (max (x 0) (-x 0 - x 1 / 8))
      (max (SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1) (x 1 - 17))) :
    (∃ (a : Fin 4 → Vec 2) (c : Fin 4 → ℝ),
      ∀ x, IsGreatest (Set.range fun i => dot (a i) x + c i) (Gbar x)) ∧
    RealAlgebraicGeometry.IsSemialgebraicObjective Gbar ∧
    Tendsto Gbar (cocompact (Vec 2)) atTop ∧ (∀ x, Gbar ![-1, 16] ≤ Gbar x) ∧
    (∀ x, Gbar x = Gbar ![-1, 16] → x = ![-1, 16]) ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential Gbar 0 ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
      ∃ R : AdmissibleBFGSRun 2 Gbar, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
        R.x 0 = BfgsCoverage.Article.Failure.seedPoint 0 ∧ R.H 0 = 1 ∧
        (∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric Gbar (R.x k) (R.H k) c₁ c₂ N =
          (some (R.α k), SeedOrbit.trialHistory (SeedOrbit.phase k))) ∧
        Tendsto R.x atTop (𝓝 0) := by
  set a : Fin 4 → Vec 2 := ![![1, 0], ![-1, -1/8], ![SeedOrbit.seedC, SeedOrbit.seedD], ![0, 1]]
    with ha
  set c : Fin 4 → ℝ := ![0, 0, 0, -17] with hc
  have hval : ∀ x : Vec 2, (fun i => dot (a i) x + c i) =
      ![x 0, -x 0 - x 1 / 8, SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1, x 1 - 17] := by
    intro x
    funext i
    fin_cases i <;> simp [ha, hc, dot, Fin.sum_univ_two] <;> ring
  have hgr : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + c i) (Gbar x) := by
    intro x
    rw [hval x, hGbar x]
    set A := x 0
    set B := -x 0 - x 1 / 8
    set C := SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1
    set D := x 1 - 17
    refine ⟨?_, ?_⟩
    · rcases max_choice (max A B) (max C D) with h | h <;> rw [h]
      · rcases max_choice A B with h' | h' <;> rw [h']
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rcases max_choice C D with h' | h' <;> rw [h']
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hcoer, hval16, hmin16, -, hns, hruns⟩ := Ch12D.coercive_failure Gbar hGbar
  obtain ⟨-, -, huniq, -⟩ := Ch12D.coercive_minimizer Gbar hGbar
  refine ⟨⟨a, c, hgr⟩, max_affine_semialgebraic a c Gbar hgr, hcoer, hmin16,
    fun x hx => huniq x (hx.trans hval16), hns, fun c₁ c₂ h1 h2 h3 h4 => ?_⟩
  obtain ⟨R, hR1, hR2, hR0, hH0, -, -, hs, -, hx, -⟩ := hruns c₁ c₂ h1 h2 h3 h4
  exact ⟨R, hR1, hR2, hR0, hH0, hs, hx⟩

/-- The branches $\frac\mu2\|x\|^2+g^Tx$ are analytic at every point. -/
theorem quadratic_branch_analytic (μ : ℝ) (g x : Vec 2) :
    AnalyticAt ℝ (fun y : Vec 2 => μ / 2 * sqNorm y + dot g y) x := by
  have hproj : ∀ i : Fin 2, AnalyticAt ℝ (fun y : Vec 2 => y i) x := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).analyticAt x
  unfold sqNorm dot
  refine (analyticAt_const.mul ?_).add ?_
  · exact Finset.analyticAt_sum _ fun i _ => (hproj i).pow 2
  · exact Finset.analyticAt_sum _ fun i _ => analyticAt_const.mul (hproj i)

/-- Item `C/01_I/prose/035` (`companion/chapters/01_I.tex:123`): "Each branch is quadratic,
analytic, and has Hessian exactly $\mu I$." For the slopes $g_0,g_1,g_2$ of the three-piece seed
and every $\mu>0$, each branch $\frac\mu2\|x\|^2+g_i^Tx$ of
$Q_\mu$ (a quadratic polynomial by its formula) is analytic at every point, $C^2$, and has Hessian
matrix exactly $\mu I$ at every point (`LQuadraticSeed.branch_hessian`). -/
theorem qmu_branches (μ : ℝ) (_hμ : 0 < μ) (i : Fin 3) :
    (∀ x, AnalyticAt ℝ
      (fun y : Vec 2 => μ / 2 * sqNorm y + dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) y)
        x) ∧
    ContDiff ℝ 2
      (fun y : Vec 2 => μ / 2 * sqNorm y + dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) y) ∧
    ∀ x, RadialHessian.matrix
      (fun y : Vec 2 => μ / 2 * sqNorm y + dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) y)
        x = μ • (1 : Mat 2) :=
  ⟨fun x => quadratic_branch_analytic μ _ x, LQuadraticSeed.branch_contDiff μ i,
    LQuadraticSeed.branch_hessian μ i⟩

/-- Item `C/01_I/prose/037` (`companion/chapters/01_I.tex:123`): "This is global failure, and
is consistent with local convergence near the true minimizer."

For every $\mu>0$: the runs of `L:thm:global` converge to the vertex $0$, while the true minimizer
$x_*$ of $Q_\mu$ is not $0$ (global failure), and $Q_\mu$, a convex quadratic plus a finite
maximum of linear functions with the unique minimizer $x_*$, has a local convergence basin at
$x_*$: for every open $U\ni x_*$ some $\varepsilon>0$, chosen before the run, gives
$x_k\in U$, $Q_\mu(x_k)\to Q_\mu(x_*)$ and $x_k\to x_*$ for every admissible run with
$Q_\mu(x_0)\le Q_\mu(x_*)+\varepsilon$ (the article's smooth-plus-polyhedral case of
Corollary `art:plq`, `BfgsCoverage.Article.Local.loss_plus_polyhedral_penalty`). -/
theorem qmu_local_basin (μ : ℝ) (hμ : 0 < μ) :
    LQuadraticSeed.minimizer μ ≠ 0 ∧
    ∀ U : Set (Vec 2), IsOpen U → LQuadraticSeed.minimizer μ ∈ U →
      ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
        LQuadraticSeed.objective μ (R.x 0) ≤
            LQuadraticSeed.objective μ (LQuadraticSeed.minimizer μ) + ε →
          (∀ k, R.x k ∈ U) ∧
          Tendsto (fun k => LQuadraticSeed.objective μ (R.x k)) atTop
            (𝓝 (LQuadraticSeed.objective μ (LQuadraticSeed.minimizer μ))) ∧
          Tendsto R.x atTop (𝓝 (LQuadraticSeed.minimizer μ)) := by
  refine ⟨LQuadraticSeed.minimizer_ne_zero hμ, ?_⟩
  have hloss : ConvexOn ℝ univ (fun x : Vec 2 => μ / 2 * sqNorm x) := by
    have h := (BfgsCoverage.Article.Local.sqNorm_convex (n := 2)).smul
      (by positivity : (0 : ℝ) ≤ μ / 2)
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  have hcd : ContDiff ℝ 2 (fun x : Vec 2 => μ / 2 * sqNorm x) := by
    unfold sqNorm
    exact contDiff_const.mul (ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2)
  have hloss_s : CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => μ / 2 * sqNorm x) :=
    ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ hcd.contDiffOn
  have hφ : ∀ x : Vec 2, IsGreatest
      (Set.range fun j => dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) x + 0)
      (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x) := by
    intro x
    simp only [add_zero]
    refine ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := LQuadraticSeed.objective_eq_branch μ x
      have hb : LQuadraticSeed.branch μ i x =
          μ / 2 * sqNorm x + dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x := rfl
      have hq := (BfgsCoverage.Article.LowerCurvature.quadratic_def μ x).1
      exact ⟨i, by linarith⟩
    · rintro _ ⟨j, rfl⟩
      exact LQuadraticSeed.seed_branch_le j x
  have hFdef : ∀ x, LQuadraticSeed.objective μ x =
      μ / 2 * sqNorm x + SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x :=
    fun x => (BfgsCoverage.Article.LowerCurvature.quadratic_def μ x).1
  exact BfgsCoverage.Article.Local.loss_plus_polyhedral_penalty (fun x : Vec 2 => μ / 2 * sqNorm x)
    (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD) (LQuadraticSeed.objective μ) hloss
    hloss_s (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD) (fun _ => 0) hφ hFdef
    (LQuadraticSeed.minimizer μ) (LQuadraticSeed.objective_minimum hμ)
    (fun x hx => LQuadraticSeed.objective_unique_minimum hμ hx)

/-! ## Section 1.3: general positive mechanisms (P1-P3) -/

open TransportedCertificate in
/-- Value convergence from band conditions in which visibility is required only at the first
points of small eligible pairs (general form: transport factor $1+Ld$, field PSD at the
differentiable band points). If the values stalled at a level above $F(x_*)$, all iterates would
lie in one band $K_\eta$. Restricted to the first points of the small eligible pairs of that band,
the pairwise hypotheses form a `BandCertificate`; a tail of the run consists of such points (its
accepted pairs are eligible, `accepted_pair_eligible`, and $d_k\to0$), which contradicts the
certificate (`band_certificate_incompatible`, the argument of Theorem 3.1). Proof by the
independent reviewer of this module (15 October 2026). -/
theorem pairwise_visibility_values {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (hK : IsCompact K) (hxK : ∀ k, R.x k ∈ K) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x)
    (hcert : ∀ η : ℝ, 0 < η → (positiveBand F K (F xstar) η).Nonempty →
      ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ L ∧ 0 < δ ∧
        (∀ x ∈ positiveBand F K (F xstar) η, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        ∀ x z g h, x ∈ positiveBand F K (F xstar) η → z ∈ positiveBand F K (F xstar) η →
          EligiblePair F R.c₁ R.c₂ x z g h → pairDecrease x z g ≤ δ →
          m ≤ metricEnergy (W x) g ∧
          metricEnergy (W z) (h - g) ≤ C * pairCurvature x z g h ∧
          ((1 + L * pairDecrease x z g) •
            (stepProjector (pairStep x z) * W x * stepProjector (pairStep x z)) -
            stepProjector (pairStep x z) * W z * stepProjector (pairStep x z)).PosSemidef) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
  have hsum := R.summable_predicted_decreases_of_lower_bound (F xstar) (fun k => hmin (R.x k))
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_set K hK hxK
  have hbounded : BddBelow (Set.range (fun k => F (R.x k))) := by
    refine ⟨F xstar, ?_⟩
    rintro z ⟨k, rfl⟩
    exact hmin _
  let ℓ := ⨅ k, F (R.x k)
  have hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) :=
    tendsto_atTop_ciInf R.objective_antitone hbounded
  have hfloor : F xstar ≤ ℓ := le_ciInf (fun k => hmin (R.x k))
  have hlevels : ∀ k, ℓ ≤ F (R.x k) := fun k => ciInf_le hbounded k
  have hvalue : ℓ = F xstar := by
    by_contra hne
    have hpos : F xstar < ℓ := lt_of_le_of_ne hfloor (Ne.symm hne)
    let η := (ℓ - F xstar) / 2
    have hη : 0 < η := by dsimp only [η]; linarith
    have hband : ∀ k, R.x k ∈ positiveBand F K (F xstar) η := by
      intro k
      refine ⟨hxK k, ?_⟩
      dsimp only [η]
      linarith [hlevels k]
    obtain ⟨W, m, C, L, δ, hm, hL, hδ, hpsd, hpair⟩ := hcert η hη ⟨R.x 0, hband 0⟩
    -- the first points of the small eligible pairs of the band
    let K' : Set (Vec n) := {x | x ∈ K ∧ ∃ z g h, z ∈ positiveBand F K (F xstar) η ∧
      EligiblePair F R.c₁ R.c₂ x z g h ∧ pairDecrease x z g ≤ δ}
    have hsub : ∀ x, x ∈ positiveBand F K' (F xstar) η → x ∈ positiveBand F K (F xstar) η :=
      fun x hx => ⟨hx.1.1, hx.2⟩
    let Cert : BandCertificate F K' (F xstar) R.c₁ R.c₂ η :=
      { W := W, m := m, C := C, L := L, δ := δ, m_pos := hm, L_nonneg := hL, delta_pos := hδ
        positive_semidefinite := fun x hx hd => hpsd x (hsub x hx) hd
        visibility := fun x hx g hgx => by
          obtain ⟨-, z, g', h, hz, hel, hd⟩ := hx.1
          have hgg : g' = g := AffineProjection.gradientFunctional_injective (hel.gradient_x.unique hgx)
          subst hgg
          exact (hpair x z g' h (hsub x hx) hz hel hd).1
        secant := fun x z g h hx hz hel hd => (hpair x z g h (hsub x hx) (hsub z hz) hel hd).2.1
        transport := fun x z g h hx hz hel hd => (hpair x z g h (hsub x hx) (hsub z hz) hel hd).2.2 }
    have hevent : ∀ᶠ k in atTop, R.d k < δ :=
      hsum.tendsto_atTop_zero.eventually (gt_mem_nhds hδ)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
    have hband' : ∀ k, R.x (J + k) ∈ positiveBand F K' (F xstar) η := by
      intro k
      refine ⟨⟨hxK (J + k), R.x (J + k + 1), R.g (J + k), R.g (J + k + 1), hband (J + k + 1),
        R.accepted_pair_eligible (J + k), ?_⟩, (hband (J + k)).2⟩
      rw [R.accepted_pair_decrease]
      exact (hJ (J + k) (Nat.le_add_right J k)).le
    exact (R.shift J).band_certificate_incompatible Cert hband'
      (fun k => (hJ (J + k) (Nat.le_add_right J k)).le)
      G hG (fun k => hg (J + k)) (R.shift_summable_d hsum J)
  simpa only [hvalue] using hlim

/-- Item `C/01_I/prose/041` (`companion/chapters/01_I.tex:141-149`), the P1 summary, with its
displays Item `C/01_I/disp/010` (`companion/chapters/01_I.tex:143`) and Item
`C/01_I/disp/011` (`companion/chapters/01_I.tex:145`).

"On each compact positive objective band, it suffices that a finite-valued PSD field $W$ satisfy
\[ g^TW(x)g\ge m>0,\qquad y^TW(z)y\le Ct, \]
\[ \Pi_sW(z)\Pi_s\preceq\Pi_sW(x)\Pi_s, \]
for every eligible pair with sufficiently small $d$. The latter two constants and the field may
depend on the band and on the fixed line-search parameters. No continuity, uniform boundedness, or
positive definiteness of $W$ is required. Then every admissible run on the compact sublevel has
value and solution-set convergence; uniqueness gives iterate convergence."

Literal reading: "for every eligible pair with sufficiently small $d$" governs all three
conditions, so the visibility $g^TW(x)g\ge m$ ($g=\nabla F(x)$ at the first endpoint, line 137) is
required only at the first points $x$ of the eligible pairs $x,z$ of the band with $d\le\delta$,
not at every differentiable point of the band as in Theorem 3.1 (`C/03_T/theorem/001`). The
conclusions still hold: the argument of Theorem 3.1 uses visibility only at the iterates of a tail
of the run, which are first points of small eligible pairs (`pairwise_visibility_values`).
Setting: $F$ finite convex (a field of the run), $x_*$ a minimizer, $K=\{F\le b\}$ compact, the
bands $K_\eta=\{x\in K:F(x)\ge F(x_*)+\eta\}$, $\eta>0$; each nonempty band has its own field $W$
(real entries, so finite-valued; no continuity, bound or definiteness), PSD at every point of the
band, and its own constants $m>0$, $C$, $\delta>0$; (T) is the summary's normalized form
($A\preceq B$ is `(B - A).PosSemidef`, $\Pi_s$ = `stepProjector s`); $s=z-x$, $y=h-g$, $d=-g^Ts$,
$t=y^Ts$; eligibility is for the fixed constants $c_1,c_2$ of the runs; "every admissible run on
the compact sublevel": every run with these constants and $F(x_0)\le b$; the distance is Euclidean
(`euclideanSolutionDistance`). -/
theorem pairwise_certificate_convergence {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hK : IsCompact {x | F x ≤ b}) (c₁ c₂ : ℝ)
    (hcert : ∀ η : ℝ, 0 < η → {x | F x ≤ b ∧ F x ≥ F xstar + η}.Nonempty →
      ∃ (W : Vec n → Mat n) (m C δ : ℝ), 0 < m ∧ 0 < δ ∧
        (∀ x ∈ {x | F x ≤ b ∧ F x ≥ F xstar + η}, (W x).PosSemidef) ∧
        ∀ x ∈ {x | F x ≤ b ∧ F x ≥ F xstar + η}, ∀ z ∈ {x | F x ≤ b ∧ F x ≥ F xstar + η},
          ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
            -dot g (z - x) ≤ δ →
            dot g (W x *ᵥ g) ≥ m ∧
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x) ∧
            (TransportedCertificate.stepProjector (z - x) * W x *
                TransportedCertificate.stepProjector (z - x) -
              TransportedCertificate.stepProjector (z - x) * W z *
                TransportedCertificate.stepProjector (z - x)).PosSemidef) :
    ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ → F (R.x 0) ≤ b →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
        ((∀ y, F y = F xstar → y = xstar) → Tendsto R.x atTop (𝓝 xstar)) := by
  rintro R rfl rfl hx0
  have hxK : ∀ k, F (R.x k) ≤ b := fun k => (R.objective_antitone (Nat.zero_le k)).trans hx0
  have hval := pairwise_visibility_values R {x | F x ≤ b} hK hxK xstar hmin
    (fun η hη hne => by
      obtain ⟨W, m, C, δ, hm, hδ, hpsd, hpair⟩ := hcert η hη hne
      refine ⟨W, m, C, 0, δ, hm, le_rfl, hδ, fun x hx _ => hpsd x hx, ?_⟩
      intro x z g h hx hz hel hd
      obtain ⟨hV, hS, hT⟩ := hpair x hx z hz g h hel hd
      refine ⟨hV, hS, ?_⟩
      simpa only [zero_mul, add_zero, one_smul, TransportedCertificate.pairStep] using hT)
  obtain ⟨hdist, huniq⟩ := compact_value_distance F R.convex xstar hmin b hK R.x hxK hval
  exact ⟨hval, hdist, huniq⟩

/-- Item `C/01_I/prose/055` (`companion/chapters/01_I.tex:169`): "If a fixed subspace $S$
satisfies $\|P_Sy_k\|^2\le L_Sy_k^Ts_k$, the actual update gives
$\operatorname{tr}(P_SB_k)=O(k)$ for $B_k=H_k^{-1}$." ("for $B_k=H_k^{-1}$" added on 15 October
2026, wording point W43.)

For every admissible run, every subspace $S$ of Euclidean $\mathbb R^n$ with orthogonal projection
$P_S$ (the matrix `PS`, `hPS`) and every $L_S$ with $\|P_Sy_k\|^2\le L_St_k$ for all $k$:
$\operatorname{tr}(P_SB_k)\le\operatorname{tr}(P_SB_0)+L_Sk$ for every $k$ (the trace grows at most
linearly; it is derived from the update, Chapter 2's display `C/02_M/disp/035`). -/
theorem smooth_subspace_trace_linear {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (PS : Mat n)
    (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (LS : ℝ) (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k) :
    ∀ k : ℕ, (PS * R.hessian k).trace ≤ (PS * R.hessian 0).trace + LS * k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨heq, hle⟩ := Ch02M.projection_trace_step R S PS hPS LS k (hsmooth k)
    rw [heq]
    push_cast
    linarith

/-! ## Section 1.6: shared algebra and quantitative record -/

/-- Item `C/01_I/disp/019` (`companion/chapters/01_I.tex:301-304`), with line 299 ("The
principal-minor inequality is proved once in Chapter M"):
\[ e_j(H_{k+1})\le\frac{\|y_k\|^2}{\beta_k^2q_k}e_{j+1}(H_k)+\frac{\alpha_k}{\beta_k}e_j(H_k),\quad
   q_k=g_k^TH_kg_k,\quad\beta_k=\frac{y_k^Ts_k}{d_k}. \]
Along every admissible run, for every $k$ and $1\le j\le n$ ($e_j$ = `principalSum`, the sum of
the $j\times j$ principal minors, the $j$th elementary symmetric polynomial of the eigenvalues of
the positive definite $H_k$; $e_{n+1}=0$), with $q_k$ and $\beta_k=t_k/d_k$ as variables with their
defining equations ($d_k=\alpha_kq_k$). Chapter 2 writes $\beta=-y^THg/q$
(Theorem `M:hierarchy`, `Ch02M.hierarchy`); along a run the two agree. -/
theorem principal_minor_run {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ)
    (q β : ℝ) (hq : q = dot (R.g k) (R.H k *ᵥ R.g k))
    (hβ : β = dot (R.gradientChange k) (R.displacement k) / R.d k) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n →
      principalSum (R.H (k + 1)) j ≤
        sqNorm (R.gradientChange k) / (β ^ 2 * q) * principalSum (R.H k) (j + 1) +
          R.α k / β * principalSum (R.H k) j := by
  have hqk : R.q k = q := by rw [hq]; rfl
  have hqpos : 0 < q := hqk ▸ R.q_pos k
  have hdk : R.d k = R.α k * q := by rw [← hqk]; rfl
  have hα := R.alpha_pos k
  have ht : dot (R.gradientChange k) (R.displacement k) =
      -R.α k * dot (R.gradientChange k) (R.H k *ᵥ R.g k) := by
    show dot (R.gradientChange k) (-R.α k • (R.H k *ᵥ R.g k)) = _
    rw [dot_smul_right]
  have hβ' : β = -dot (R.gradientChange k) (R.H k *ᵥ R.g k) / q := by
    rw [hβ, hdk, ht]
    field_simp
    ring
  have hβpos : 0 < β := by
    rw [hβ]
    exact div_pos (R.curvature_pos k) (R.d_pos k)
  exact Ch02M.hierarchy (R.H k) (R.H (k + 1)) (R.g k) (R.gradientChange k) (R.displacement k)
    (R.α k) q β (R.positive_definite k) rfl hα hq hqpos hβ' hβpos (R.update k)

/-- Item `C/01_I/prose/116` (`companion/chapters/01_I.tex:310`): "The former $\liminf q_k=0$
and $\Omega(N^2)$ headlines are retired as main results. They remain consequences used by older
proofs."

Both remain consequences of the recorded reciprocal theorems (Chapter 2). With bounded gradients
and $d_k\to0$ (the hypotheses of Theorem `M:average`): $q_k<\varepsilon$ for infinitely many $k$,
for every $\varepsilon>0$; since $q_k>0$, this is $\liminf q_k=0$. With bounded gradients and
$\sum d_k<\infty$ (Theorem `M:superquadratic`): for every $c$, eventually
$\sum_{k<N}q_k^{-1}\ge cN^2$, in particular $\sum_{k<N}q_k^{-1}=\Omega(N^2)$. -/
theorem retired_headlines {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (∀ k, 0 < R.q k) ∧
    ((∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) → Tendsto R.d atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, R.q k < ε) ∧
    ((∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) → Summable R.d →
      ∀ c : ℝ, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ ∑ k ∈ Finset.range N, (R.q k)⁻¹) := by
  refine ⟨R.q_pos, fun hbdd hd ε hε => ?_, fun hbdd hs c => ?_⟩
  · rw [Filter.frequently_atTop]
    by_contra hcon
    push_neg at hcon
    obtain ⟨K, hK⟩ := hcon
    have havg := (Ch02M.average R hbdd hd).2
    set C := ∑ k ∈ Finset.range K, (R.q k)⁻¹ with hCdef
    have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => (inv_pos.mpr (R.q_pos k)).le
    obtain ⟨N, hN, hNK⟩ :=
      ((havg.eventually_gt_atTop (C + 1 / ε)).and (eventually_ge_atTop (K + 1))).exists
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hsplit : ∑ k ∈ Finset.range N, (R.q k)⁻¹ = C + ∑ k ∈ Finset.Ico K N, (R.q k)⁻¹ :=
      (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    have htail : ∑ k ∈ Finset.Ico K N, (R.q k)⁻¹ ≤ (N : ℝ) * (1 / ε) := by
      calc ∑ k ∈ Finset.Ico K N, (R.q k)⁻¹ ≤ ∑ k ∈ Finset.Ico K N, (1 / ε) :=
            Finset.sum_le_sum fun k hk => by
              rw [one_div]
              exact inv_anti₀ hε (hK k (Finset.mem_Ico.1 hk).1)
        _ = ((N - K : ℕ) : ℝ) * (1 / ε) := by simp
        _ ≤ (N : ℝ) * (1 / ε) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le N K
    have hbound : 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ C + 1 / ε := by
      rw [hsplit]
      have hNpos : (0 : ℝ) < N := by linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hNpos]
      nlinarith
    linarith
  · have hg := BfgsCoverage.Article.Energy.superquadratic_growth R hbdd hs
    filter_upwards [hg.eventually_ge_atTop c, eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      positivity
    rwa [le_div_iff₀ hNpos] at hN

/-! ## Section 1.4: P5 and the explicit supersession -/

/-- One compact sublevel $\{F\le b\}$ with $b>F(x_*)$ for some point $x_*$ (for example a
minimizer) makes every sublevel of a finite convex function compact. -/
theorem sublevels_compact_of_one {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (b : ℝ) (hb : F xstar < b) (hK : IsCompact {x | F x ≤ b})
    (t : ℝ) : IsCompact {x | F x ≤ t} := by
  have hc : Continuous F := convex_continuous hF
  have hclosed : IsClosed {x | F x ≤ t} := isClosed_le hc continuous_const
  rcases le_or_lt t b with htb | htb
  · exact hK.of_isClosed_subset hclosed fun x (hx : F x ≤ t) => (le_trans hx htb : F x ≤ b)
  · set lam := (b - F xstar) / (t - F xstar) with hlam
    have htF : 0 < t - F xstar := by linarith
    have hlam0 : 0 < lam := div_pos (by linarith) htF
    have hlam1 : lam ≤ 1 := (div_le_one htF).mpr (by linarith)
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall xstar
    apply Metric.isCompact_of_isClosed_isBounded hclosed
    rw [Metric.isBounded_iff_subset_closedBall xstar]
    refine ⟨r / lam, fun x (hx : F x ≤ t) => ?_⟩
    have hy : F (xstar + lam • (x - xstar)) ≤ b := by
      have hconv := hF.2 (mem_univ xstar) (mem_univ x) (by linarith : (0 : ℝ) ≤ 1 - lam)
        hlam0.le (by ring : (1 - lam) + lam = 1)
      have he : (1 - lam) • xstar + lam • x = xstar + lam • (x - xstar) := by
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [he, smul_eq_mul, smul_eq_mul] at hconv
      have hlt : lam * (t - F xstar) = b - F xstar := by
        rw [hlam]
        field_simp
      nlinarith
    have hd := hr hy
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hlam0.le] at hd
    rw [Metric.mem_closedBall, dist_eq_norm, le_div_iff₀ hlam0]
    linarith

open AffineCriticalObjective in
/-- Item `C/01_I/prose/074` (`companion/chapters/01_I.tex:218-220`), anchor "Let
\(F:\mathbb R^2\to\mathbb R\) be finite convex": "Let $F:\mathbb R^2\to\mathbb R$ be finite convex,
have an attained minimum and a compact sublevel above the minimum, and have strictly convex
positive sublevels. Away from affine-critical points, assume either local convex $C^2$ smoothness
or a local maximum of two convex $C^2$ branches whose active gradients are linearly independent.
Then every infinite admissible run has an affine-critical cluster point." ("above the minimum"
added on 15 October 2026, wording point W40.)

The hypotheses are read globally (every positive sublevel strictly convex: its boundary contains
no nontrivial segment; the regular-switching alternative of Chapter 9 at every non-affine-critical
point), and the conclusion is for every admissible run, wherever it starts: the run lies in the
sublevel $\{F\le F(x_0)\}$, compact because one sublevel above $F_*$ is
(`sublevels_compact_of_one`), and Theorem `C:thm:cluster` (`Ch09C.cluster`) applies to the larger
of the two levels. -/
theorem p5_cluster (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (hK : ∃ b, Fstar < b ∧ IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    ∀ R : AdmissibleBFGSRun 2 F, ∃ p, MapClusterPt p atTop R.x ∧ IsAffineCritical F p := by
  intro R
  obtain ⟨b, hb, hKb⟩ := hK
  obtain ⟨⟨xs, hxs⟩, hlow⟩ := hFstar
  have hb' : F xs < b := hxs ▸ hb
  have hK' : IsCompact {x | F x ≤ max b (F (R.x 0))} :=
    sublevels_compact_of_one hF xs b hb' hKb _
  exact Ch09C.cluster F hF Fstar ⟨⟨xs, hxs⟩, hlow⟩ (max b (F (R.x 0)))
    (lt_of_lt_of_le hb (le_max_left _ _)) hK' (fun t ht _ => hstrict t ht)
    (fun p _ hp => hreg p hp) R (show F (R.x 0) ≤ max b (F (R.x 0)) from le_max_right _ _)

/-- Item `C/01_I/prose/082` (`companion/chapters/01_I.tex:230-234`), anchor "The older theorem
for", with its display Item `C/01_I/disp/016` (`companion/chapters/01_I.tex:232`): "The older
theorem for
\[ F(u,v)=\max\{a(u)+pv,b(u)-qv\},\qquad p,q>0, \]
with convex $C^2$ profiles, coercive $\phi=(qa+pb)/(p+q)$ having unique minimizer $u_*$, and
$a'',b''>0$ off $u_*$, is a corollary of P5, not an independent strongest theorem."

The older theorem, with both conclusions: $F$ has the unique minimizer
$x_*=(u_*,(b(u_*)-a(u_*))/(p+q))$; every admissible run converges to it (values and iterates); and
for every neighbourhood $U$ of $x_*$ some $\varepsilon>0$, chosen before the run, gives
$x_k\in U$ and convergence for every run with $F(x_0)\le F(x_*)+\varepsilon$ (the local result).
$\phi$ and $F$ are variables with their defining equations; coercivity of $\phi$ is not needed
(`_hcoer`), only the unique minimizer. The proof is the corollary: the library's
`RidgeSupersession.fullBFGS_convergence` applies the planar theorem (P5,
`AdmissibleBFGSRun.planar_convergence_on_sublevel`) after deriving its hypotheses, and
`localized_fullBFGS_convergence` localizes it. -/
theorem ridge_supersession (a b : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    (φ : ℝ → ℝ) (hφ : ∀ u, φ u = (q * a u + p * b u) / (p + q))
    (_hcoer : Tendsto φ (cocompact ℝ) atTop) (ustar : ℝ) (hmin : ∀ u, φ ustar ≤ φ u)
    (huniq : ∀ u, φ u = φ ustar → u = ustar)
    (ha'' : ∀ u, u ≠ ustar → 0 < deriv (deriv a) u) (hb'' : ∀ u, u ≠ ustar → 0 < deriv (deriv b) u)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (a (x 0) + p * x 1) (b (x 0) - q * x 1)) :
    let xstar : Vec 2 := ![ustar, (b ustar - a ustar) / (p + q)]
    (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      (∀ R : AdmissibleBFGSRun 2 F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar)) ∧
      ∀ U ∈ 𝓝 xstar, ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) ≤ F xstar + ε →
        (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  intro xstar
  have hFe : F = RidgeSupersession.objective a b p q := funext hF
  have hφe : φ = RidgeSupersession.profile a b p q := funext hφ
  subst hFe hφe
  have hx : xstar = RidgeSupersession.optimizer a b p q ustar := rfl
  have hval : RidgeSupersession.objective a b p q xstar = RidgeSupersession.profile a b p q ustar :=
    RidgeSupersession.objective_optimizer (add_pos hp hq).ne' ustar
  refine ⟨fun x => RidgeSupersession.optimizer_minimum hp hq hmin x,
    fun x hx' => RidgeSupersession.optimizer_unique hp hq hmin huniq x hx', fun R => ?_,
    fun U hU => ?_⟩
  · rw [hval]
    exact RidgeSupersession.fullBFGS_convergence ha hb hca hcb hp hq hmin huniq ha'' hb'' R
  · rw [hval]
    exact RidgeSupersession.localized_fullBFGS_convergence ha hb hca hcb hp hq hmin huniq ha'' hb''
      U hU

/-- Item `C/01_I/prose/083` (`companion/chapters/01_I.tex:236`), the proof of the explicit
supersession ("Here is the implication."), its determinant step: with $\phi=(qa+pb)/(p+q)$, at every $u$ the determinant of the
gradients $(a'(u),p)$ and $(b'(u),-q)$ of the two branches is
$-qa'(u)-pb'(u)=-(p+q)\phi'(u)$; under the hypotheses of `ridge_supersession` it vanishes only at
$u_*$, and a tie point with $u=u_*$ is the optimizer. -/
theorem ridge_tie_determinant (a b : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    (ustar : ℝ) (hmin : ∀ u, RidgeSupersession.profile a b p q ustar ≤ RidgeSupersession.profile a b p q u)
    (huniq : ∀ u, RidgeSupersession.profile a b p q u = RidgeSupersession.profile a b p q ustar →
      u = ustar) :
    (∀ u, deriv a u * (-q) - p * deriv b u = -q * deriv a u - p * deriv b u ∧
      -q * deriv a u - p * deriv b u = -(p + q) * deriv (RidgeSupersession.profile a b p q) u) ∧
    (∀ u, deriv (RidgeSupersession.profile a b p q) u = 0 ↔ u = ustar) ∧
    ∀ v : ℝ, a ustar + p * v = b ustar - q * v → (![ustar, v] : Vec 2) =
      ![ustar, (b ustar - a ustar) / (p + q)] := by
  have hA := ha.differentiable (by norm_num)
  have hB := hb.differentiable (by norm_num)
  have hpq : p + q ≠ 0 := (add_pos hp hq).ne'
  refine ⟨fun u => ⟨by ring, ?_⟩, fun u => ⟨fun h => ?_, fun h => ?_⟩, fun v hv => ?_⟩
  · rw [(RidgeSupersession.profile_hasDerivAt hA hB p q u).deriv]
    field_simp
    ring
  · exact RidgeSupersession.profile_deriv_zero_implies_optimizer hA hB hca hcb hp hq hmin huniq u h
  · subst h
    have hloc : IsLocalMin (RidgeSupersession.profile a b p q) u :=
      Filter.Eventually.of_forall hmin
    exact hloc.deriv_eq_zero
  · have hv' : v = (b ustar - a ustar) / (p + q) := by
      field_simp
      linarith
    rw [hv']

/-! ## Section 1.5: the noncompact homogeneous theory -/

/-- Item `C/01_I/prose/110` (`companion/chapters/01_I.tex:289`): "A compact-level certificate
theorem cannot replace these noncompact statements."

For the finite convex degree-one homogeneous $F(u,v)=|v|$ (bounded below, minimum $0$), no
sublevel $\{F\le b\}$, $b\ge0$, is compact, so the compact-level theorems (which assume a compact
sublevel $\{F\le b\}$, $b>F_*$) do not apply; yet Theorem 7.A gives $F(x_k)\to0$ for every
admissible run (`AdmissibleBFGSRun.homogeneous_bounded_below_convergence`), and admissible runs
exist (`BfgsCoverage.Article.Master.absVRun`). -/
theorem compact_theorem_cannot_replace :
    ConvexOn ℝ univ BfgsCoverage.Article.Master.absV ∧
      Homogeneous.PositiveDegreeOne BfgsCoverage.Article.Master.absV ∧
      (∀ x, BfgsCoverage.Article.Master.absV 0 ≤ BfgsCoverage.Article.Master.absV x) ∧
      (∀ b : ℝ, 0 ≤ b → ¬ IsCompact {x | BfgsCoverage.Article.Master.absV x ≤ b}) ∧
      (∀ R : AdmissibleBFGSRun 2 BfgsCoverage.Article.Master.absV,
        Tendsto (fun k => BfgsCoverage.Article.Master.absV (R.x k)) atTop (𝓝 0)) ∧
      Nonempty (AdmissibleBFGSRun 2 BfgsCoverage.Article.Master.absV) := by
  have hhom : Homogeneous.PositiveDegreeOne BfgsCoverage.Article.Master.absV := by
    intro t ht x
    simp [BfgsCoverage.Article.Master.absV, abs_mul, abs_of_nonneg ht]
  refine ⟨BfgsCoverage.Article.Master.absV_convex, hhom, fun x => ?_, fun b hb hK => ?_,
    fun R => (R.homogeneous_bounded_below_convergence hhom 0 fun x => abs_nonneg _).2.2,
    ⟨BfgsCoverage.Article.Master.absVRun 1 1 one_pos⟩⟩
  · simp [BfgsCoverage.Article.Master.absV]
  · obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    have hmem : (![r + 1, 0] : Vec 2) ∈ {x | BfgsCoverage.Article.Master.absV x ≤ b} := by
      simp [BfgsCoverage.Article.Master.absV, hb]
    have hd := hr hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hd
    have h0 : |(![r + 1, 0] : Vec 2) 0| ≤ ‖(![r + 1, 0] : Vec 2)‖ := by
      have := norm_le_pi_norm (![r + 1, 0] : Vec 2) 0
      rwa [Real.norm_eq_abs] at this
    simp only [Matrix.cons_val_zero] at h0
    linarith [le_abs_self (r + 1)]

/-! ## Section 1.7: geometric findings -/

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/01_I/prose/127` (`companion/chapters/01_I.tex:333`): "Thus only finitely many
affine-critical values occur, giving no false affine criticality below a sufficiently low
threshold."

For a finite convex semialgebraic $F$ (Chapter 8, `Ch08A.finitely_many_values`,
`Ch08A.low_level_gap`): $F$ takes finitely many values on the affine-critical set
$\mathcal C_{\rm aff}=\{p:0\in\operatorname{aff}\partial F(p)\}$; and when $F$ attains its minimum
$F_*$ (the setting of Proposition `A:semialgebraic`), some $\varepsilon>0$ makes every
affine-critical point with $F(p)<F_*+\varepsilon$ stationary ($0\in\partial F(p)$, i.e. a
minimizer): no false affine criticality below $F_*+\varepsilon$. -/
theorem semialgebraic_values_gap {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (F '' {x | IsAffineCritical F x}).Finite ∧
    ∀ Fstar : ℝ, IsLeast (Set.range F) Fstar → ∃ ε : ℝ, 0 < ε ∧ ∀ p : Vec n, F p < Fstar + ε →
      (0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) → (0 : Vec n) ∈ subdifferential F p :=
  ⟨(Ch08A.finitely_many_values hF hsa).2.2, fun Fstar h => Ch08A.low_level_gap hF hsa Fstar h⟩

/-! ## Section 1.8: verification and unresolved boundaries (open questions, line 347)

"The remaining central gaps are: arbitrary-dimensional rotating-normal smooth-max geometry; the
general local theorem for finite uniformly strongly convex $C^2$ branches without the recorded
nondegeneracy/geometric assumptions; generic or positive-measure failure; other fixed line-search
implementations; arbitrary nonunique solution-set iterate convergence; noncompact high-rank
homogeneous zero-value iterates; and sharp rates or universal matrix asymptotics."

The precise gaps are stated below without proof (status `OPEN`); the first and the sixth are the
open questions of Chapters 8 and 7 (`Ch08A.GeneralDimensionalConjecture`,
`Ch07H.ZeroValueIterateQuestion`). -/

/-- Item `C/01_I/prose/137` (`companion/chapters/01_I.tex:347`), OPEN (stated without proof):
"the general local theorem for finite uniformly strongly convex $C^2$ branches without the
recorded nondegeneracy/geometric assumptions."

For every finite maximum $F$ of $C^2$ branches that are all $\kappa$-strongly convex (Euclidean),
every minimizer $x_*$ and every pair $0<c_1<c_2<1$, there is $\varepsilon>0$ such that every
admissible run with these constants (any $H_0\succ0$) starting with $F(x_0)<F(x_*)+\varepsilon$
converges to $x_*$. The article's open question `C2StronglyConvexLocalFailure` (a local failure in
this class, for the specified search with $H_0=I$) would refute it
(`c2_failure_refutes_local_theorem`). -/
def C2StronglyConvexLocalTheorem : Prop :=
  ∀ (n m : ℕ) (hm : 0 < m) (f : Fin m → Vec n → ℝ) (κ : ℝ), 0 < κ →
    (∀ i, ContDiff ℝ 2 (f i) ∧ FixedNormal.EuclideanStrongConvexOn univ κ (f i)) →
    let F : Vec n → ℝ := fun x =>
      (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => f i x)
    ∀ xstar : Vec n, (∀ x, F xstar ≤ F x) → ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → c₂ < 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ →
        F (R.x 0) < F xstar + ε → Tendsto R.x atTop (𝓝 xstar)

/-- The local failure in the class of uniformly strongly convex $C^2$ maxima (the article's open
question, `BfgsCoverage.Article.Verification.C2StronglyConvexLocalFailure`) and the general local
theorem `C2StronglyConvexLocalTheorem` exclude each other: the two open statements are
complementary. -/
theorem c2_failure_refutes_local_theorem :
    BfgsCoverage.Article.Verification.C2StronglyConvexLocalFailure →
      ¬ C2StronglyConvexLocalTheorem := by
  intro hfail hthm
  obtain ⟨n, m, hm, f, κ, hκ, hf, xstar, c₁, c₂, R, hmin, hc₁, hc₁₂, hc₂, hstart, hR⟩ := hfail
  obtain ⟨ε, hε, hconv⟩ := hthm n m hm f κ hκ hf xstar hmin c₁ c₂ hc₁ hc₁₂ hc₂
  have hcont : Continuous fun x : Vec n =>
      (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => f i x) :=
    Continuous.finset_sup'_apply _ fun i _ => (hf i).1.continuous
  have hval := (hcont.tendsto xstar).comp hstart
  obtain ⟨ℓ, hℓ⟩ := (hval.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))).exists
  obtain ⟨-, h1, h2, -, hnot⟩ := hR ℓ
  exact hnot (hconv (R ℓ) h1 h2 hℓ)

/-- The failing starts: the starting points $x_0$ from which the specified unit-first search
(`NonStrictLineSearch.fromMetric`, some trial budget at each step) with $H_0=I$ and the constants
$c_1,c_2$ produces an infinite admissible run on $F$ whose values do not tend to $F(x_*)$. -/
def failingStarts {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (c₁ c₂ : ℝ) : Set (Vec n) :=
  {x₀ | ∃ R : AdmissibleBFGSRun n F, R.x 0 = x₀ ∧ R.H 0 = 1 ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
    (∀ k, ∃ N : ℕ, (NonStrictLineSearch.fromMetric F (R.x k) (R.H k) c₁ c₂ N).1 = some (R.α k)) ∧
    ¬ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar))}

/-- Item `C/01_I/prose/138` (`companion/chapters/01_I.tex:347`), OPEN (stated without proof):
"generic or positive-measure failure."

Some finite convex objective with an attained minimum and some pair $0<c_1<c_2<1$ have a large set
of failing starts $S$ (`failingStarts`), in one of the two senses of the gap. Generic failure, read
topologically: $S$ is comeagre in some nonempty open set $U$ of starting points ($U\setminus S$ is
meagre), i.e. failure from a generic start of an open region. This is the weakest of the usual
readings: it follows from failure on a comeagre set of all starting points and from failure at
every point of a nonempty open set; and for sets with the Baire property it is the same as being
nonmeagre, the topological counterpart of the second sense. Positive-measure failure: $S$ has
positive Lebesgue (outer) measure. The failing starts of the constructions are countable, hence
null and meagre (`Ch12D.starts_null`). -/
def GenericOrPositiveMeasureFailure : Prop :=
  ∃ (n : ℕ) (F : Vec n → ℝ) (xstar : Vec n) (c₁ c₂ : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧
    ((∃ U : Set (Vec n), IsOpen U ∧ U.Nonempty ∧ IsMeagre (U \ failingStarts F xstar c₁ c₂)) ∨
      0 < MeasureTheory.volume (failingStarts F xstar c₁ c₂))

/-- Item `C/01_I/prose/140` (`companion/chapters/01_I.tex:347`), OPEN (stated without proof):
"arbitrary nonunique solution-set iterate convergence."

For every finite convex objective and every admissible run with a compact initial sublevel whose
values tend to the minimum value (minimizers possibly not unique), the iterates converge. (With a
unique minimizer this holds: `compact_value_distance`.) -/
def NonuniqueIterateConvergence : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (xstar : Vec n) (R : AdmissibleBFGSRun n F),
    (∀ x, F xstar ≤ F x) → IsCompact {x | F x ≤ F (R.x 0)} →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) →
    ∃ xlim : Vec n, Tendsto R.x atTop (𝓝 xlim)

/-! ## Non-vacuity -/

/-- The objective $u^2+|v|=\max\{u^2+v,u^2-v\}$ in the form of the explicit supersession
($a=b=t^2$, $p=q=1$). -/
def ridgeExample : Vec 2 → ℝ :=
  RidgeSupersession.objective (fun t => t ^ 2) (fun t => t ^ 2) 1 1

/-- The hypotheses of `ridge_supersession` hold for $a=b=t^2$, $p=q=1$ ($u^2+|v|$), and admissible
runs on this objective exist. -/
example : ∃ φ : ℝ → ℝ, (∀ u, φ u = (1 * (fun t : ℝ => t ^ 2) u + 1 * (fun t : ℝ => t ^ 2) u) / (1 + 1)) ∧
    Tendsto φ (cocompact ℝ) atTop ∧ (∀ u, φ 0 ≤ φ u) ∧ (∀ u, φ u = φ 0 → u = 0) ∧
    ContDiff ℝ 2 (fun t : ℝ => t ^ 2) ∧ ConvexOn ℝ univ (fun t : ℝ => t ^ 2) ∧
    (∀ u : ℝ, u ≠ 0 → 0 < deriv (deriv (fun t : ℝ => t ^ 2)) u) ∧
    Nonempty (AdmissibleBFGSRun 2 ridgeExample) := by
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    simp
  have hobj : ridgeExample = UnexcitedMetric.objective := by
    funext x
    simp only [ridgeExample, RidgeSupersession.objective, UnexcitedMetric.objective, one_mul]
    rw [sub_eq_add_neg, max_add_add_left, ← abs_eq_max_neg]
  refine ⟨fun u => u ^ 2, fun u => by ring, ?_, fun u => by simp [sq_nonneg],
    fun u hu => by simpa using hu, contDiff_id.pow 2, even_two.convexOn_pow, fun u _ => ?_, ?_⟩
  · have h := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp
      (tendsto_norm_cocompact_atTop (E := ℝ))
    refine h.congr fun u => ?_
    simp [Real.norm_eq_abs, sq_abs]
  · rw [hd]
    have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 u := by
      simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
    rw [h2.deriv]
    norm_num
  · rw [hobj]
    exact ⟨BfgsCoverage.Article.Master.axisRun 1 one_pos⟩

theorem ridgeExample_eq (x : Vec 2) : ridgeExample x = x 0 ^ 2 + |x 1| := by
  simp only [ridgeExample, RidgeSupersession.objective, one_mul]
  rw [sub_eq_add_neg, max_add_add_left, ← abs_eq_max_neg]

open AffineCriticalObjective in
/-- The hypotheses of `p5_cluster` hold for $u^2+|v|$ (`ridgeExample`, the ridge objective with
$a=b=t^2$, $p=q=1$, whose planar hypotheses the explicit supersession derives in the library:
`RidgeSupersession.strict_contours`, `RidgeSupersession.source_regular`), so its conclusion
applies to every admissible run on it (runs exist, previous example). -/
example : ∀ R : AdmissibleBFGSRun 2 ridgeExample,
    ∃ p, MapClusterPt p atTop R.x ∧ IsAffineCritical ridgeExample p := by
  have ha : ContDiff ℝ 2 (fun t : ℝ => t ^ 2) := contDiff_id.pow 2
  have hca : ConvexOn ℝ univ (fun t : ℝ => t ^ 2) := even_two.convexOn_pow
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    simp
  have hd2 : ∀ u : ℝ, u ≠ 0 → 0 < deriv (deriv (fun t : ℝ => t ^ 2)) u := by
    intro u _
    rw [hd]
    have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 u := by
      simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
    rw [h2.deriv]
    norm_num
  have hsc := RidgeSupersession.strictConvex_of_second_pos_except ha 0 hd2
  have hF : ConvexOn ℝ univ ridgeExample := RidgeSupersession.objective_convex hca hca 1 1
  have h0 : ridgeExample 0 = 0 := by rw [ridgeExample_eq]; simp
  have hmin : ∀ x, ridgeExample 0 ≤ ridgeExample x := by
    intro x
    rw [h0, ridgeExample_eq]
    positivity
  have huniq : ∀ x, ridgeExample x = ridgeExample 0 → x = 0 := by
    intro x hx
    rw [h0, ridgeExample_eq] at hx
    have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), abs_nonneg (x 1)]
    have hx1 : x 1 = 0 := by
      rw [hx0] at hx
      simpa using hx
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  apply p5_cluster ridgeExample hF 0
    ⟨⟨0, h0⟩, by rintro _ ⟨y, rfl⟩; rw [← h0]; exact hmin y⟩
    ⟨1, one_pos, Localization.sublevel_compact hF 0 hmin huniq 1⟩
    (fun t _ x y hxy => RidgeSupersession.strict_contours hsc hsc one_pos one_pos t x y hxy)
  intro p hp
  rcases RidgeSupersession.source_regular ha ha hca hca one_pos one_pos p hp with
    hc | ⟨f, U, hU, hpU, hf, hrep, hact, hdet⟩
  · left
    obtain ⟨V, hVsub, hVo, hpV⟩ := mem_nhds_iff.1 (hc.eventually (by simp))
    exact ⟨V, hVo, hpV, fun y hy => (show ContDiffAt ℝ 2 ridgeExample y from hVsub hy).contDiffWithinAt⟩
  · right
    refine ⟨U, hU, hpU, f 0, f 1, (hf 0).1, (hf 1).1, (hf 0).2, (hf 1).2, fun z hz => ?_,
      hact 0, hact 1, ?_⟩
    · obtain ⟨⟨i, hi⟩, hub⟩ := hrep z hz
      change RidgeSupersession.objective (fun t => t ^ 2) (fun t => t ^ 2) 1 1 z = _
      apply le_antisymm
      · rw [← hi]
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
      · exact max_le (hub ⟨0, rfl⟩) (hub ⟨1, rfl⟩)
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have e0 := congrFun hst 0
      have e1 := congrFun hst 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
      unfold HomogeneousPlanar.pairDet at hdet
      have hs : s * (coordinateGradient (f 0) p 0 * coordinateGradient (f 1) p 1 -
          coordinateGradient (f 0) p 1 * coordinateGradient (f 1) p 0) = 0 := by
        linear_combination coordinateGradient (f 1) p 1 * e0 - coordinateGradient (f 1) p 0 * e1
      have ht : t * (coordinateGradient (f 0) p 0 * coordinateGradient (f 1) p 1 -
          coordinateGradient (f 0) p 1 * coordinateGradient (f 1) p 0) = 0 := by
        linear_combination -coordinateGradient (f 0) p 1 * e0 + coordinateGradient (f 0) p 0 * e1
      exact ⟨(mul_eq_zero.1 hs).resolve_right hdet, (mul_eq_zero.1 ht).resolve_right hdet⟩

/-- The hypothesis of `no_acceptable_point_no_run` holds at the five-piece obstruction of
Chapter 6 (`h(x,y,z)=\max\{-x,y+z,-y+z,x/4,-z\}` at $(-2,0,1)$ with $H=I$ and
$(c_1,c_2)=(1/4,1/2)$): no admissible run passes through that state. -/
example (R : AdmissibleBFGSRun 3 FivePieceObstruction.objective) (h1 : R.c₁ = 1 / 4)
    (h2 : R.c₂ = 1 / 2) (k : ℕ) : ¬ (R.x k = ![-2, 0, 1] ∧ R.H k = 1) :=
  no_acceptable_point_no_run FivePieceObstruction.objective (1 / 4) (1 / 2) ![-2, 0, 1] 1
    ![-1, 0, 0] Ch06F.five_piece_ray.1 Ch06F.five_piece_obstruction.2.2.2 R h1 h2 k

/-- The hypotheses of `compact_value_distance` hold (a constant sequence at the minimizer of
$Q_1$). -/
example : Tendsto (fun _ : ℕ => euclideanSolutionDistance (LQuadraticSeed.objective 1)
      (LQuadraticSeed.minimizer 1)) atTop (𝓝 0) ∧
    ((∀ y, LQuadraticSeed.objective 1 y = LQuadraticSeed.objective 1 (LQuadraticSeed.minimizer 1) →
      y = LQuadraticSeed.minimizer 1) →
      Tendsto (fun _ : ℕ => LQuadraticSeed.minimizer 1) atTop (𝓝 (LQuadraticSeed.minimizer 1))) :=
  compact_value_distance (LQuadraticSeed.objective 1) (LQuadraticSeed.objective_convex zero_le_one)
    (LQuadraticSeed.minimizer 1) (LQuadraticSeed.objective_minimum one_pos)
    (LQuadraticSeed.objective 1 (LQuadraticSeed.minimizer 1))
    (LQuadraticSeed.objective_sublevels_compact one_pos _) (fun _ => LQuadraticSeed.minimizer 1)
    (fun _ => le_rfl) tendsto_const_nhds

/-- The hypotheses of `smooth_subspace_trace_linear` can hold on an actual run (the run
`BfgsCoverage.Article.Master.axisRun` on $u^2+|v|$, the zero subspace, $P_S=0$, $L_S=0$). -/
example (k : ℕ) :
    ((0 : Mat 2) * (BfgsCoverage.Article.Master.axisRun 1 one_pos).hessian k).trace ≤
      ((0 : Mat 2) * (BfgsCoverage.Article.Master.axisRun 1 one_pos).hessian 0).trace + 0 * k :=
  smooth_subspace_trace_linear _ ⊥ 0 (fun v => by simp [euclideanVector]) 0 (fun j => by simp) k

/-- The hypotheses of `pairwise_certificate_convergence` can hold: $F(x)=\max\{|x|,2x-1\}$ on
$\mathbb R$, $x_*=0$, $b=2$, $(c_1,c_2)=(1/4,1/3)$, with the radial fields $W(x)=xx^T$ of
`Ch03T.s_not_exactly_rs` (band certificates with $m=\eta^2$, $C=6$, $L=0$). -/
example : ∃ F : Vec 1 → ℝ, (∀ x, F 0 ≤ F x) ∧ IsCompact {x | F x ≤ 2} ∧
    ∀ η : ℝ, 0 < η → {x | F x ≤ 2 ∧ F x ≥ F 0 + η}.Nonempty →
      ∃ (W : Vec 1 → Mat 1) (m C δ : ℝ), 0 < m ∧ 0 < δ ∧
        (∀ x ∈ {x | F x ≤ 2 ∧ F x ≥ F 0 + η}, (W x).PosSemidef) ∧
        ∀ x ∈ {x | F x ≤ 2 ∧ F x ≥ F 0 + η}, ∀ z ∈ {x | F x ≤ 2 ∧ F x ≥ F 0 + η},
          ∀ g h : Vec 1, TransportedCertificate.EligiblePair F (1/4) (1/3) x z g h →
            -dot g (z - x) ≤ δ →
            dot g (W x *ᵥ g) ≥ m ∧
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x) ∧
            (TransportedCertificate.stepProjector (z - x) * W x *
                TransportedCertificate.stepProjector (z - x) -
              TransportedCertificate.stepProjector (z - x) * W z *
                TransportedCertificate.stepProjector (z - x)).PosSemidef := by
  obtain ⟨F, -, -, hmin, -, hK, -, hcert, -, -⟩ := Ch03T.s_not_exactly_rs
  refine ⟨F, hmin, hK, fun η hη _ => ?_⟩
  obtain ⟨Cert, hW, -, -, hL⟩ := hcert (1/4) (1/3) (by norm_num) η hη
  refine ⟨Cert.W, Cert.m, Cert.C, Cert.δ, Cert.m_pos, Cert.delta_pos, fun x _ => ?_, ?_⟩
  · rw [hW]
    simpa only [one_smul] using SmoothSubspace.scaled_outer_posSemidef (x - 0) 1 zero_le_one
  · intro x hx z hz g h hel hd
    refine ⟨Cert.visibility x hx g hel.gradient_x, Cert.secant x z g h hx hz hel hd, ?_⟩
    have hT := Cert.transport x z g h hx hz hel hd
    rw [hL] at hT
    simpa only [zero_mul, add_zero, one_smul, TransportedCertificate.pairStep] using hT

end BfgsCoverage.Companion.Ch01I
