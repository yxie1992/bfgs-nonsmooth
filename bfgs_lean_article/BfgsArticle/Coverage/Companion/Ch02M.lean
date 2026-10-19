import BfgsArticle.Coverage.Article.Energy
import BfgsArticle.Coverage.Article.MatrixAlgebra
import BfgsVerification.FoundationEndToEnd
import BfgsVerification.SharpPotentialTargets
import BfgsVerification.QuantitativeGrowth
import BfgsVerification.FrameNorms
import BfgsVerification.FixedNormalStrongConvex
import BfgsArticle.LUniformLocal

/-!
# Lean coverage: `companion/chapters/02_M.tex`

Chapter M of the companion ("BFGS algebra and reciprocal budgets"): the notation and
elementary consequences (`M:basic`, `M:hessian`, `M:annihilation`), Lemmas `M:localization`
and `M:strictcontours`, Theorem `M:hierarchy` and its proof, Theorems `M:average` and
`M:superquadratic` and their proofs, the fixed-reference and moving-frame energy identities,
Theorem `M:residualtheorem` and its proof, and the prose claims (including "Relation to earlier
work"). Register: `editorial/lean_coverage/register/C_02_M.json`.

## Conventions

* The chapter inherits the infinite-admissible-run convention (line 9;
  `companion/chapters/01_I.tex:40-47`): a run is `R : AdmissibleBFGSRun n F` (Definition
  `art:admissible` of the article; finite convex `F`, $H_0\succ0$, $\alpha_k>0$, $g_k\ne0$ at
  differentiable accepted points, fixed $0<c_1<c_2<1$ with Armijo and weak Wolfe). Notation
  (`notation_display`, and the article's `BfgsCoverage.Article.Energy.run_notation`):
  $B_k$ = `R.hessian k`, $q_k$ = `R.q k`, $d_k=\alpha_kq_k$ = `R.d k`, $s_k$ =
  `R.displacement k`, $y_k$ = `R.gradientChange k`, $t_k$ = `R.curvature k`,
  $\beta_k$ = `R.beta k`; $\Delta_k$ and $c=1-c_2$ are written out as
  `F (R.x k) - F (R.x (k + 1))` and `1 - R.c₂`; $e_j(H)$ = `principalSum H j`.
* Norms are Euclidean: `‖euclideanVector v‖` is $\|v\|$, `sqNorm v` is $\|v\|^2$, `dot a b` is
  $a^Tb$; `FrameNorms.euclideanOpNorm T` is the Euclidean operator norm, `SmoothSubspace.frobSq`
  the squared Frobenius norm. "Bounded gradients" is `∃ Λ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ`
  (or a bound `G > 0` where the text names it); $\sum d_k<\infty$ is `Summable R.d`. A subspace
  $S$ is a `Submodule` of `EuclideanSpace ℝ (Fin n)` with orthogonal projection
  `S.orthogonalProjection`.
* Objects that the text introduces ($M_k$, $r_k$, $a_k$, $E_k$, $R_k$ — `Rk`, since `R` names the
  run —, $A$, $a$, $b$, $u$, $v$, $\kappa$, $P$, $\mathcal F$ — `F` in the matrix theorems —,
  $G$, $K_0$, $V_\eta$, $D_J$, $\widetilde A_k$, $P_S$, $C_S$, $\overline P$) are variables with
  their defining equations as hypotheses. A hypothesis whose name starts with `_` is a standing
  assumption that the Lean proof does not use. Where the companion repeats a display of the
  article verbatim, the register points to the article item (`SAME_AS`).

## Items

* `prose/004` (line 9, the convention): `admissible_convention`.
* `disp/001`, `disp/002` (`M:basic`), `prose/005` (12-22): `notation_display`, `basic`,
  `summable_of_finite_limit`.
* `disp/003` (`M:hessian`), `disp/004` (`M:annihilation`), `prose/006`-`prose/008` (23-32):
  `hessian_form`, `annihilation`, `metric_cauchy_schwarz`, `bounded_subgradients`,
  `bounded_subgradients_argument`.
* `lemma/M:localization` with `disp/006` (34-45): `localization`, `localization_radial`;
  `lemma/M:strictcontours` (49-51): `strict_contours`.
* `prose/010`, `prose/011` (63): `elementary_symmetric_def`, `trace_det`;
  `theorem/M:hierarchy`, `disp/009`, `disp/014` (65-102): `hierarchy`, `compression_notation`,
  `rank_one_increase`.
* `theorem/M:average`, `disp/017`, `disp/018` (121-136): `average`, `hierarchy_step`,
  `potential_ge_trace`.
* `theorem/M:superquadratic`, `disp/022`-`disp/024`, `prose/013` (144-173): `superquadratic`,
  `weighted_step`, `product_bound`, `liminf_bound`, `retained_comparison`.
* `disp/025`-`disp/027`, `prose/014`-`prose/019` (182-194): `reference_notation`,
  `fixed_energy`, `cancellation`, `pairing_ge_gap`, `energy_bound`, `negligible_corrections`,
  `quadratic_corrections`.
* `disp/029`, `disp/030`, `prose/023` (196-211): `frame_identity`, `normalized_trace`,
  `frame_criterion`.
* `theorem/M:residualtheorem` (220-237): `residual_theorem`; `disp/035`-`disp/040`
  (240-272): `projection_trace`, `frame_energy`, `frame_young`, `residual_energy`,
  `residual_recurrence`, `residual_budget`.
* `prose/027`, `prose/030`, `prose/043` (275-288): `euclidean_smallness_insufficient`,
  `classical_facts`, `additive_errors_not_summable`.

The other displays of the proof of Theorem `M:hierarchy` (`disp/008`, `disp/010`-`disp/013`,
`disp/015`) and display `disp/019` repeat displays of the article and are `SAME_AS` those items
(`BfgsCoverage.Article.MatrixAlgebra`, `BfgsCoverage.Article.Energy`).

## Readings and implicit hypotheses

* Theorem `M:hierarchy` did not state $H\succ0$ and $\alpha>0$ (both implicit: the text defines
  $e_j$ only for SPD matrices, line 63, and an ordinary update has a positive length); since 15
  October 2026 it states them, as the article does (wording point W4). Lean's `principalSum` is
  defined for every matrix, and `hierarchy_needs_positive_length` shows that the inequality fails
  for $\alpha<0$.
* Theorems `M:average` and `M:superquadratic` say "an infinite full-BFGS run ... fixed weak
  Wolfe". Under the chapter's convention this is an admissible run (`average`,
  `superquadratic`); `average_full_bfgs` and `superquadratic_full_bfgs` prove them also for every
  full-BFGS sequence satisfying weak Wolfe, without an objective. The statement of Theorem
  `M:superquadratic` uses $G$, $K_0$ and $V_\eta$ of the proof of Theorem `M:average`, as it says
  since 15 October 2026 (wording point W3).
* The sentence "Thus, along runs with bounded gradients, $\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$
  excludes a positive gap" (line 194; the bounded gradients stated since 15 October 2026, wording
  point W1) needs $\sum_{k<N}q_k^{-1}\to\infty$, which Theorem `M:average` supplies under bounded
  gradients; `negligible_corrections` assumes bounded gradients,
  `negligible_corrections_of_divergent` only the divergence.
* The proof of Theorem `M:residualtheorem` argues by contradiction, so the standing assumptions of
  its displays cannot all hold; each display is stated under them (`projection_trace`, ...,
  `residual_budget`) and proved from a general one-step form whose assumptions are satisfiable
  (`projection_trace_step`, `frame_energy_step`, `frame_young_step`, `residual_energy_step`,
  `residual_recurrence_step`, `normalized_budget`). Likewise display `disp/030` is proved from
  `normalized_trace_step`.

## Non-vacuity

The examples at the end (namespace `Examples`) show that the standing assumptions can hold: the
article's quadratic run ($x_k=2^{-k}$) with values tending to $0$ and the choices of the proofs of
Theorems `M:average` and `M:superquadratic`, and with $x_*=0$,
$\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$ and $O(N^2)$; full-BFGS sequences with weak Wolfe; Lemma
`M:localization` for $x^2/2$ with $r=2$ ($\omega_2=2$), including a run with
$F(x_0)-F(x_*)<\omega_2$; Lemma `M:strictcontours` with a positive limiting level, by an actual
failing run of the article's Theorem `art:local-failure-lower` on its strongly convex objective
(`strong_convex_strict_contours`); Theorem `M:hierarchy`; moving frames; the suppositions of the
moving-frame criterion (display `disp/030`, the $O(N)$ part of `frame_criterion`), by a 1-D run
on $f(t)=1-t$ ($t\le1$), $-\log t$ ($t\ge1$) with bounded gradients and $d_k=1$ (`logRun`);
and Theorem `M:residualtheorem` with the general forms of its proof displays ($S=\{0\}$). The
moving-frame suppositions cannot hold together with bounded gradients and $d_k\to0$
(`frame_criterion`), which is why `logRun` has $d_k=1$; its values tend to $\inf F=-\infty$
("nonoptimal" at line 204 is descriptive, not a hypothesis of the Lean statements).
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter BfgsVerification

namespace BfgsCoverage.Companion.Ch02M

/-! ### Helpers -/

/-- $\|v\|^2=v^Tv$ for the Euclidean norm. -/
theorem euclid_norm_sq {n : ℕ} (v : Vec n) : ‖euclideanVector v‖ ^ 2 = sqNorm v :=
  FrameNorms.euclidean_norm_sq (euclideanVector v)

/-- A squared bound gives the Euclidean norm bound. -/
theorem euclid_norm_le_of_sqNorm_le {n : ℕ} {v : Vec n} {G : ℝ} (hG : 0 ≤ G)
    (h : sqNorm v ≤ G ^ 2) : ‖euclideanVector v‖ ≤ G :=
  (sq_le_sq₀ (norm_nonneg _) hG).mp (by rw [euclid_norm_sq]; exact h)

/-- The Euclidean norm is continuous on `Vec n`. -/
theorem continuous_euclid_norm {n : ℕ} : Continuous fun v : Vec n => ‖euclideanVector v‖ :=
  (PiLp.continuous_equiv_symm 2 _).norm

/-- `euclideanVector` is linear. -/
theorem euclideanVector_smul {n : ℕ} (c : ℝ) (x : Vec n) :
    euclideanVector (c • x) = c • euclideanVector x := rfl

theorem euclideanVector_sub {n : ℕ} (x y : Vec n) :
    euclideanVector (x - y) = euclideanVector x - euclideanVector y := rfl

theorem euclideanVector_add {n : ℕ} (x y : Vec n) :
    euclideanVector (x + y) = euclideanVector x + euclideanVector y := rfl

theorem euclideanVector_zero {n : ℕ} : euclideanVector (0 : Vec n) = 0 := rfl

/-- The Euclidean closed unit ball of `Vec n` is compact. -/
theorem euclid_closedBall_compact {n : ℕ} (ρ : ℝ) :
    IsCompact {u : Vec n | ‖euclideanVector u‖ ≤ ρ} := by
  have h := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ).image
    (PiLp.continuous_equiv 2 (fun _ : Fin n => ℝ))
  convert h using 1
  ext u
  constructor
  · intro hu
    exact ⟨euclideanVector u, by simpa [Metric.mem_closedBall, dist_zero_right] using hu, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right, euclideanVector] using hw

/-! ### Section `M:notation` -/

/-- Item `C/02_M/prose/004` (`companion/chapters/02_M.tex:9`): "All results inherit the
infinite-admissible-run convention in the inventory." The convention of
`companion/chapters/01_I.tex:40-47` (nonzero gradients at differentiable accepted iterates,
positive lengths, fixed Armijo--weak-Wolfe constants $0<c_1<c_2<1$, $H_0\succ0$, the full BFGS
update, a finite convex objective) is the library structure `AdmissibleBFGSRun n F`
(Definition `art:admissible` of the article; `BfgsCoverage.Article.Energy.admissible_iff`).
Every run in this module is `R : AdmissibleBFGSRun n F`. Unfolded: the run's step, update and
line-search conditions, with $s_k$, $y_k$, $t_k$ the library's `R.displacement k`,
`R.gradientChange k`, `R.curvature k`. -/
theorem admissible_convention {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    ConvexOn ℝ Set.univ F ∧ (R.H 0).PosDef ∧ (0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1) ∧
      ∀ k, R.g k ≠ 0 ∧ 0 < R.α k ∧ HasFDerivAt F (gradientFunctional (R.g k)) (R.x k) ∧
        R.displacement k = -R.α k • (R.H k *ᵥ R.g k) ∧
        R.x (k + 1) = R.x k + R.displacement k ∧
        R.H (k + 1) = inverseBFGS (R.H k) (R.displacement k) (R.gradientChange k) ∧
        F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (R.g k) (R.displacement k) ∧
        dot (R.g (k + 1)) (R.displacement k) ≥ R.c₂ * dot (R.g k) (R.displacement k) :=
  ⟨R.convex, R.initial_posDef, ⟨R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩, fun k =>
    ⟨R.gradient_nonzero k, R.alpha_pos k, R.hasGradient k, rfl, R.step k, R.update k,
      R.armijo k, R.weak_wolfe k⟩⟩

/-- Item `C/02_M/disp/001` (`companion/chapters/02_M.tex:12-17`):
\[ B_k=H_k^{-1},\quad q_k=g_k^TH_kg_k>0,\quad d_k=-g_k^Ts_k=\alpha_kq_k,\quad
   t_k=y_k^Ts_k,\quad\Delta_k=F(x_k)-F(x_{k+1}),\quad c=1-c_2>0. \]
The display defines notation and asserts $q_k>0$, $-g_k^Ts_k=\alpha_kq_k$ and $c>0$. In Lean
$B_k$, $q_k$, $d_k$, $t_k$ are `R.hessian k`, `R.q k`, `R.d k` (defined as $\alpha_kq_k$),
`R.curvature k`; $\Delta_k$ and $c$ are written out as `F (R.x k) - F (R.x (k + 1))` and
`1 - R.c₂`. -/
theorem notation_display {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.hessian k = (R.H k)⁻¹ ∧ R.q k = dot (R.g k) (R.H k *ᵥ R.g k) ∧ 0 < R.q k ∧
      R.d k = -dot (R.g k) (R.displacement k) ∧
      -dot (R.g k) (R.displacement k) = R.α k * R.q k ∧
      R.curvature k = dot (R.gradientChange k) (R.displacement k) ∧ 0 < 1 - R.c₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := BfgsCoverage.Article.Energy.notation_display R k
  exact ⟨h1, h2, R.q_pos k, h3, h4, rfl, R.wolfe_constant_pos⟩

/-- Item `C/02_M/disp/002`, equation `M:basic` (`companion/chapters/02_M.tex:19-21`).
Convexity, Armijo and weak Wolfe give, for every $k$,
\[ c_1d_k\le\Delta_k\le d_k,\qquad t_k\ge c\,d_k>0, \]
with $\Delta_k=F(x_k)-F(x_{k+1})$ and $c=1-c_2$. -/
theorem basic {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.c₁ * R.d k ≤ F (R.x k) - F (R.x (k + 1)) ∧ F (R.x k) - F (R.x (k + 1)) ≤ R.d k ∧
      R.curvature k ≥ (1 - R.c₂) * R.d k ∧ (1 - R.c₂) * R.d k > 0 :=
  ⟨R.armijo_decrease k, R.convexity_decrease_upper k, R.curvature_lower_bound k,
    mul_pos R.wolfe_constant_pos (R.d_pos k)⟩

/-- Item `C/02_M/prose/005` (`companion/chapters/02_M.tex:22`): "In particular
$\sum d_k<\infty$ on a run with finite limiting value." If $F(x_k)$ has a finite limit, then
$\sum_kd_k<\infty$ (`Summable R.d`; $d_k>0$). -/
theorem summable_of_finite_limit {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hlim : ∃ ℓ : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) : Summable R.d := by
  obtain ⟨ℓ, hℓ⟩ := hlim
  exact R.summable_predicted_decreases_of_value_limit ℓ hℓ

/-- Item `C/02_M/disp/003`, equation `M:hessian` (`companion/chapters/02_M.tex:23-25`): the
Hessian form of the update,
\[ B_{k+1}=B_k-\frac{g_kg_k^T}{q_k}+\frac{y_ky_k^T}{t_k}. \] -/
theorem hessian_form {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.hessian (k + 1) = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
      (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) :=
  R.hessian_update k

/-- Item `C/02_M/disp/004`, equation `M:annihilation` (`companion/chapters/02_M.tex:27-29`):
\[ M_k:=B_k-\frac{g_kg_k^T}{q_k}\succeq0,\qquad M_ks_k=0. \]
$M_k$ is the variable `M k` with its defining equation. -/
theorem annihilation {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (M : ℕ → Mat n)
    (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ) :
    (M k).PosSemidef ∧ M k *ᵥ R.displacement k = 0 := by
  rw [hM k]
  exact ⟨R.annihilated_hessian_posSemidef k, R.annihilated_hessian_mul_displacement k⟩

/-- Item `C/02_M/prose/006` (`companion/chapters/02_M.tex:30`): "For example
$(g_k^Tz)^2\le q_k z^TB_kz$, and $B_ks_k=-\alpha_kg_k$ proves the second identity." For every
$k$ and every $z$, $(g_k^Tz)^2\le q_k\,z^TB_kz$; and $B_ks_k=-\alpha_kg_k$. -/
theorem metric_cauchy_schwarz {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    (∀ z : Vec n, dot (R.g k) z ^ 2 ≤ R.q k * dot z (R.hessian k *ᵥ z)) ∧
      R.hessian k *ᵥ R.displacement k = -R.α k • R.g k := by
  have hq := R.q_pos k
  have hH := R.positive_definite k
  refine ⟨fun z => ?_, ?_⟩
  · have hpsd := (R.annihilated_hessian_posSemidef k).2 z
    simp only [star_trivial] at hpsd
    have hexp : z ⬝ᵥ ((R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) *ᵥ z) =
        dot z (R.hessian k *ᵥ z) - (R.q k)⁻¹ * dot (R.g k) z ^ 2 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec_assoc, dotProduct_smul]
      have houter : outer (R.g k) (R.g k) *ᵥ z = dot (R.g k) z • R.g k := by
        ext i
        simp only [outer, Matrix.mulVec, dotProduct, dot, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [houter, dotProduct_smul]
      change dot z (R.hessian k *ᵥ z) - (R.q k)⁻¹ • (dot (R.g k) z • dot z (R.g k)) = _
      have hc : dot z (R.g k) = dot (R.g k) z := dotProduct_comm _ _
      rw [hc, smul_eq_mul, smul_eq_mul]
      ring
    rw [hexp] at hpsd
    have h2 : (R.q k)⁻¹ * dot (R.g k) z ^ 2 ≤ dot z (R.hessian k *ᵥ z) := by linarith
    rw [inv_mul_le_iff₀ hq] at h2
    exact h2
  · change (R.H k)⁻¹ *ᵥ (-R.α k • (R.H k *ᵥ R.g k)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.one_mulVec]

/-- Item `C/02_M/prose/007` (`companion/chapters/02_M.tex:32`): "A finite convex function
has uniformly bounded subgradients on any compact set $K$." For a finite convex
$F:\R^n\to\R$ and a compact $K$ there is $G$ with $\|g\|\le G$ (Euclidean norm) for every
$x\in K$ and every subgradient $g$ of $F$ at $x$, i.e. every $g$ with
$F(y)\ge F(x)+g^T(y-x)$ for all $y$. -/
theorem bounded_subgradients {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ G : ℝ, ∀ x ∈ K, ∀ g : Vec n, (∀ y, dot g (y - x) ≤ F y - F x) →
      ‖euclideanVector g‖ ≤ G := by
  obtain ⟨G, hG, hbound⟩ := convex_supporting_bound_on_compact hF hK
  exact ⟨G, fun x hx g hg => euclid_norm_le_of_sqNorm_le hG.le (hbound x hx g hg)⟩

/-- Item `C/02_M/prose/008` (`companion/chapters/02_M.tex:32`): "Indeed, choose
$\epsilon>0$ and bound its continuous values on $K+\epsilon\overline B$. The supporting
inequality at $x$ evaluated at $x+\epsilon u$ bounds $g^Tu$ for every unit $u$, hence
$\|g\|$." For a finite convex $F$, a compact $K$ and $\epsilon>0$: $F$ is bounded above on
$K+\epsilon\overline B$ by some $M$ and below on $K$ by some $m$; for every $x\in K$, every
subgradient $g$ at $x$ and every Euclidean unit vector $u$, $g^Tu\le(M-m)/\epsilon$; hence
$\|g\|\le(M-m)/\epsilon$. -/
theorem bounded_subgradients_argument {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {K : Set (Vec n)} (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ M m : ℝ, (∀ x ∈ K, ∀ u : Vec n, ‖euclideanVector u‖ ≤ 1 → F (x + ε • u) ≤ M) ∧
      (∀ x ∈ K, m ≤ F x) ∧
      ∀ x ∈ K, ∀ g : Vec n, (∀ y, dot g (y - x) ≤ F y - F x) →
        (∀ u : Vec n, ‖euclideanVector u‖ = 1 → dot g u ≤ (M - m) / ε) ∧
          ‖euclideanVector g‖ ≤ (M - m) / ε := by
  have hcont := convex_continuous hF
  set S : Set (Vec n) := (fun p : Vec n × Vec n => p.1 + ε • p.2) ''
    (K ×ˢ {u : Vec n | ‖euclideanVector u‖ ≤ 1}) with hSdef
  have hS : IsCompact S :=
    (hK.prod (euclid_closedBall_compact 1)).image
      (continuous_fst.add (continuous_const.smul continuous_snd))
  obtain ⟨M, hM⟩ := hS.bddAbove_image hcont.continuousOn
  obtain ⟨m, hm⟩ := convex_boundedBelow_on_compact hF hK
  have hMS : ∀ x ∈ K, ∀ u : Vec n, ‖euclideanVector u‖ ≤ 1 → F (x + ε • u) ≤ M :=
    fun x hx u hu => hM ⟨x + ε • u, ⟨(x, u), ⟨hx, hu⟩, rfl⟩, rfl⟩
  refine ⟨M, m, hMS, hm, fun x hx g hg => ?_⟩
  have hunit : ∀ u : Vec n, ‖euclideanVector u‖ = 1 → dot g u ≤ (M - m) / ε := by
    intro u hu
    have h1 := hg (x + ε • u)
    rw [add_sub_cancel_left, dot_smul_right] at h1
    have h2 := hMS x hx u hu.le
    have h3 := hm x hx
    rw [le_div_iff₀ hε]
    linarith
  refine ⟨hunit, ?_⟩
  by_cases hg0 : ‖euclideanVector g‖ = 0
  · rw [hg0]
    have h0 := hMS x hx 0 (by simp [euclideanVector])
    simp only [smul_zero, add_zero] at h0
    exact div_nonneg (by linarith [hm x hx]) hε.le
  · have hpos : 0 < ‖euclideanVector g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
    set u : Vec n := ‖euclideanVector g‖⁻¹ • g with hu
    have hun : ‖euclideanVector u‖ = 1 := by
      rw [hu, euclideanVector_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ hpos.ne']
    have hdot : dot g u = ‖euclideanVector g‖ := by
      rw [hu, dot_smul_right]
      have hgg : dot g g = ‖euclideanVector g‖ ^ 2 := by
        rw [euclid_norm_sq]
        simp only [dot, sqNorm, pow_two]
      rw [hgg]
      field_simp
      ring
    rw [← hdot]
    exact hunit u hun

/-! ### Lemma `M:localization` -/

/-- The sphere minimum of Lemma `M:localization`: under the lemma's assumptions the Euclidean
sphere of radius $r$ is nonempty, $\omega_r$ (defined as the infimum) is a minimum, and
$\omega_r>0$. -/
theorem sphere_min {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ω = sInf ((fun z => F (xstar + z) - F xstar) '' {z | ‖euclideanVector z‖ = r})) :
    {z : Vec n | ‖euclideanVector z‖ = r}.Nonempty ∧
      IsLeast ((fun z => F (xstar + z) - F xstar) '' {z | ‖euclideanVector z‖ = r}) ω ∧
      0 < ω := by
  set S := {z : Vec n | ‖euclideanVector z‖ = r} with hSdef
  have hS : IsCompact S :=
    (euclid_closedBall_compact r).of_isClosed_subset
      (isClosed_eq continuous_euclid_norm continuous_const) (fun z hz => le_of_eq hz)
  have hne : S.Nonempty := by
    refine ⟨Pi.single (⟨0, hn⟩ : Fin n) r, ?_⟩
    have h := euclid_norm_sq (Pi.single (⟨0, hn⟩ : Fin n) r)
    have hs : sqNorm (Pi.single (⟨0, hn⟩ : Fin n) r) = r ^ 2 := by
      simp [sqNorm, Pi.single_apply]
    rw [hs] at h
    exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).mp h
  have hcont : ContinuousOn (fun z => F (xstar + z) - F xstar) S :=
    ((convex_continuous hF).comp (continuous_const.add continuous_id)).sub
      continuous_const |>.continuousOn
  obtain ⟨z0, hz0, hmin0⟩ := hS.exists_isMinOn hne hcont
  have hleast : IsLeast ((fun z => F (xstar + z) - F xstar) '' S) (F (xstar + z0) - F xstar) :=
    ⟨⟨z0, hz0, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmin0 hz⟩
  have hωeq : ω = F (xstar + z0) - F xstar := by rw [hω]; exact hleast.csInf_eq
  refine ⟨hne, hωeq ▸ hleast, ?_⟩
  rw [hωeq]
  have hz0ne : z0 ≠ 0 := by
    rintro rfl
    have h0 : ‖euclideanVector (0 : Vec n)‖ = r := hz0
    rw [show euclideanVector (0 : Vec n) = 0 from rfl, norm_zero] at h0
    exact hr.ne h0
  have hne' : F (xstar + z0) ≠ F xstar := fun h => hz0ne (by
    have := huniq _ h
    simpa using this)
  exact sub_pos.mpr (lt_of_le_of_ne (hmin _) (Ne.symm hne'))

/-- Item `C/02_M/disp/006` (`companion/chapters/02_M.tex:43-45`), in the proof of Lemma
`M:localization`. Under the assumptions of the lemma (with $\omega_r$ the minimum over the
Euclidean sphere of radius $r$), for $\|x-x_*\|\ge r$, convexity along the radial segment gives
\[ F(x)-F(x_*)\ge\frac{\|x-x_*\|}{r}\omega_r\ge\omega_r. \] -/
theorem localization_radial {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (_hU : U ∈ 𝓝 xstar) (r : ℝ) (hr : 0 < r)
    (_hrU : {x | ‖euclideanVector (x - xstar)‖ ≤ r} ⊆ U) (ω : ℝ)
    (hω : ω = sInf ((fun z => F (xstar + z) - F xstar) '' {z | ‖euclideanVector z‖ = r}))
    (x : Vec n) (hx : ‖euclideanVector (x - xstar)‖ ≥ r) :
    F x - F xstar ≥ ‖euclideanVector (x - xstar)‖ / r * ω ∧
      ‖euclideanVector (x - xstar)‖ / r * ω ≥ ω := by
  obtain ⟨_, hleast, hωpos⟩ := sphere_min hn F hF xstar hmin huniq r hr ω hω
  set ρ := ‖euclideanVector (x - xstar)‖ with hρdef
  have hρ : 0 < ρ := lt_of_lt_of_le hr hx
  set t := r / ρ with htdef
  have ht0 : 0 ≤ t := div_nonneg hr.le hρ.le
  have ht1 : t ≤ 1 := (div_le_one hρ).mpr hx
  have hz : ‖euclideanVector (t • (x - xstar))‖ = r := by
    rw [euclideanVector_smul, norm_smul, Real.norm_of_nonneg ht0, ← hρdef, htdef]
    field_simp
  have hωz : ω ≤ F (xstar + t • (x - xstar)) - F xstar := hleast.2 ⟨_, hz, rfl⟩
  have hconv := hF.2 (Set.mem_univ xstar) (Set.mem_univ x) (sub_nonneg.mpr ht1) ht0
    (by ring : (1 - t) + t = 1)
  have heq : (1 - t) • xstar + t • x = xstar + t • (x - xstar) := by module
  rw [heq, smul_eq_mul, smul_eq_mul] at hconv
  have h1 : ω ≤ t * (F x - F xstar) := by nlinarith
  constructor
  · calc ρ / r * ω ≤ ρ / r * (t * (F x - F xstar)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hρ.le hr.le)
      _ = F x - F xstar := by rw [htdef]; field_simp; ring
  · have h1' : 1 ≤ ρ / r := (one_le_div hr).mpr hx
    nlinarith

/-- Item `C/02_M/lemma/M:localization` (`companion/chapters/02_M.tex:34-40`), Lemma
`M:localization` ("A low sublevel is an invariant local basin"), with its display
`C/02_M/disp/005`.

Let $F$ be finite convex with a unique minimizer $x_*$. In positive dimension ($n\ge1$), choose
$r>0$ so that the closed Euclidean ball $\overline B_r(x_*)$ lies in the specified structural
neighborhood $U$ of $x_*$. Then the sphere $\{\|z\|=r\}$ is nonempty,
\[ \omega_r=\min_{\|z\|=r}\{F(x_*+z)-F(x_*)\}>0 \]
(the infimum is attained), and $F(x_0)-F(x_*)<\omega_r$ places the entire initial sublevel
$\{F\le F(x_0)\}$ in the open ball $B_r(x_*)$. As the title says, the basin is invariant: every
admissible run with $F(x_0)-F(x_*)<\omega_r$ stays in $B_r(x_*)\subset U$ (no bound on $H_0$). -/
theorem localization {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (hU : U ∈ 𝓝 xstar) (r : ℝ) (hr : 0 < r)
    (hrU : {x | ‖euclideanVector (x - xstar)‖ ≤ r} ⊆ U) (ω : ℝ)
    (hω : ω = sInf ((fun z => F (xstar + z) - F xstar) '' {z | ‖euclideanVector z‖ = r})) :
    {z : Vec n | ‖euclideanVector z‖ = r}.Nonempty ∧
      IsLeast ((fun z => F (xstar + z) - F xstar) '' {z | ‖euclideanVector z‖ = r}) ω ∧
      0 < ω ∧
      (∀ x0 : Vec n, F x0 - F xstar < ω →
        {x | F x ≤ F x0} ⊆ {x | ‖euclideanVector (x - xstar)‖ < r}) ∧
      ∀ R : AdmissibleBFGSRun n F, F (R.x 0) - F xstar < ω →
        ∀ k, ‖euclideanVector (R.x k - xstar)‖ < r ∧ R.x k ∈ U := by
  obtain ⟨hne, hleast, hωpos⟩ := sphere_min hn F hF xstar hmin huniq r hr ω hω
  have htrap : ∀ x0 : Vec n, F x0 - F xstar < ω →
      {x | F x ≤ F x0} ⊆ {x | ‖euclideanVector (x - xstar)‖ < r} := by
    intro x0 hx0 x hx
    by_contra hfar
    have hfar' : ‖euclideanVector (x - xstar)‖ ≥ r := le_of_not_lt hfar
    have h := (localization_radial hn F hF xstar hmin huniq U hU r hr hrU ω hω x hfar')
    have hxle : F x ≤ F x0 := hx
    linarith [h.1, h.2]
  refine ⟨hne, hleast, hωpos, htrap, fun R hR k => ?_⟩
  have hk : ‖euclideanVector (R.x k - xstar)‖ < r := htrap (R.x 0) hR (R.objective_le_initial k)
  exact ⟨hk, hrU (le_of_lt hk)⟩

/-- Proof of Lemma `M:localization`, undisplayed remarks of
`companion/chapters/02_M.tex:46` (not register items): "This argument also proves boundedness of
every sublevel for a finite convex function with an attained unique minimizer. In dimension zero
the space is a singleton, so the trapping and compact-sublevel conclusions hold directly." Every
sublevel is bounded and compact; and in dimension zero all points coincide and every sublevel is
compact. -/
theorem localization_remarks {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    (∀ a : ℝ, Bornology.IsBounded {x | F x ≤ a} ∧ IsCompact {x | F x ≤ a}) ∧
      (n = 0 → (∀ x y : Vec n, x = y) ∧ ∀ a : ℝ, IsCompact {x | F x ≤ a}) := by
  refine ⟨fun a => ⟨Localization.sublevel_bounded hF xstar hmin huniq a,
    Localization.sublevel_compact hF xstar hmin huniq a⟩, fun hn0 => ?_⟩
  subst hn0
  exact ⟨fun x y => funext fun i => i.elim0, fun a => Set.Finite.isCompact (Set.toFinite _)⟩

/-! ### Lemma `M:strictcontours` -/

/-- Item `C/02_M/lemma/M:strictcontours` (`companion/chapters/02_M.tex:49-51`), Lemma
`M:strictcontours` ("Strict contours give vanishing steps on a positive limiting level").

Suppose the run is contained in a compact sublevel $\{F\le b\}$, $F(x_k)\downarrow\ell>F_*$
($F_*=\min F$), and the boundary of $\{F\le\ell\}$ contains no nontrivial line segment
(every segment $[x,z]$ in the frontier has $x=z$). Then $s_k\to0$.

The monotonicity in "$\downarrow$" holds for every admissible run (Armijo) and is not used
(`_hmono`). -/
theorem strict_contours {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (b : ℝ) (hK : IsCompact {x | F x ≤ b}) (hrun : ∀ k, F (R.x k) ≤ b)
    (ℓ : ℝ) (_hmono : Antitone fun k => F (R.x k))
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ))
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (hℓ : ℓ > Fstar)
    (hcontour : ∀ x z : Vec n, segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z) :
    Tendsto R.displacement atTop (𝓝 0) := by
  have hsub : R.initialSublevel ⊆ {x | F x ≤ b} := fun x hx => le_trans hx (hrun 0)
  have hclosed : IsClosed R.initialSublevel :=
    isClosed_le (convex_continuous R.convex) continuous_const
  have hK0 : IsCompact R.initialSublevel := hK.of_isClosed_subset hclosed hsub
  obtain ⟨⟨y, hy⟩, _⟩ := hFstar
  exact R.steps_tendsto_zero_of_strict_contour hK0 ℓ hlim ⟨y, hy ▸ hℓ⟩ hcontour

/-! ### Section `M:principal` -/

/-- Item `C/02_M/prose/010` (`companion/chapters/02_M.tex:63`), the definition "For SPD $H$,
let $e_j(H)$ be the elementary symmetric polynomial of degree $j$ of its eigenvalues, with
$e_{n+1}=0$." The Lean $e_j(H)$ is the library's `principalSum H j`, the sum of the
$j\times j$ principal minors. This theorem unfolds it to the text's definition: for SPD $H$
it is the $j$-th elementary symmetric polynomial of the eigenvalues `hH.isHermitian.eigenvalues`
(with multiplicity), for every $j$, and $e_{n+1}(H)=0$. -/
theorem elementary_symmetric_def {n : ℕ} (H : Mat n) (hH : H.PosDef) :
    (∀ j : ℕ, principalSum H j =
      (Multiset.map hH.isHermitian.eigenvalues Finset.univ.val).esymm j) ∧
      principalSum H (n + 1) = 0 :=
  ⟨(BfgsCoverage.Article.Energy.principal_sums_coefficients H hH.isHermitian).2.2.2,
    principalSum_terminal H⟩

/-- Item `C/02_M/prose/011` (`companion/chapters/02_M.tex:63`): "Thus $e_1=\tr$ and
$e_n=\det$." For SPD $H$, $e_1(H)=\tr H$ and $e_n(H)=\det H$. -/
theorem trace_det {n : ℕ} (H : Mat n) (hH : H.PosDef) :
    principalSum H 1 = H.trace ∧ principalSum H n = H.det :=
  BfgsCoverage.Article.Energy.principal_trace_det H
    (BfgsCoverage.Article.Energy.isSymm_of_posDef hH)

/-- Item `C/02_M/theorem/M:hierarchy` (`companion/chapters/02_M.tex:65-70`), Theorem
`M:hierarchy` (Principal-minor hierarchy), with its display \eqref{M:minor}.

For $H\succ0$ and an ordinary inverse-BFGS update with $s=-\alpha Hg$, $\alpha>0$, $q=g^THg>0$
and $\beta=-y^THg/q>0$,
\[ e_j(H_+)\le \frac{\|y\|^2}{\beta^2q}e_{j+1}(H)+\frac\alpha\beta e_j(H),\qquad1\le j\le n. \]
($H\succ0$ and $\alpha>0$ are stated since 15 October 2026, wording point W4; before, they were
implicit in the setting of $e_j$, line 63, and in the convention that an ordinary update has a
positive length.) $H_+$ is the inverse update
`inverseBFGS H s y`. The standing assumptions are written as in the article's
`MatrixAlgebra.lean`; $\|y\|^2$ is `sqNorm y` and $e_j$ is `principalSum`. -/
theorem hierarchy {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n →
      principalSum Hplus j ≤
        sqNorm y / (β ^ 2 * q) * principalSum H (j + 1) + α / β * principalSum H j :=
  (BfgsCoverage.Article.Energy.minor_hierarchy H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ
    hHplus).1

/-- The positivity $\alpha>0$ stated in Theorem `M:hierarchy` (implicit there before 15 October
2026) is needed: for $n=2$,
$H=I$, $g=e_1$, $y=-e_1$ and $\alpha=-1$ (so $s=e_1$, $q=1$, $\beta=1$, $t=y^Ts=-1$), the
update is $H_+=\operatorname{diag}(-1,1)$ and \eqref{M:minor} fails at $j=1$:
$e_1(H_+)=0>-1=\|y\|^2e_2(H)/(\beta^2q)+(\alpha/\beta)e_1(H)$. -/
theorem hierarchy_needs_positive_length :
    ∃ (H Hplus : Mat 2) (g y s : Vec 2) (α q β : ℝ),
      H.PosDef ∧ s = -α • (H *ᵥ g) ∧ q = dot g (H *ᵥ g) ∧ 0 < q ∧
        β = -dot y (H *ᵥ g) / q ∧ 0 < β ∧ Hplus = inverseBFGS H s y ∧ α < 0 ∧
        ¬ principalSum Hplus 1 ≤
          sqNorm y / (β ^ 2 * q) * principalSum H (1 + 1) + α / β * principalSum H 1 := by
  refine ⟨1, inverseBFGS 1 ![1, 0] ![-1, 0], ![1, 0], ![-1, 0], ![1, 0], -1, 1, 1,
    Matrix.PosDef.one, ?_, ?_, one_pos, ?_, one_pos, rfl, by norm_num, ?_⟩
  · ext i
    fin_cases i <;> simp
  · simp [dot, Fin.sum_univ_two]
  · simp [dot, Fin.sum_univ_two]
  · rw [principalSum_one, principalSum_one, show (1 + 1 : ℕ) = 2 from rfl, principalSum_top]
    simp [inverseBFGS, dot, outer, sqNorm, Fin.sum_univ_two, Matrix.trace, Matrix.mul_apply,
      Matrix.one_apply]

/-- Item `C/02_M/disp/009` (`companion/chapters/02_M.tex:77-80`), in the proof of Theorem
`M:hierarchy`: the definitions
\[ A=Z^THZ,\ a=Z^THg,\ b=Z^THy,\ r=y^THy,\quad u=a^TA^{-1}a,\quad w=a^TA^{-1}b,\quad
   z=b^TA^{-1}b \]
for $Z$ with $j$ orthonormal columns. The later theorems take these objects as variables with
exactly these defining equations. They are meaningful because $A$ is invertible (stated here:
$A\succ0$, $AA^{-1}=A^{-1}A=I$), which the proof also notes at line 103 ("only $A$ must be
invertible, which it is"). -/
theorem compression_notation {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (A : Mat j) (hA : A = Zᵀ * H * Z) :
    A.PosDef ∧ A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  have hApos : A.PosDef := hA ▸ metricGram_posDef hH
    (BfgsCoverage.Article.Energy.mulVec_injective_of_orthonormal hZ)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hApos.det_pos.ne'
  exact ⟨hApos, Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu⟩

/-- Item `C/02_M/disp/014` (`companion/chapters/02_M.tex:100-102`), in the proof of Theorem
`M:hierarchy`. Under the assumptions of the theorem, with $Z$ ($j$ orthonormal columns,
$1\le j\le n$), $v,\kappa,P,\mathcal F$ (`F`) and $A,a,b,r,u$ as defined in the proof: adding the
rank-one term $\frac{\alpha}{\beta q}vv^T$ changes the compressed determinant by exactly
\[ \frac{\alpha}{\beta q}\det A\,u\le\frac\alpha\beta\det A, \]
because $u\le q$. Stated as $\det(Z^TH_+Z)=\det(Z^T\mathcal FZ)+\frac{\alpha}{\beta q}\det A\,u$,
the inequality, and $u\le q$. -/
theorem rank_one_increase {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (hj : 1 ≤ j) (hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y))
    (u : ℝ) (hu : u = dot a (A⁻¹ *ᵥ a)) :
    (Zᵀ * Hplus * Z).det = (Zᵀ * F * Z).det + α / (β * q) * A.det * u ∧
      α / (β * q) * A.det * u ≤ α / β * A.det ∧ u ≤ q := by
  have hupd := BfgsCoverage.Article.MatrixAlgebra.compression_update H Hplus g y s α q β hH hs hα
    hq_def hq hβ_def hβ hHplus Z hZ hj hjn v hv κ hκ P hP F hF a ha
  have hinc := (BfgsCoverage.Article.MatrixAlgebra.compression_add_rank_one H Hplus g y s α q β
    hH hs hα hq_def hq hβ_def hβ hHplus Z hZ hj hjn v hv κ hκ P hP F hF A hA a b ha hb r hr u hu
    (α / (β * q))).2
  obtain ⟨_, _, huq, hle⟩ := BfgsCoverage.Article.MatrixAlgebra.u_bounds H Hplus g y s α q β hH hs
    hα hq_def hq hβ_def hβ hHplus Z hZ hj hjn A hA a ha u hu
  refine ⟨?_, hle, huq⟩
  rw [hupd, hinc, mul_assoc]

/-! ### Section `M:reciprocal` -/

/-- Item `C/02_M/theorem/M:average` (`companion/chapters/02_M.tex:121-127`), Theorem
`M:average` (Bounded gradients and vanishing predicted decrease), with its display
`C/02_M/disp/016`.

If an infinite full-BFGS run has bounded gradients, fixed weak Wolfe and $d_k\to0$, then
\[ \Bigl(\prod_{k<N}q_k^{-1}\Bigr)^{1/N}\to\infty,\qquad\frac1N\sum_{k<N}q_k^{-1}\to\infty. \]
The run is an admissible run (the chapter's convention; its weak-Wolfe constant $c_2<1$ is
fixed). "Bounded gradients" is $\exists\Lambda\ \forall k\ \|g_k\|\le\Lambda$ (Euclidean norm);
the power is the real power. `average_full_bfgs` proves the same for every full-BFGS
sequence satisfying only weak Wolfe (no objective). -/
theorem average {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (hd : Tendsto R.d atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∏ k ∈ Finset.range N, (R.q k)⁻¹) ^ (1 / (N : ℝ))) atTop atTop ∧
      Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop :=
  BfgsCoverage.Article.Energy.reciprocal_growth R hbdd hd

/-- The full-BFGS matrix run determined by sequences $H_k,g_k,\alpha_k$ that satisfy the
update, $H_0\succ0$, $g_k\ne0$, $\alpha_k>0$ and weak Wolfe with a fixed $c_2<1$ (positive
definiteness, $q_k>0$ and $t_k>0$ are proved by the library's `fullBFGS_positive_invariants`). -/
def weakWolfeRun {n : ℕ} (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ) (c₂ : ℝ)
    (hH0 : (H 0).PosDef) (hg : ∀ k, g k ≠ 0) (hα : ∀ k, 0 < α k) (hc₂ : c₂ < 1)
    (hww : ∀ k, c₂ * dot (g k) (-α k • (H k *ᵥ g k)) ≤ dot (g (k + 1)) (-α k • (H k *ᵥ g k)))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (-α k • (H k *ᵥ g k)) (g (k + 1) - g k)) :
    FullBFGSRun n where
  H := H
  g := g
  α := α
  positive_definite := fun k =>
    (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hww hupd k).1
  alpha_pos := hα
  energy_pos := fun k => (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hww hupd k).2.1
  curvature_pos := fun k =>
    (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hww hupd k).2.2
  update := hupd

/-- Theorem `M:average` read for an infinite full-BFGS run with fixed weak Wolfe and no
objective: sequences $H_k,g_k,\alpha_k$ with $H_0\succ0$, $g_k\ne0$, $\alpha_k>0$,
$s_k=-\alpha_kH_kg_k$, the inverse update, and $g_{k+1}^Ts_k\ge c_2g_k^Ts_k$ for a fixed
$0<c_2<1$. With $q_k=g_k^TH_kg_k$ and $d_k=\alpha_kq_k$: bounded gradients and $d_k\to0$ give
both limits of Theorem `M:average`. -/
theorem average_full_bfgs {n : ℕ} (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ) (c₂ : ℝ)
    (hH0 : (H 0).PosDef) (hg : ∀ k, g k ≠ 0) (hα : ∀ k, 0 < α k) (_hc₂pos : 0 < c₂)
    (hc₂ : c₂ < 1)
    (hww : ∀ k, c₂ * dot (g k) (-α k • (H k *ᵥ g k)) ≤ dot (g (k + 1)) (-α k • (H k *ᵥ g k)))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (-α k • (H k *ᵥ g k)) (g (k + 1) - g k))
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (g k)‖ ≤ Λ)
    (hd : Tendsto (fun k => α k * dot (g k) (H k *ᵥ g k)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
        (∏ k ∈ Finset.range N, (dot (g k) (H k *ᵥ g k))⁻¹) ^ (1 / (N : ℝ))) atTop atTop ∧
      Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (dot (g k) (H k *ᵥ g k))⁻¹)
        atTop atTop := by
  set Rf := weakWolfeRun H g α c₂ hH0 hg hα hc₂ hww hupd
  obtain ⟨G, hG, hgG⟩ := BfgsCoverage.Article.Energy.sqNorm_bound_of_bounded g hbdd
  obtain ⟨h1, h2⟩ := reciprocalGrowth n Rf G (1 - c₂) hG (sub_pos.mpr hc₂) hgG
    (fun k => Rf.beta_ge_of_weakWolfe k c₂ (hww k)) hd
  refine ⟨h1.congr fun N => ?_, h2.congr fun N => ?_⟩
  · rw [reciprocalGeometricMean, one_div]
    rfl
  · rw [reciprocalMean, div_eq_inv_mul, one_div]
    rfl

/-- Item `C/02_M/disp/017` (`companion/chapters/02_M.tex:130-132`), in the proof of Theorem
`M:average`. Under the assumptions of the theorem, with $G>0$, $\|g_k\|\le G$ for all $k$ and
$K_0=4G^2/c^2$ ($c=1-c_2$): for every $k$ and $1\le j\le n$,
\[ e_j(H_{k+1})\le q_k^{-1}\{K_0e_{j+1}(H_k)+(d_k/c)e_j(H_k)\}. \] -/
theorem hierarchy_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G)
    (K0 : ℝ) (hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2) (k j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    principalSum (R.H (k + 1)) j ≤
      (R.q k)⁻¹ * (K0 * principalSum (R.H k) (j + 1) +
        R.d k / (1 - R.c₂) * principalSum (R.H k) j) := by
  have h := BfgsCoverage.Article.Energy.normalized_hierarchy R _hbdd _hd G hG hgG K0 hK0 k j hj
    hjn
  rw [inv_mul_eq_div, le_div_iff₀ (R.q_pos k), mul_comm]
  exact h

/-- Item `C/02_M/disp/018` (`companion/chapters/02_M.tex:134-136`), in the proof of Theorem
`M:average`. Under the assumptions of display `C/02_M/disp/017`, fix $\eta>0$ and a tail $J$ with
$d_k/c\le\eta$ for $k\ge J$, and define, for SPD $H$,
\[ V_\eta(H)=\sum_{j=1}^n(K_0/\eta)^{j-1}e_j(H)\ge\tr H. \]
$V_\eta$ is the variable `V` (specified on SPD matrices); the claim is $V_\eta(H)\ge\tr H$ for
every SPD $H$. -/
theorem potential_ge_trace {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (G : ℝ) (_hG : 0 < G) (_hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G)
    (K0 : ℝ) (hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2)
    (η : ℝ) (hη : 0 < η) (J : ℕ) (_hJ : ∀ k, J ≤ k → R.d k / (1 - R.c₂) ≤ η)
    (V : Mat n → ℝ)
    (hV : ∀ H : Mat n, H.PosDef →
      V H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) :
    ∀ H : Mat n, H.PosDef → V H ≥ H.trace := by
  intro H hH
  have hn := R.dimension_pos
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    positivity
  rw [hV H hH, BfgsCoverage.Article.Energy.potential_eq_weighted, ← principalSum_one, ge_iff_le]
  exact ScalarHierarchy.first_le_weighted n _ _ hn (div_nonneg hK0nn hη.le)
    (principalSum_nonneg hH.posSemidef)

/-- Item `C/02_M/theorem/M:superquadratic` (`companion/chapters/02_M.tex:144-155`), Theorem
`M:superquadratic` (Finite horizon and superquadratic growth under summability), with its
displays \eqref{M:finitehorizon} and \eqref{M:superquad}.

Assume bounded gradients, fixed weak Wolfe and $\sum_kd_k<\infty$. For a fixed tail $J$ let
$D_J=\sum_{k\ge J}d_k>0$. For every $\eta>0$ and $m\ge2$, with $G$, $K_0$ and $V_\eta$ as in the
proof of Theorem~\ref{M:average},
\[ \sum_{k=J}^{J+m-1}q_k^{-1}\ge m[G^2V_\eta(H_J)]^{-1/m}
   \Bigl(\eta+\frac{D_J}{c(m-1)}\Bigr)^{-(m-1)/m}. \]
In particular $\frac1{N^2}\sum_{k<N}q_k^{-1}\to\infty$.

The statement uses $G$, $K_0$ and $V_\eta$ of the proof of Theorem `M:average` (declared in the
statement since 15 October 2026, wording point W3): $G>0$ is a bound
$\|g_k\|\le G$ (this is how bounded gradients enter), $c=1-c_2$, $K_0=4G^2/c^2$ and
$V_\eta(H)=\sum_{j=1}^n(K_0/\eta)^{j-1}e_j(H)$ for SPD $H$ (the variable `V η H`). Real powers;
the sum over $k=J,\dots,J+m-1$ is over `Finset.Ico J (J + m)`. -/
theorem superquadratic {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) (hsum : Summable R.d)
    (J : ℕ) (DJ : ℝ) (hDJ : DJ = ∑' i, R.d (J + i))
    (K0 : ℝ) (hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2)
    (V : ℝ → Mat n → ℝ)
    (hV : ∀ η : ℝ, 0 < η → ∀ H : Mat n, H.PosDef →
      V η H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) :
    0 < DJ ∧
      (∀ η : ℝ, 0 < η → ∀ m : ℕ, 2 ≤ m →
        ∑ k ∈ Finset.Ico J (J + m), (R.q k)⁻¹ ≥
          (m : ℝ) * (G ^ 2 * V η (R.H J)) ^ (-1 / (m : ℝ)) *
            (η + DJ / ((1 - R.c₂) * ((m : ℝ) - 1))) ^ (-((m : ℝ) - 1) / (m : ℝ))) ∧
      Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop := by
  refine ⟨?_, fun η hη m hm => ?_, ?_⟩
  · rw [hDJ]
    exact (R.shift_summable_d hsum J).tsum_pos (fun i => (R.d_pos (J + i)).le) 0 (R.d_pos (J + 0))
  · exact BfgsCoverage.Article.Energy.finite_horizon_bound R G hG hgG hsum J DJ hDJ K0 hK0 η hη
      (V η) (hV η hη) m hm
  · refine (BfgsCoverage.Article.Energy.superquadratic_growth R ⟨G, hgG⟩ hsum).congr fun N => ?_
    rw [one_div, div_eq_inv_mul]

/-- Theorem `M:superquadratic` read for an infinite full-BFGS run with fixed weak Wolfe and no
objective (as in `average_full_bfgs`): bounded gradients and $\sum_kd_k<\infty$ give
$\frac1{N^2}\sum_{k<N}q_k^{-1}\to\infty$, $D_J=\sum_{k\ge J}d_k>0$ for every tail $J$, and, for
every tail $J$, $\eta>0$ and $m\ge2$, the finite-horizon bound \eqref{M:finitehorizon} with
$G>0$ any gradient bound, $c=1-c_2$, $K_0=4G^2/c^2$. -/
theorem superquadratic_full_bfgs {n : ℕ} (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ) (c₂ : ℝ)
    (hH0 : (H 0).PosDef) (hg : ∀ k, g k ≠ 0) (hα : ∀ k, 0 < α k) (_hc₂pos : 0 < c₂)
    (hc₂ : c₂ < 1)
    (hww : ∀ k, c₂ * dot (g k) (-α k • (H k *ᵥ g k)) ≤ dot (g (k + 1)) (-α k • (H k *ᵥ g k)))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (-α k • (H k *ᵥ g k)) (g (k + 1) - g k))
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (g k)‖ ≤ G)
    (hsum : Summable (fun k => α k * dot (g k) (H k *ᵥ g k))) :
    Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (dot (g k) (H k *ᵥ g k))⁻¹)
        atTop atTop ∧
      (∀ J : ℕ, 0 < ∑' i, α (J + i) * dot (g (J + i)) (H (J + i) *ᵥ g (J + i))) ∧
      ∀ (J : ℕ) (η : ℝ), 0 < η → ∀ m : ℕ, 2 ≤ m →
        (m : ℝ) * (G ^ 2 * ∑ j ∈ Finset.Icc 1 n,
            ((4 * G ^ 2 / (1 - c₂) ^ 2) / η) ^ (j - 1) * principalSum (H J) j) ^ (-1 / (m : ℝ)) *
          (η + (∑' i, α (J + i) * dot (g (J + i)) (H (J + i) *ᵥ g (J + i))) /
            ((1 - c₂) * ((m : ℝ) - 1))) ^ (-((m : ℝ) - 1) / (m : ℝ)) ≤
          ∑ k ∈ Finset.Ico J (J + m), (dot (g k) (H k *ᵥ g k))⁻¹ := by
  set Rf := weakWolfeRun H g α c₂ hH0 hg hα hc₂ hww hupd
  have hgG2 : ∀ k, sqNorm (Rf.g k) ≤ G ^ 2 := fun k =>
    BfgsCoverage.Article.Energy.sqNorm_le_of_norm_le (hgG k)
  have hβ : ∀ k, 1 - c₂ ≤ Rf.beta k := fun k => Rf.beta_ge_of_weakWolfe k c₂ (hww k)
  refine ⟨?_, fun J => ?_, fun J η hη m hm => ?_⟩
  · refine (superquadraticReciprocalGrowth n Rf G (1 - c₂) hG (sub_pos.mpr hc₂) hgG2 hβ
      hsum).congr fun N => ?_
    rw [one_div, div_eq_inv_mul]
    rfl
  · have hpos : ∀ k, 0 < α k * dot (g k) (H k *ᵥ g k) := fun k =>
      mul_pos (hα k) (Rf.energy_pos k)
    have hs : Summable (fun i => α (J + i) * dot (g (J + i)) (H (J + i) *ᵥ g (J + i))) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff J).mpr hsum
    exact hs.tsum_pos (fun i => (hpos (J + i)).le) 0 (hpos (J + 0))
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : 0 < m' := by omega
    have h := finiteHorizon Rf G (1 - c₂) hG (sub_pos.mpr hc₂) hgG2 hβ hsum J m' hm' η hη
    dsimp only at h
    have hcast : ((m' + 1 : ℕ) : ℝ) - 1 = (m' : ℝ) := by
      push_cast
      ring
    rw [BfgsCoverage.Article.Energy.potential_eq_weighted, hcast, Finset.sum_Ico_eq_sum_range,
      show J + (m' + 1) - J = m' + 1 by omega]
    exact h

/-- $q_k\le G^2\tr H_k\le G^2V_\eta(H_k)$ when $\|g_k\|\le G$ (the endpoint bound used in the
proofs of Theorems `M:average` and `M:superquadratic`). -/
theorem q_le_potential {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (G : ℝ) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) (K0 : ℝ) (hK0 : 0 ≤ K0)
    (η : ℝ) (hη : 0 < η) (V : Mat n → ℝ)
    (hV : ∀ H : Mat n, H.PosDef →
      V H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) (k : ℕ) :
    R.q k ≤ G ^ 2 * V (R.H k) := by
  have hH := R.positive_definite k
  have hn := R.dimension_pos
  calc R.q k ≤ sqNorm (R.g k) * (R.H k).trace :=
        metricEnergy_le_sqNorm_mul_trace (R.H k) (R.g k) hH.posSemidef
    _ ≤ G ^ 2 * (R.H k).trace :=
        mul_le_mul_of_nonneg_right (BfgsCoverage.Article.Energy.sqNorm_le_of_norm_le (hgG k))
          (trace_pos_of_posDef hH hn).le
    _ ≤ G ^ 2 * V (R.H k) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg G)
        rw [hV _ hH, BfgsCoverage.Article.Energy.potential_eq_weighted, ← principalSum_one]
        exact ScalarHierarchy.first_le_weighted n _ _ hn (div_nonneg hK0 hη.le)
          (principalSum_nonneg hH.posSemidef)

/-- Item `C/02_M/disp/022` (`companion/chapters/02_M.tex:158-160`), in the proof of Theorem
`M:superquadratic`. Under the assumptions of the theorem, for the given $\eta>0$ and $m\ge2$,
without any tail restriction on $d_k$, the weighted hierarchy gives for every $k$
\[ V_\eta(H_{k+1})\le\frac{\eta+d_k/c}{q_k}V_\eta(H_k). \] -/
theorem weighted_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) (hsum : Summable R.d)
    (J : ℕ) (DJ : ℝ) (_hDJ : DJ = ∑' i, R.d (J + i))
    (K0 : ℝ) (hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2)
    (V : ℝ → Mat n → ℝ)
    (hV : ∀ η : ℝ, 0 < η → ∀ H : Mat n, H.PosDef →
      V η H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j)
    (η : ℝ) (hη : 0 < η) (m : ℕ) (_hm : 2 ≤ m) (k : ℕ) :
    V η (R.H (k + 1)) ≤ (η + R.d k / (1 - R.c₂)) / R.q k * V η (R.H k) := by
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    positivity
  have hVw : ∀ k, V η (R.H k) =
      ScalarHierarchy.weightedPotential n (K0 / η) (principalSum (R.H k)) := fun k =>
    (hV η hη _ (R.positive_definite k)).trans
      (BfgsCoverage.Article.Energy.potential_eq_weighted n _ _)
  have hq := R.q_pos k
  have hstep := ScalarHierarchy.weighted_step n (principalSum (R.H k))
    (principalSum (R.H (k + 1))) (R.q k) K0 η (R.d k / (1 - R.c₂)) hK0nn hη
    (principalSum_nonneg (R.positive_definite k).posSemidef) (principalSum_terminal (R.H k))
    (fun j hj hjn => BfgsCoverage.Article.Energy.normalized_hierarchy R ⟨G, hgG⟩
      hsum.tendsto_atTop_zero G hG hgG K0 hK0 k j hj hjn)
  rw [← hVw k, ← hVw (k + 1)] at hstep
  rw [div_mul_eq_mul_div, le_div_iff₀ hq]
  linarith

/-- AM--GM for positive reals in product form: if $\sum_{i<m}x_i\le mB$ then
$\prod_{i<m}x_i\le B^m$ (from the library's logarithmic form). -/
theorem prod_le_pow_of_sum_le (x : ℕ → ℝ) (m : ℕ) (B : ℝ) (hx : ∀ i, 0 < x i) (hB : 0 < B)
    (hsum : ∑ i ∈ Finset.range m, x i ≤ (m : ℝ) * B) :
    ∏ i ∈ Finset.range m, x i ≤ B ^ m := by
  have h := QuantitativeGrowth.sum_log_le_of_sum_le x m B hx hB hsum
  have hprod : ∏ i ∈ Finset.range m, x i = Real.exp (∑ i ∈ Finset.range m, Real.log (x i)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hx i)).symm
  have hpow : B ^ m = Real.exp ((m : ℝ) * Real.log B) := by
    rw [Real.exp_nat_mul, Real.exp_log hB]
  rw [hprod, hpow]
  exact Real.exp_le_exp.mpr h

/-- Item `C/02_M/disp/023` (`companion/chapters/02_M.tex:162-166`), in the proof of Theorem
`M:superquadratic`. Under the assumptions of display `C/02_M/disp/022` (the given $\eta>0$ and
$m\ge2$), iterating for $m-1$ steps, using the endpoint bound for $q_{J+m-1}$ and
arithmetic--geometric mean:
\[ \prod_{k=J}^{J+m-1}q_k\le G^2V_\eta(H_J)\prod_{k=J}^{J+m-2}(\eta+d_k/c)
   \le G^2V_\eta(H_J)\Bigl(\eta+\frac{D_J}{c(m-1)}\Bigr)^{m-1}. \] -/
theorem product_bound {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) (hsum : Summable R.d)
    (J : ℕ) (DJ : ℝ) (hDJ : DJ = ∑' i, R.d (J + i))
    (K0 : ℝ) (hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2)
    (V : ℝ → Mat n → ℝ)
    (hV : ∀ η : ℝ, 0 < η → ∀ H : Mat n, H.PosDef →
      V η H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j)
    (η : ℝ) (hη : 0 < η) (m : ℕ) (hm : 2 ≤ m) :
    ∏ k ∈ Finset.Ico J (J + m), R.q k ≤
        G ^ 2 * V η (R.H J) * ∏ k ∈ Finset.Ico J (J + m - 1), (η + R.d k / (1 - R.c₂)) ∧
      G ^ 2 * V η (R.H J) * ∏ k ∈ Finset.Ico J (J + m - 1), (η + R.d k / (1 - R.c₂)) ≤
        G ^ 2 * V η (R.H J) * (η + DJ / ((1 - R.c₂) * ((m : ℝ) - 1))) ^ (m - 1) := by
  have hc := R.wolfe_constant_pos
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    positivity
  have hVpos : ∀ k, 0 < V η (R.H k) := fun k =>
    lt_of_lt_of_le (mul_pos (R.q_pos k) (inv_pos.mpr (pow_pos hG 2)))
      (by
        have h := q_le_potential R G hgG K0 hK0nn η hη (V η) (hV η hη) k
        rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hG 2)]
        linarith)
  have ha : ∀ k, 0 < η + R.d k / (1 - R.c₂) := fun k =>
    add_pos_of_pos_of_nonneg hη (div_nonneg (R.d_pos k).le hc.le)
  have hstep : ∀ k, R.q k * V η (R.H (k + 1)) ≤ (η + R.d k / (1 - R.c₂)) * V η (R.H k) := by
    intro k
    have h := weighted_step R G hG hgG hsum J DJ hDJ K0 hK0 V hV η hη m hm k
    rw [div_mul_eq_mul_div, le_div_iff₀ (R.q_pos k)] at h
    linarith
  have htel : ∀ i : ℕ, (∏ l ∈ Finset.range i, R.q (J + l)) * V η (R.H (J + i)) ≤
      (∏ l ∈ Finset.range i, (η + R.d (J + l) / (1 - R.c₂))) * V η (R.H J) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← add_assoc]
      have hP : 0 ≤ ∏ l ∈ Finset.range i, R.q (J + l) :=
        Finset.prod_nonneg fun l _ => (R.q_pos _).le
      calc (∏ l ∈ Finset.range i, R.q (J + l)) * R.q (J + i) * V η (R.H (J + i + 1))
          = (∏ l ∈ Finset.range i, R.q (J + l)) * (R.q (J + i) * V η (R.H (J + i + 1))) := by
            ring
        _ ≤ (∏ l ∈ Finset.range i, R.q (J + l)) *
            ((η + R.d (J + i) / (1 - R.c₂)) * V η (R.H (J + i))) :=
            mul_le_mul_of_nonneg_left (hstep (J + i)) hP
        _ = (η + R.d (J + i) / (1 - R.c₂)) *
            ((∏ l ∈ Finset.range i, R.q (J + l)) * V η (R.H (J + i))) := by ring
        _ ≤ (η + R.d (J + i) / (1 - R.c₂)) *
            ((∏ l ∈ Finset.range i, (η + R.d (J + l) / (1 - R.c₂))) * V η (R.H J)) :=
            mul_le_mul_of_nonneg_left ih (ha _).le
        _ = _ := by ring
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 1 ≤ m' := by omega
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range,
    show J + (m' + 1) - J = m' + 1 by omega, show J + (m' + 1) - 1 - J = m' by omega,
    show m' + 1 - 1 = m' by omega]
  constructor
  · rw [Finset.prod_range_succ]
    have hP : 0 ≤ ∏ l ∈ Finset.range m', R.q (J + l) :=
      Finset.prod_nonneg fun l _ => (R.q_pos _).le
    calc (∏ l ∈ Finset.range m', R.q (J + l)) * R.q (J + m')
        ≤ (∏ l ∈ Finset.range m', R.q (J + l)) * (G ^ 2 * V η (R.H (J + m'))) :=
          mul_le_mul_of_nonneg_left (q_le_potential R G hgG K0 hK0nn η hη (V η) (hV η hη) _) hP
      _ = G ^ 2 * ((∏ l ∈ Finset.range m', R.q (J + l)) * V η (R.H (J + m'))) := by ring
      _ ≤ G ^ 2 * ((∏ l ∈ Finset.range m', (η + R.d (J + l) / (1 - R.c₂))) * V η (R.H J)) :=
          mul_le_mul_of_nonneg_left (htel m') (sq_nonneg G)
      _ = _ := by ring
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg G) (hVpos J).le)
    have hm'R : (0 : ℝ) < m' := by exact_mod_cast hm'
    have hcastm : ((m' + 1 : ℕ) : ℝ) - 1 = (m' : ℝ) := by
      push_cast
      ring
    rw [hcastm]
    apply prod_le_pow_of_sum_le _ m' _ (fun i => ha (J + i))
      (add_pos_of_pos_of_nonneg hη (div_nonneg (hDJ ▸ tsum_nonneg fun i => (R.d_pos _).le)
        (mul_nonneg hc.le hm'R.le)))
    have hpart : ∑ l ∈ Finset.range m', R.d (J + l) ≤ DJ := by
      rw [hDJ]
      exact (R.shift_summable_d hsum J).sum_le_tsum _ fun i _ => (R.d_pos _).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div]
    have h1 : (∑ l ∈ Finset.range m', R.d (J + l)) / (1 - R.c₂) ≤ DJ / (1 - R.c₂) :=
      div_le_div_of_nonneg_right hpart hc.le
    have h2 : (m' : ℝ) * (DJ / ((1 - R.c₂) * (m' : ℝ))) = DJ / (1 - R.c₂) := by
      field_simp
      ring
    nlinarith

/-- Item `C/02_M/disp/024` (`companion/chapters/02_M.tex:168-170`), in the proof of Theorem
`M:superquadratic`. Under the assumptions of the theorem, with the tail $J$ fixed and
$D_J=\sum_{k\ge J}d_k$ (choosing $\eta=D_J/[c(m-1)]$ for each horizon $m$),
\[ \liminf_{N\to\infty}N^{-2}\sum_{k<N}q_k^{-1}\ge\frac{c}{2D_J}. \]
Stated twice: every $a<c/(2D_J)$ is eventually a lower bound for $N^{-2}\sum_{k<N}q_k^{-1}$
(the meaning of the inequality); and the $\liminf$ in the extended reals `EReal` is at least
$c/(2D_J)$ (a real-valued $\liminf$ is not used, since the sequence is unbounded). Proved along
the text's route by the library's `QuantitativeGrowth.hierarchy_fixed_tail_lower_eventually`. -/
theorem liminf_bound {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) (hsum : Summable R.d)
    (J : ℕ) (DJ : ℝ) (hDJ : DJ = ∑' i, R.d (J + i))
    (K0 : ℝ) (_hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2)
    (V : ℝ → Mat n → ℝ)
    (_hV : ∀ η : ℝ, 0 < η → ∀ H : Mat n, H.PosDef →
      V η H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) :
    (∀ a : ℝ, a < (1 - R.c₂) / (2 * DJ) →
      ∀ᶠ N : ℕ in atTop, a ≤ 1 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹) ∧
      (((1 - R.c₂) / (2 * DJ) : ℝ) : EReal) ≤
        liminf (fun N : ℕ => ((1 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ : ℝ) : EReal))
          atTop := by
  have hc := R.wolfe_constant_pos
  have hDJpos : 0 < DJ := by
    rw [hDJ]
    exact (R.shift_summable_d hsum J).tsum_pos (fun i => (R.d_pos (J + i)).le) 0 (R.d_pos (J + 0))
  have hg2 : ∀ k, sqNorm (R.toFullBFGSRun.g k) ≤ G ^ 2 := fun k =>
    BfgsCoverage.Article.Energy.sqNorm_le_of_norm_le (hgG k)
  have NH := fullBFGS_normalizedHierarchy R.toFullBFGSRun G (1 - R.c₂) hG hc hg2
    R.beta_lower_bound
  have hbudget : ∀ m, ∑ i ∈ Finset.range m, R.toFullBFGSRun.d (J + i) / (1 - R.c₂) ≤
      DJ / (1 - R.c₂) := by
    intro m
    rw [← Finset.sum_div, hDJ]
    exact div_le_div_of_nonneg_right
      ((R.shift_summable_d hsum J).sum_le_tsum _ fun i _ => (R.d_pos _).le) hc.le
  have hev : ∀ a : ℝ, a < (1 - R.c₂) / (2 * DJ) →
      ∀ᶠ N : ℕ in atTop, a ≤ 1 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ := by
    intro a ha
    have ha' : a < (2 * (DJ / (1 - R.c₂)))⁻¹ := by
      have heq : (2 * (DJ / (1 - R.c₂)))⁻¹ = (1 - R.c₂) / (2 * DJ) := by
        field_simp
      rw [heq]
      exact ha
    have h := QuantitativeGrowth.hierarchy_fixed_tail_lower_eventually NH
      (fun k => div_nonneg (R.d_pos k).le hc.le) J (DJ / (1 - R.c₂)) (div_pos hDJpos hc)
      hbudget a ha'
    refine h.mono fun N hN => ?_
    rw [one_div, ← div_eq_inv_mul]
    exact hN
  refine ⟨hev, ?_⟩
  apply le_of_forall_lt_imp_le_of_dense
  intro x hx
  induction x using EReal.rec with
  | bot => exact bot_le
  | coe a =>
    have ha : a < (1 - R.c₂) / (2 * DJ) := EReal.coe_lt_coe_iff.mp hx
    exact Filter.le_liminf_of_le (by isBoundedDefault)
      ((hev a ha).mono fun N hN => EReal.coe_le_coe_iff.mpr hN)
  | top => exact absurd hx (not_lt.mpr le_top)

/-- Item `C/02_M/prose/013` (`companion/chapters/02_M.tex:173`): "The finite-horizon bound
and the weaker-assumption geometric-mean theorem are retained alongside the strongest
summable-budget asymptotic statement." The comparisons it asserts: the assumption $d_k\to0$ of
Theorem `M:average` is weaker than $\sum_kd_k<\infty$ of Theorem `M:superquadratic`; and the
conclusion \eqref{M:superquad} is the stronger one, since $\frac1{N^2}\sum_{k<N}q_k^{-1}\to\infty$
implies $\frac1N\sum_{k<N}q_k^{-1}\to\infty$. -/
theorem retained_comparison {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (Summable R.d → Tendsto R.d atTop (𝓝 0)) ∧
      (Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop →
        Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop) := by
  refine ⟨fun hs => hs.tendsto_atTop_zero, fun h => ?_⟩
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hS : 0 ≤ ∑ k ∈ Finset.range N, (R.q k)⁻¹ :=
    Finset.sum_nonneg fun k _ => (inv_pos.mpr (R.q_pos k)).le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hle : 1 / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact mul_le_mul_of_nonneg_right hle hS

/-! ### Section `M:energy`: the fixed-reference energy -/

/-- Item `C/02_M/disp/025` (`companion/chapters/02_M.tex:183-185`), with the definitions of the
sentence that introduces it, Item `C/02_M/prose/014` (`companion/chapters/02_M.tex:182`): "For
any fixed reference point $x_*$ define $r_k=x_k-x_*$, $a_k=g_k^Tr_k$, $E_k=r_k^TB_kr_k$ and
$R_k=(y_k^Tr_{k+1})^2/t_k$." These are the library's `R.referencePairing xstar k`,
`R.referenceEnergy xstar k` and `R.referenceCorrection xstar k`; $R_k$ is the variable `Rk`
(`R` names the run). -/
theorem reference_notation {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (r k))
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (k : ℕ) :
    a k = R.referencePairing xstar k ∧ E k = R.referenceEnergy xstar k ∧
      Rk k = R.referenceCorrection xstar k := by
  obtain ⟨h1, h2, h3⟩ := BfgsCoverage.Article.Energy.reference_notation R xstar r hr E hE a ha
    Rk hRk k
  exact ⟨h2, h1, h3⟩

/-- Item `C/02_M/disp/026`, equation `M:fixedenergy` (`companion/chapters/02_M.tex:187-189`),
with the claim of the sentence that introduces it, Item `C/02_M/prose/015`
(`companion/chapters/02_M.tex:186`): expansion of \eqref{M:hessian} at
$r_{k+1}=r_k-\alpha_kH_kg_k$ gives exactly
\[ E_{k+1}=E_k-\frac{a_k^2}{q_k}+R_k \]
for every fixed $x_*$ and every $k$ (notation of `reference_notation`). -/
theorem fixed_energy {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (r k))
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (k : ℕ) :
    r (k + 1) = r k - R.α k • (R.H k *ᵥ R.g k) ∧ E (k + 1) = E k - a k ^ 2 / R.q k + Rk k := by
  refine ⟨?_, (BfgsCoverage.Article.Energy.reference_energy R xstar r hr E hE a ha Rk hRk
    (F xstar) rfl).1 k⟩
  rw [hr, hr, R.step k]
  change R.x k + -R.α k • (R.H k *ᵥ R.g k) - xstar = R.x k - xstar - R.α k • (R.H k *ᵥ R.g k)
  rw [neg_smul]
  abel

/-- Item `C/02_M/prose/016` (`companion/chapters/02_M.tex:190`): "The cancellation is
$-2\alpha a+\alpha^2q-(a-\alpha q)^2/q=-a^2/q$." For every fixed $x_*$ and every $k$, with
$a=a_k$, $\alpha=\alpha_k$, $q=q_k$:
$-2\alpha_ka_k+\alpha_k^2q_k-(a_k-\alpha_kq_k)^2/q_k=-a_k^2/q_k$. -/
theorem cancellation {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (_hr : ∀ k, r k = R.x k - xstar)
    (a : ℕ → ℝ) (_ha : ∀ k, a k = dot (R.g k) (r k)) (k : ℕ) :
    -2 * R.α k * a k + R.α k ^ 2 * R.q k - (a k - R.α k * R.q k) ^ 2 / R.q k =
      -a k ^ 2 / R.q k := by
  have hq := (R.q_pos k).ne'
  field_simp
  ring

/-- Item `C/02_M/prose/017` (`companion/chapters/02_M.tex:190`): "If $x_*$ is a minimizer,
convexity gives $a_k\ge F(x_k)-F_*$." With $F_*=F(x_*)$: $a_k\ge F(x_k)-F_*$ for every $k$. -/
theorem pairing_ge_gap {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (_hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (r k)) (k : ℕ) :
    a k ≥ F (R.x k) - Fstar := by
  rw [ha, hr, hFstar]
  exact R.gap_le_referencePairing xstar k

/-- Item `C/02_M/disp/027`, equation `M:energybound` (`companion/chapters/02_M.tex:191-193`).
With the notation of `reference_notation`, if $x_*$ is a minimizer and $F_*=F(x_*)$, then for
every $N$
\[ [F(x_N)-F_*]^2\sum_{k<N}q_k^{-1}\le E_0+\sum_{k<N}R_k. \] -/
theorem energy_bound {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (r k))
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (N : ℕ) :
    (F (R.x N) - Fstar) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤
      E 0 + ∑ k ∈ Finset.range N, Rk k :=
  (BfgsCoverage.Article.Energy.reference_energy R xstar r hr E hE a ha Rk hRk Fstar hFstar).2
    hmin N

/-- A gap tending to zero excludes a positive gap. -/
theorem no_positive_gap {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (Fstar : ℝ)
    (h : Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar)) :
    ¬ ∃ η : ℝ, 0 < η ∧ ∀ k, F (R.x k) - Fstar ≥ η := by
  rintro ⟨η, hη, hgap⟩
  have hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 0) := by
    simpa using h.sub_const Fstar
  have := ge_of_tendsto' hlim hgap
  linarith

/-- The first claim of item `C/02_M/prose/018` in the form the deduction from
\eqref{M:energybound} actually gives: if $x_*$ is a minimizer, $\sum_{k<N}q_k^{-1}\to\infty$ and
$\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$, then $F(x_k)\to F_*$, so there is no positive gap.
Without $\sum_{k<N}q_k^{-1}\to\infty$ the bound gives nothing when all $R_k=0$; Theorem
`M:average` supplies the divergence under bounded gradients (see `negligible_corrections`). -/
theorem negligible_corrections_of_divergent {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (hdiv : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop)
    (ho : (fun N : ℕ => ∑ k ∈ Finset.range N, Rk k) =o[atTop]
      (fun N : ℕ => ∑ k ∈ Finset.range N, (R.q k)⁻¹)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      ¬ ∃ η : ℝ, 0 < η ∧ ∀ k, F (R.x k) - Fstar ≥ η := by
  have hRf : Rk = R.referenceCorrection xstar := funext fun k => by
    rw [hRk, hr]
    rfl
  subst hRf hFstar
  have hgap := EnergyBudget.energy_gap_tendsto_zero (R.referenceEnergy_nonneg xstar) R.q_pos
    (fun k => sub_nonneg.mpr (hmin (R.x k))) (R.gap_antitone xstar)
    (R.gap_le_referencePairing xstar) (R.fixed_reference_energy xstar) hdiv
    ho.tendsto_div_nhds_zero
  have hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
    simpa only [sub_add_cancel, zero_add] using hgap.add_const (F xstar)
  exact ⟨hlim, no_positive_gap R _ hlim⟩

/-- Item `C/02_M/prose/018` (`companion/chapters/02_M.tex:194`): "Thus, along runs with bounded
gradients, $\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$ excludes a positive gap." (The bounded gradients
are stated since 15 October 2026, wording point W1.) With the notation of
`reference_notation`, $x_*$ a minimizer and $F_*=F(x_*)$: if
$\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$ as $N\to\infty$, then $F(x_k)\to F_*$, i.e. no gap
$F(x_k)-F_*\ge\eta>0$ persists.

The deduction from \eqref{M:energybound} needs $\sum_{k<N}q_k^{-1}\to\infty$
(`negligible_corrections_of_divergent`), which Theorem `M:average` gives under bounded
gradients ($d_k\to0$ follows from the minimizer). The bounded gradients, which the sentence
states since 15 October 2026, are the hypothesis `hbdd` here, as in the library's
`objective_tendsto_min_of_negligible_corrections`. -/
theorem negligible_corrections {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (ho : (fun N : ℕ => ∑ k ∈ Finset.range N, Rk k) =o[atTop]
      (fun N : ℕ => ∑ k ∈ Finset.range N, (R.q k)⁻¹)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      ¬ ∃ η : ℝ, 0 < η ∧ ∀ k, F (R.x k) - Fstar ≥ η := by
  have hd : Tendsto R.d atTop (𝓝 0) :=
    R.predicted_decreases_tendsto_zero_of_lower_bound (F xstar) fun k => hmin (R.x k)
  have hmean := (average R hbdd hd).2
  have hdiv : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hmean
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hS : 0 ≤ ∑ k ∈ Finset.range N, (R.q k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (R.q_pos k)).le
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hN1
    calc 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ 1 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hS
      _ = _ := one_mul _
  exact negligible_corrections_of_divergent R xstar hmin Fstar hFstar r hr Rk hRk hdiv ho

/-- Item `C/02_M/prose/019` (`companion/chapters/02_M.tex:194`): "With the summability
assumptions of Theorem `M:superquadratic`, an $O(N^2)$ cumulative correction suffices." With
the notation of `reference_notation`, $x_*$ a minimizer and $F_*=F(x_*)$, under bounded
gradients and $\sum_kd_k<\infty$: if $\sum_{k<N}R_k=O(N^2)$, then $F(x_k)\to F_*$ (no positive
gap persists). -/
theorem quadratic_corrections {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (hO : (fun N : ℕ => ∑ k ∈ Finset.range N, Rk k) =O[atTop] (fun N : ℕ => (N : ℝ) ^ 2)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      ¬ ∃ η : ℝ, 0 < η ∧ ∀ k, F (R.x k) - Fstar ≥ η := by
  have hRf : Rk = R.referenceCorrection xstar := funext fun k => by
    rw [hRk, hr]
    rfl
  subst hRf hFstar
  obtain ⟨G, hG, hg⟩ := BfgsCoverage.Article.Energy.sqNorm_bound_of_bounded R.g hbdd
  obtain ⟨C, hC⟩ := hO.bound
  have hcor : ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ Finset.range N, R.referenceCorrection xstar k ≤ C * (N : ℝ) ^ 2 := by
    filter_upwards [hC] with N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (N : ℝ))] at hN
    exact (le_abs_self _).trans hN
  have hlim := R.objective_tendsto_min_of_quadratic_corrections xstar hmin G hG hg C hcor
  exact ⟨hlim, no_positive_gap R _ hlim⟩

/-! ### Section `M:energy`: moving frames -/

/-- Item `C/02_M/disp/029`, equation `M:frameidentity` (`companion/chapters/02_M.tex:201-203`),
under the supposition of display `C/02_M/disp/028` (lines 197-199) and the definitions of
Item `C/02_M/prose/021` (`companion/chapters/02_M.tex:200`). For frames
$V_k\in\R^{n\times r}$ with $V_{k+1}=V_kT_k+s_kb_k^T$ (`rectOuter s b` is $sb^T$), set
$A_k=V_k^TB_kV_k$, $a_k=V_k^Tg_k$, $c_k=V_{k+1}^Ty_k$. Then for every $k$
\[ A_{k+1}=T_k^T\Bigl(A_k-\frac{a_ka_k^T}{q_k}\Bigr)T_k+\frac{c_kc_k^T}{t_k}. \] -/
theorem frame_identity {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T : ℕ → Mat r) (b : ℕ → Vec r)
    (hV : ∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (A : ℕ → Mat r) (hA : ∀ k, A k = (V k)ᵀ * R.hessian k * V k)
    (a : ℕ → Vec r) (ha : ∀ k, a k = (V k)ᵀ *ᵥ R.g k)
    (c : ℕ → Vec r) (hc : ∀ k, c k = (V (k + 1))ᵀ *ᵥ R.gradientChange k) (k : ℕ) :
    A (k + 1) = (T k)ᵀ * (A k - (R.q k)⁻¹ • outer (a k) (a k)) * T k +
      (R.curvature k)⁻¹ • outer (c k) (c k) := by
  rw [hA, hA, ha, hc]
  exact R.moving_frame_energy k (V k) (V (k + 1)) (T k) (b k) (hV k)

/-- The trace identity of display `C/02_M/disp/030` at one step $k$, assuming only what it
uses: $V_{k+1}=V_kT_k+s_kb_k^T$, $P_k$ and $P_{k+1}$ invertible and $P_{k+1}=P_kT_k$. With the
notation of `frame_identity` and $\widetilde A_k=P_k^{-T}A_kP_k^{-1}$,
\[ \tr\widetilde A_{k+1}=\tr\widetilde A_k-\frac{\|P_k^{-T}a_k\|^2}{q_k}
   +\frac{\|P_{k+1}^{-T}c_k\|^2}{t_k}. \] -/
theorem normalized_trace_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T : ℕ → Mat r) (b : ℕ → Vec r) (P : ℕ → Mat r)
    (A : ℕ → Mat r) (hA : ∀ k, A k = (V k)ᵀ * R.hessian k * V k)
    (a : ℕ → Vec r) (ha : ∀ k, a k = (V k)ᵀ *ᵥ R.g k)
    (c : ℕ → Vec r) (hc : ∀ k, c k = (V (k + 1))ᵀ *ᵥ R.gradientChange k)
    (At : ℕ → Mat r) (hAt : ∀ k, At k = ((P k)⁻¹)ᵀ * A k * (P k)⁻¹) (k : ℕ)
    (hVk : V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (hPk : (P k).det ≠ 0) (hPk1 : (P (k + 1)).det ≠ 0) (hprod : P (k + 1) = P k * T k) :
    (At (k + 1)).trace = (At k).trace - sqNorm (((P k)⁻¹)ᵀ *ᵥ a k) / R.q k +
      sqNorm (((P (k + 1))⁻¹)ᵀ *ᵥ c k) / R.curvature k := by
  have hstep := MovingFrame.normalized_frame_step (V k) (V (k + 1)) (P k) (P (k + 1))
    (T k) (R.displacement k) (b k) hPk hPk1 hprod hVk
  have hident := R.moving_frame_energy k (V k * (P k)⁻¹) (V (k + 1) * (P (k + 1))⁻¹)
    1 (((P (k + 1))⁻¹)ᵀ *ᵥ b k) (by simpa only [Matrix.mul_one] using hstep)
  have hAt' : ∀ j, At j = metricGram (R.hessian j) (V j * (P j)⁻¹) := by
    intro j
    rw [hAt, hA, EnergyIdentities.gram_transport]
    rfl
  rw [hAt' (k + 1), hAt' k, hident, ha, hc]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, MovingFrame.trace_outer, Matrix.transpose_mul,
    ← Matrix.mulVec_mulVec, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Item `C/02_M/disp/030` (`companion/chapters/02_M.tex:205-210`). Under the supposition of
Item `C/02_M/prose/022` (`companion/chapters/02_M.tex:204`): on a tail $k\ge J$,
$\|a_k\|\ge\epsilon>0$, $\|c_k\|^2/t_k\le C$, and the cumulative products $P_J=I$,
$P_{k+1}=P_kT_k$ have bounded norms and bounded inverse norms (Euclidean operator norms;
$P_k$ invertible), congruence by $P_{k+1}^{-1}$ and a trace yield, for every $k\ge J$,
\[ \tr\widetilde A_{k+1}=\tr\widetilde A_k-\frac{\|P_k^{-T}a_k\|^2}{q_k}
   +\frac{\|P_{k+1}^{-T}c_k\|^2}{t_k},\qquad\widetilde A_k=P_k^{-T}A_kP_k^{-1}. \]
($P_k^{-T}$ is `((P k)⁻¹)ᵀ`.) The identity uses only the invertibility and the products; the
other suppositions are unused (`normalized_trace_step`). All the suppositions can hold (example
`logRun` at the end). -/
theorem normalized_trace {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T : ℕ → Mat r) (b : ℕ → Vec r)
    (hV : ∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (A : ℕ → Mat r) (hA : ∀ k, A k = (V k)ᵀ * R.hessian k * V k)
    (a : ℕ → Vec r) (ha : ∀ k, a k = (V k)ᵀ *ᵥ R.g k)
    (c : ℕ → Vec r) (hc : ∀ k, c k = (V (k + 1))ᵀ *ᵥ R.gradientChange k)
    (J : ℕ) (ε : ℝ) (_hε : 0 < ε) (_hvis : ∀ k, J ≤ k → ‖euclideanVector (a k)‖ ≥ ε)
    (C : ℝ) (_hcor : ∀ k, J ≤ k → sqNorm (c k) / R.curvature k ≤ C)
    (P : ℕ → Mat r) (_hPJ : P J = 1) (hprod : ∀ k, J ≤ k → P (k + 1) = P k * T k)
    (_hPbdd : ∃ K : ℝ, ∀ k, J ≤ k → FrameNorms.euclideanOpNorm (P k) ≤ K)
    (hPinv : ∀ k, J ≤ k → (P k).det ≠ 0)
    (_hPinvbdd : ∃ L : ℝ, ∀ k, J ≤ k → FrameNorms.euclideanOpNorm (P k)⁻¹ ≤ L)
    (At : ℕ → Mat r) (hAt : ∀ k, At k = ((P k)⁻¹)ᵀ * A k * (P k)⁻¹) :
    ∀ k, J ≤ k → (At (k + 1)).trace = (At k).trace - sqNorm (((P k)⁻¹)ᵀ *ᵥ a k) / R.q k +
      sqNorm (((P (k + 1))⁻¹)ᵀ *ᵥ c k) / R.curvature k :=
  fun k hk => normalized_trace_step R V T b P A hA a ha c hc At hAt k (hV k) (hPinv k hk)
    (hPinv (k + 1) (by omega)) (hprod k hk)

/-- Squared operator-norm bound in the library's coordinate form: $\|M\|\le K$ (Euclidean
operator norm) gives $\|M^Tv\|^2\le(K^2+1)\|v\|^2$ for every $v$. -/
theorem sqNorm_transpose_le {r : ℕ} (M : Mat r) (K : ℝ)
    (hM : FrameNorms.euclideanOpNorm M ≤ K) (v : Vec r) :
    sqNorm (Mᵀ *ᵥ v) ≤ (K ^ 2 + 1) * sqNorm v := by
  have hsq : FrameNorms.euclideanOpNorm M ^ 2 ≤ K ^ 2 + 1 := by
    have h0 : 0 ≤ FrameNorms.euclideanOpNorm M := norm_nonneg _
    nlinarith
  exact ((FrameNorms.operatorSqBound_iff_opNorm_sq M (K ^ 2 + 1) (by positivity)).mpr hsq) v

/-- Item `C/02_M/prose/023` (`companion/chapters/02_M.tex:211`): "Positivity gives
$\sum_{J\le k<N}q_k^{-1}=O(N)$, contradicting Theorem `M:average` under its hypotheses." ("under
its hypotheses" added on 15 October 2026, wording point W2.) Under the suppositions of
display `C/02_M/disp/030` (frames $V_{k+1}=V_kT_k+s_kb_k^T$; on the tail $k\ge J$:
$\|a_k\|\ge\epsilon>0$, $\|c_k\|^2/t_k\le C$, $P_J=I$, $P_{k+1}=P_kT_k$ with bounded norms and
bounded inverse norms): $\sum_{J\le k<N}q_k^{-1}=O(N)$; and this contradicts Theorem
`M:average`, i.e. the suppositions cannot hold together with the hypotheses of that theorem
(bounded gradients and $d_k\to0$). The suppositions alone are satisfiable (example
`logRun` at the end: bounded gradients, $d_k=1$); "nonoptimal" (line 204) is descriptive and not
a hypothesis here. -/
theorem frame_criterion {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {r : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin r) ℝ) (T : ℕ → Mat r) (b : ℕ → Vec r)
    (hV : ∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k))
    (a : ℕ → Vec r) (ha : ∀ k, a k = (V k)ᵀ *ᵥ R.g k)
    (c : ℕ → Vec r) (hc : ∀ k, c k = (V (k + 1))ᵀ *ᵥ R.gradientChange k)
    (J : ℕ) (ε : ℝ) (hε : 0 < ε) (hvis : ∀ k, J ≤ k → ‖euclideanVector (a k)‖ ≥ ε)
    (C : ℝ) (hcor : ∀ k, J ≤ k → sqNorm (c k) / R.curvature k ≤ C)
    (P : ℕ → Mat r) (_hPJ : P J = 1) (hprod : ∀ k, J ≤ k → P (k + 1) = P k * T k)
    (hPbdd : ∃ K : ℝ, ∀ k, J ≤ k → FrameNorms.euclideanOpNorm (P k) ≤ K)
    (hPinv : ∀ k, J ≤ k → (P k).det ≠ 0)
    (hPinvbdd : ∃ L : ℝ, ∀ k, J ≤ k → FrameNorms.euclideanOpNorm (P k)⁻¹ ≤ L) :
    ((fun N : ℕ => ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹) =O[atTop] (fun N : ℕ => (N : ℝ))) ∧
      ((∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) → Tendsto R.d atTop (𝓝 0) → False) := by
  obtain ⟨K, hK⟩ := hPbdd
  obtain ⟨L, hL⟩ := hPinvbdd
  have hm : 0 < ε ^ 2 := by positivity
  have hvis' : ∀ k, J ≤ k → ε ^ 2 ≤ sqNorm ((V k)ᵀ *ᵥ R.g k) := by
    intro k hk
    rw [← ha, ← euclid_norm_sq]
    exact pow_le_pow_left₀ hε.le (hvis k hk) 2
  have hcor' : ∀ k, J ≤ k →
      sqNorm ((V (k + 1))ᵀ *ᵥ R.gradientChange k) / R.curvature k ≤ C := by
    intro k hk
    rw [← hc]
    exact hcor k hk
  have htr : ∀ k, J ≤ k → ∀ v, sqNorm ((P k)ᵀ *ᵥ v) ≤ (K ^ 2 + 1) * sqNorm v :=
    fun k hk v => sqNorm_transpose_le (P k) K (hK k hk) v
  have hinv : ∀ k, J ≤ k → ∀ v, sqNorm (((P k)⁻¹)ᵀ *ᵥ v) ≤ (L ^ 2 + 1) * sqNorm v :=
    fun k hk v => sqNorm_transpose_le ((P k)⁻¹) L (hL k hk) v
  have hK1 : 0 < K ^ 2 + 1 := by positivity
  have hL1 : 0 ≤ L ^ 2 + 1 := by positivity
  refine ⟨?_, fun hbdd hd => ?_⟩
  · set S := R.shift J
    have hbound := S.moving_frame_reciprocal_sum_bound (fun k => V (J + k)) (fun k => T (J + k))
      (fun k => P (J + k)) (fun k => b (J + k)) (fun k => hPinv (J + k) (Nat.le_add_right J k))
      (fun k => hprod (J + k) (Nat.le_add_right J k)) (fun k => hV (J + k)) (ε ^ 2)
      (K ^ 2 + 1) (L ^ 2 + 1) C hK1 hL1 (fun k => hvis' (J + k) (Nat.le_add_right J k))
      (fun k => hcor' (J + k) (Nat.le_add_right J k))
      (fun k => htr (J + k) (Nat.le_add_right J k)) (fun k => hinv (J + k) (Nat.le_add_right J k))
    set E0 := S.normalizedFrameEnergy (fun k => V (J + k)) (fun k => P (J + k)) 0 with hE0
    have hE0nn : 0 ≤ E0 := S.normalizedFrameEnergy_nonneg _ _ 0
    set B := (K ^ 2 + 1) / ε ^ 2 * (E0 + |(L ^ 2 + 1) * C|) with hB
    apply Asymptotics.IsBigO.of_bound B
    filter_upwards [eventually_ge_atTop (max J 1)] with N hN
    have hJN : J ≤ N := le_of_max_le_left hN
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hS : 0 ≤ ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (R.q_pos k)).le
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS, abs_of_nonneg (by positivity)]
    have hsum_eq : ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹ =
        ∑ k ∈ Finset.range (N - J), (S.q k)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range]
      rfl
    have h1 := hbound (N - J)
    rw [← hsum_eq] at h1
    have hNJ : ((N - J : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N J
    have hLC : (L ^ 2 + 1) * C * ((N - J : ℕ) : ℝ) ≤ |(L ^ 2 + 1) * C| * N := by
      calc (L ^ 2 + 1) * C * ((N - J : ℕ) : ℝ) ≤ |(L ^ 2 + 1) * C| * ((N - J : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
        _ ≤ |(L ^ 2 + 1) * C| * N := mul_le_mul_of_nonneg_left hNJ (abs_nonneg _)
    have hstep : ε ^ 2 / (K ^ 2 + 1) * ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹ ≤
        (E0 + |(L ^ 2 + 1) * C|) * N := by
      have hE0N : E0 ≤ E0 * N := le_mul_of_one_le_right hE0nn hN1R
      nlinarith
    have hcoef : 0 < ε ^ 2 / (K ^ 2 + 1) := div_pos hm hK1
    have hinvc : (K ^ 2 + 1) / ε ^ 2 = (ε ^ 2 / (K ^ 2 + 1))⁻¹ := by rw [inv_div]
    rw [hB, mul_assoc, hinvc, ← div_eq_inv_mul, le_div_iff₀ hcoef,
      mul_comm (∑ k ∈ Finset.Ico J N, (R.q k)⁻¹)]
    exact hstep
  · obtain ⟨G, hG, hg⟩ := BfgsCoverage.Article.Energy.sqNorm_bound_of_bounded R.g hbdd
    exact R.moving_frame_tail_criterion J V T P b hPinv hprod (fun k _ => hV k) (ε ^ 2)
      (K ^ 2 + 1) (L ^ 2 + 1) C hm hK1 hL1 hvis' hcor' htr hinv G hG hg hd

/-! ### Section `M:residual` -/

/-- The Euclidean inner product is `dot`. -/
theorem euclid_inner_eq_dot {n : ℕ} (g v : Vec n) :
    inner (euclideanVector g) (euclideanVector v) = dot g v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _

/-- For a matrix `U` with orthonormal columns spanning the subspace `S`, the orthogonal
projection onto `S` is `U * Uᵀ` in coordinates: $P_Sv=UU^Tv$. -/
theorem orthogonalProjection_eq {n r : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hS : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ S ↔ ∃ a : Vec r, U *ᵥ a = fun i => x i)
    (v : Vec n) :
    (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)) =
      euclideanVector ((U * Uᵀ) *ᵥ v) := by
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · rw [hS]
    exact ⟨Uᵀ *ᵥ v, by rw [Matrix.mulVec_mulVec]; rfl⟩
  · intro w hw
    obtain ⟨a, ha⟩ := (hS w).mp hw
    have hw' : w = euclideanVector (U *ᵥ a) := by
      rw [ha]
      rfl
    rw [hw', ← euclideanVector_sub, euclid_inner_eq_dot]
    change (v - (U * Uᵀ) *ᵥ v) ⬝ᵥ (U *ᵥ a) = 0
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self, zero_dotProduct]

/-- Every subspace has an orthonormal basis matrix `U`, and then
$\|P_Sv\|^2=\|U^Tv\|^2$ for every $v$. -/
theorem projection_basis {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ (r : ℕ) (U : Matrix (Fin n) (Fin r) ℝ), Uᵀ * U = 1 ∧
      (∀ x : EuclideanSpace ℝ (Fin n), x ∈ S ↔ ∃ a : Vec r, U *ᵥ a = fun i => x i) ∧
      ∀ v : Vec n, ‖(S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
        sqNorm (Uᵀ *ᵥ v) := by
  obtain ⟨U, hU, hS⟩ := FrameNorms.orthonormal_matrix_for_subspace S
  refine ⟨_, U, hU, hS, fun v => ?_⟩
  rw [orthogonalProjection_eq S U hU hS v, euclid_norm_sq, SmoothSubspace.sqNorm_projection U hU]

/-- Columns in `S` (the range condition $\operatorname{range}R\subset S$) give $UU^TR=R$. -/
theorem range_projection {n r p : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hS : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ S ↔ ∃ a : Vec r, U *ᵥ a = fun i => x i)
    (W : Matrix (Fin n) (Fin p) ℝ) (hW : ∀ v : Vec p, euclideanVector (W *ᵥ v) ∈ S) :
    (U * Uᵀ) * W = W := by
  rw [SmoothSubspace.projection_columns_iff U hU W]
  intro j
  obtain ⟨a, ha⟩ := (hS _).mp (hW (Pi.single j 1))
  refine ⟨a, ha.trans ?_⟩
  funext i
  change (W *ᵥ Pi.single j 1) i = W i j
  rw [Matrix.mulVec_single_one]
  rfl

/-- Item `C/02_M/theorem/M:residualtheorem` (`companion/chapters/02_M.tex:220-237`), Theorem
`M:residualtheorem` (Residuals in fixed smooth directions), with its displays
`C/02_M/disp/031` to `C/02_M/disp/034`.

Assume bounded gradients, fixed weak Wolfe and $\sum d_k<\infty$. For a fixed subspace $S$
(of Euclidean $\R^n$) with orthogonal projection $P_S$, suppose $\|P_Sy_k\|^2\le L_St_k$ for all
$k$. A tail $k\ge J$ cannot simultaneously admit frames $V_k\in\R^{n\times p}$ (any width
$p$), matrices $T_k$, vectors $b_k$ and residuals $R_k$ with
\[ \|V_k^Tg_k\|^2\ge m>0,\qquad\|V_{k+1}^Ty_k\|^2\le C_0t_k,\qquad
   V_{k+1}=V_kT_k+s_kb_k^T+R_k, \]
\[ \|T_k\|_{\rm op}^2\le1+C_Td_k,\quad\operatorname{range}R_k\subset S,
   \quad\|R_k\|_F^2\le C_Rd_k. \]
No full-rank frame or invertible transport is required (none is assumed). Norms: Euclidean;
$\|T\|_{\rm op}$ is `FrameNorms.euclideanOpNorm T`; $\|R\|_F^2$ is `SmoothSubspace.frobSq R`,
the sum of the squared entries; $R_k$ is `Rres k` (`R` names the run). The constants
$m,C_0,C_T,C_R$ are arbitrary reals. The library proves this with the smoothness bound needed
only on the tail (`residual_frames_on_tail_incompatible_source`). -/
theorem residual_theorem {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k) :
    ¬ ∃ (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
        (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ), 0 < m ∧
        ∀ k, J ≤ k →
          ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
          ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
          V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
          FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
          (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
          SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k := by
  rintro ⟨J, p, V, T, b, Rres, m, C0, CT, CR, hm, hfr⟩
  obtain ⟨r, U, hU, hS, hproj⟩ := projection_basis S
  obtain ⟨G, hG, hg⟩ := BfgsCoverage.Article.Energy.sqNorm_bound_of_bounded R.g hbdd
  have hsm : ∀ k, sqNorm (Uᵀ *ᵥ (R.shift J).gradientChange k) ≤ LS * (R.shift J).curvature k :=
    fun k => by rw [← hproj]; exact hsmooth (J + k)
  refine R.residual_frames_on_tail_incompatible_source J G hG hg hsum U hU LS m C0 CT CR hm hsm
    (fun k => V (J + k)) (fun k => Rres (J + k)) (fun k => T (J + k)) (fun k => b (J + k))
    (fun k => ?_) (fun k => ?_) (fun k => (hfr (J + k) (Nat.le_add_right J k)).2.2.1)
    (fun k => ?_) (fun k => ?_) (fun k => (hfr (J + k) (Nat.le_add_right J k)).2.2.2.2.2)
  · have h := (hfr (J + k) (Nat.le_add_right J k)).1
    rw [euclid_norm_sq] at h
    exact h
  · have h := (hfr (J + k) (Nat.le_add_right J k)).2.1
    rw [euclid_norm_sq] at h
    exact h
  · have h := (hfr (J + k) (Nat.le_add_right J k)).2.2.2.1
    have h0 : 0 ≤ 1 + CT * (R.shift J).d k :=
      (sq_nonneg (FrameNorms.euclideanOpNorm (T (J + k)))).trans h
    exact (FrameNorms.operatorSqBound_iff_opNorm_sq _ _ h0).mpr h
  · exact range_projection S U hU hS _ (hfr (J + k) (Nat.le_add_right J k)).2.2.2.2.1

/-! #### Displays of the proof of Theorem `M:residualtheorem`

The proof argues by contradiction: its standing assumptions are the theorem's hypotheses
together with frames on a tail (the existential that the theorem denies), so they cannot all
hold. Each display is therefore stated twice: under the full standing assumptions of the proof
at that point (as the text has it), and in a general form with only the hypotheses it uses
(one step $k$), whose assumptions are satisfiable (examples at the end). $P_S$ is a matrix `PS`
representing the orthogonal projection onto $S$ (`hPS`); $E_k$, $M_k$, $C_S$ are variables with
their defining equations. -/

/-- The matrix of the orthogonal projection onto `S` is `U * Uᵀ` for an orthonormal basis
matrix `U` of `S`. -/
theorem projection_matrix_eq {n r : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hS : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ S ↔ ∃ a : Vec r, U *ᵥ a = fun i => x i)
    (PS : Mat n) (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n))) :
    PS = U * Uᵀ := by
  apply Matrix.ext_of_mulVec_single
  intro i
  have h := hPS (Pi.single i 1)
  rw [orthogonalProjection_eq S U hU hS] at h
  exact (WithLp.equiv 2 (Vec n)).symm.injective h

/-- The general form of display `C/02_M/disp/035` at one step $k$: if $\|P_Sy_k\|^2\le L_St_k$,
\[ \tr(P_SB_{k+1})=\tr(P_SB_k)-\frac{\|P_Sg_k\|^2}{q_k}+\frac{\|P_Sy_k\|^2}{t_k}
   \le\tr(P_SB_k)+L_S. \] -/
theorem projection_trace_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (PS : Mat n)
    (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (LS : ℝ) (k : ℕ)
    (hsmooth : ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k) :
    (PS * R.hessian (k + 1)).trace =
        (PS * R.hessian k).trace - ‖euclideanVector (PS *ᵥ R.g k)‖ ^ 2 / R.q k +
          ‖euclideanVector (PS *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k ∧
      (PS * R.hessian k).trace - ‖euclideanVector (PS *ᵥ R.g k)‖ ^ 2 / R.q k +
          ‖euclideanVector (PS *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k ≤
        (PS * R.hessian k).trace + LS := by
  obtain ⟨r, U, hU, hS, _⟩ := projection_basis S
  have hPSU := projection_matrix_eq S U hU hS PS hPS
  have ht := R.curvature_pos k
  have hq := R.q_pos k
  refine ⟨?_, ?_⟩
  · rw [euclid_norm_sq, euclid_norm_sq, hPSU]
    exact R.smooth_subspace_projection_trace_update U hU k
  · rw [← hPS] at hsmooth
    have h1 : ‖euclideanVector (PS *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k ≤ LS :=
      (div_le_iff₀ ht).mpr hsmooth
    have h2 : 0 ≤ ‖euclideanVector (PS *ᵥ R.g k)‖ ^ 2 / R.q k := by positivity
    linarith

/-- Item `C/02_M/disp/035` (`companion/chapters/02_M.tex:240-245`), in the proof of Theorem
`M:residualtheorem`. Under the standing assumptions of the proof (the theorem's hypotheses and
the frames on the tail $J$ that the proof assumes), with $P_S$ the projection matrix, taking the
trace of \eqref{M:hessian} on $S$ gives, for every $k$,
\[ \tr(P_SB_{k+1})=\tr(P_SB_k)-\frac{\|P_Sg_k\|^2}{q_k}+\frac{\|P_Sy_k\|^2}{t_k}
   \le\tr(P_SB_k)+L_S. \] -/
theorem projection_trace {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ) (_hm : 0 < m)
    (_hfr : ∀ k, J ≤ k →
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k)
    (PS : Mat n) (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    (PS * R.hessian (k + 1)).trace =
        (PS * R.hessian k).trace - ‖euclideanVector (PS *ᵥ R.g k)‖ ^ 2 / R.q k +
          ‖euclideanVector (PS *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k ∧
      (PS * R.hessian k).trace - ‖euclideanVector (PS *ᵥ R.g k)‖ ^ 2 / R.q k +
          ‖euclideanVector (PS *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k ≤
        (PS * R.hessian k).trace + LS :=
  projection_trace_step R S PS hPS LS k (hsmooth k)

/-- The general form of display `C/02_M/disp/036` at one step $k$: if
$V_{k+1}=V_kT_k+s_kb_k^T+R_k$, then with $E_k=\tr(V_k^TB_kV_k)$ and $M_k$ of
\eqref{M:annihilation},
\[ E_{k+1}=\tr\bigl[(V_kT_k+R_k)^TM_k(V_kT_k+R_k)\bigr]+\frac{\|V_{k+1}^Ty_k\|^2}{t_k}. \] -/
theorem frame_energy_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {p : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ)
    (hVk : V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k) :
    E (k + 1) = ((V k * T k + Rres k)ᵀ * M k * (V k * T k + Rres k)).trace +
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k := by
  have hremove : metricGram (M k) (V (k + 1)) = metricGram (M k) (V k * T k + Rres k) := by
    have hw : V (k + 1) = (V k * T k + Rres k) +
        EnergyIdentities.rectOuter (R.displacement k) (b k) := by
      rw [hVk]
      abel
    rw [hw, hM]
    exact EnergyIdentities.gram_add_kernel (R.annihilated_hessian_isSymm k)
      (R.annihilated_hessian_mul_displacement k) _ (b k)
  rw [hE, euclid_norm_sq]
  change (metricGram (R.hessian (k + 1)) (V (k + 1))).trace =
    (metricGram (M k) (V k * T k + Rres k)).trace + _
  rw [← hremove, hM, R.hessian_update, EnergyIdentities.gram_add, EnergyIdentities.gram_smul,
    EnergyIdentities.gram_outer, Matrix.trace_add, Matrix.trace_smul, FrameBounds.trace_outer,
    smul_eq_mul, div_eq_inv_mul]

/-- Item `C/02_M/disp/036` (`companion/chapters/02_M.tex:249-252`), in the proof of Theorem
`M:residualtheorem`. Under the standing assumptions of the proof, with
$E_k=\tr(V_k^TB_kV_k)$ and $M_k$ from \eqref{M:annihilation}, for every $k\ge J$
\[ E_{k+1}=\tr\bigl[(V_kT_k+R_k)^TM_k(V_kT_k+R_k)\bigr]+\frac{\|V_{k+1}^Ty_k\|^2}{t_k}. \] -/
theorem frame_energy {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (_hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ) (_hm : 0 < m)
    (hfr : ∀ k, J ≤ k →
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k)
    (PS : Mat n) (_hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (k : ℕ) (hk : J ≤ k) :
    E (k + 1) = ((V k * T k + Rres k)ᵀ * M k * (V k * T k + Rres k)).trace +
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k :=
  frame_energy_step R V T b Rres E hE M hM k (hfr k hk).2.2.1

/-- The general form of display `C/02_M/disp/037` at one step $k$: if
$V_{k+1}=V_kT_k+s_kb_k^T+R_k$ and $\|V_{k+1}^Ty_k\|^2\le C_0t_k$, then (Young with parameter
$d_k$, then the operator bound for right multiplication by $T_k$)
\[ E_{k+1}\le(1+d_k)\|T_k\|^2\Bigl(E_k-\frac{\|V_k^Tg_k\|^2}{q_k}\Bigr)
   +(1+d_k^{-1})\tr(R_k^TM_kR_k)+C_0, \]
and the parenthesized energy is nonnegative. -/
theorem frame_young_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {p : ℕ}
    (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ)
    (hVk : V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k)
    (C0 : ℝ)
    (hC0 : ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k) :
    E (k + 1) ≤ (1 + R.d k) * FrameNorms.euclideanOpNorm (T k) ^ 2 *
        (E k - ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 / R.q k) +
      (1 + (R.d k)⁻¹) * ((Rres k)ᵀ * M k * Rres k).trace + C0 ∧
      0 ≤ E k - ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 / R.q k := by
  have hMpsd : (M k).PosSemidef := by
    rw [hM k]
    exact R.annihilated_hessian_posSemidef k
  have hd := R.d_pos k
  have h036 := frame_energy_step R V T b Rres E hE M hM k hVk
  have hyoung := FrameBounds.gram_trace_add_le hMpsd (V k * T k) (Rres k) (R.d k) hd
  have hop : FrameBounds.OperatorSqBound (T k) (FrameNorms.euclideanOpNorm (T k) ^ 2) :=
    (FrameNorms.operatorSqBound_iff_opNorm_sq _ _ (sq_nonneg _)).mpr le_rfl
  have htrans := FrameBounds.gram_trace_transport_le hMpsd (V k) (T k) _ hop
  have hbase : (metricGram (M k) (V k)).trace =
      E k - ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 / R.q k := by
    rw [hM k, EnergyIdentities.gram_sub, EnergyIdentities.gram_smul, EnergyIdentities.gram_outer,
      Matrix.trace_sub, Matrix.trace_smul, FrameBounds.trace_outer, hE k, euclid_norm_sq,
      smul_eq_mul, div_eq_inv_mul]
    rfl
  have hnn : 0 ≤ (metricGram (M k) (V k)).trace := FrameBounds.gram_trace_nonneg hMpsd (V k)
  have hcorr : ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 / R.curvature k ≤ C0 :=
    (div_le_iff₀ (R.curvature_pos k)).mpr hC0
  have h1 := mul_le_mul_of_nonneg_left htrans (by linarith : (0 : ℝ) ≤ 1 + R.d k)
  rw [hbase] at h1
  refine ⟨?_, hbase ▸ hnn⟩
  rw [h036]
  change (metricGram (M k) (V k * T k + Rres k)).trace + _ ≤
    _ + (1 + (R.d k)⁻¹) * (metricGram (M k) (Rres k)).trace + C0
  linarith

/-- Item `C/02_M/disp/037` (`companion/chapters/02_M.tex:254-257`), in the proof of Theorem
`M:residualtheorem`. Under the standing assumptions of display `C/02_M/disp/036`, for every
$k\ge J$ (Young's inequality with parameter $d_k$, then the Euclidean operator bound on right
multiplication by $T_k$),
\[ E_{k+1}\le(1+d_k)\|T_k\|^2\Bigl(E_k-\frac{\|V_k^Tg_k\|^2}{q_k}\Bigr)
   +(1+d_k^{-1})\tr(R_k^TM_kR_k)+C_0. \]
($\|T_k\|$ is the Euclidean operator norm `FrameNorms.euclideanOpNorm`.) -/
theorem frame_young {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (_hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ) (_hm : 0 < m)
    (hfr : ∀ k, J ≤ k →
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k)
    (PS : Mat n) (_hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (k : ℕ) (hk : J ≤ k) :
    E (k + 1) ≤ (1 + R.d k) * FrameNorms.euclideanOpNorm (T k) ^ 2 *
        (E k - ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 / R.q k) +
      (1 + (R.d k)⁻¹) * ((Rres k)ᵀ * M k * Rres k).trace + C0 :=
  (frame_young_step R V T b Rres E hE M hM k (hfr k hk).2.2.1 C0 (hfr k hk).2.1).1

/-- The general form of display `C/02_M/disp/038` at one step $k$: if $\|P_Sy_j\|^2\le L_St_j$
for all $j$, $\operatorname{range}R_k\subset S$ and $\|R_k\|_F^2\le C_Rd_k$, then with
$C_S=\tr(P_SB_0)$
\[ \tr(R_k^TM_kR_k)\le\|R_k\|_F^2\tr(P_SB_k)\le C_Rd_k(C_S+L_Sk). \] -/
theorem residual_energy_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {p : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (PS : Mat n) (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (CS : ℝ) (hCS : CS = (PS * R.hessian 0).trace) (CR : ℝ) (k : ℕ)
    (hrange : ∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S)
    (hsize : SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k) :
    ((Rres k)ᵀ * M k * Rres k).trace ≤ SmoothSubspace.frobSq (Rres k) * (PS * R.hessian k).trace ∧
      SmoothSubspace.frobSq (Rres k) * (PS * R.hessian k).trace ≤ CR * R.d k * (CS + LS * k) := by
  obtain ⟨r, U, hU, hS, hproj⟩ := projection_basis S
  have hPSU := projection_matrix_eq S U hU hS PS hPS
  have hW := range_projection S U hU hS (Rres k) hrange
  have htr : ∀ j, (PS * R.hessian j).trace = (metricGram (R.hessian j) U).trace := fun j => by
    rw [hPSU, SmoothSubspace.gram_trace_eq_projection_trace]
  refine ⟨?_, ?_⟩
  · rw [hM k, htr k]
    exact SmoothSubspace.residual_energy_le (R.hessian_posDef k).posSemidef (R.g k) (R.q k)
      (R.q_pos k).le U hU (Rres k) hW
  · have hsm : ∀ j, sqNorm ((U * Uᵀ) *ᵥ R.gradientChange j) ≤ LS * R.curvature j := fun j => by
      rw [SmoothSubspace.sqNorm_projection U hU, ← hproj]
      exact hsmooth j
    have hbound := R.smooth_subspace_projection_trace_bound U hU LS hsm k
    rw [← hPSU] at hbound
    have hnn : 0 ≤ (PS * R.hessian k).trace := by
      rw [htr k]
      exact FrameBounds.gram_trace_nonneg (R.hessian_posDef k).posSemidef U
    have hF0 := SmoothSubspace.frobSq_nonneg (Rres k)
    have hCRd : 0 ≤ CR * R.d k := hF0.trans hsize
    calc SmoothSubspace.frobSq (Rres k) * (PS * R.hessian k).trace
        ≤ CR * R.d k * (PS * R.hessian k).trace := mul_le_mul_of_nonneg_right hsize hnn
      _ ≤ CR * R.d k * (CS + LS * k) := by
          rw [hCS]
          exact mul_le_mul_of_nonneg_left hbound hCRd

/-- Item `C/02_M/disp/038` (`companion/chapters/02_M.tex:259-263`), in the proof of Theorem
`M:residualtheorem`. Under the standing assumptions of display `C/02_M/disp/036`, with the
derived bound $\tr(P_SB_k)\le C_S+L_Sk$ where $C_S=\tr(P_SB_0)$, for every $k\ge J$
\[ \tr(R_k^TM_kR_k)\le\|R_k\|_F^2\tr(P_SB_k)\le C_Rd_k(C_S+L_Sk). \] -/
theorem residual_energy {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ) (_hm : 0 < m)
    (hfr : ∀ k, J ≤ k →
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k)
    (PS : Mat n) (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (E : ℕ → ℝ) (_hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (CS : ℝ) (hCS : CS = (PS * R.hessian 0).trace) (k : ℕ) (hk : J ≤ k) :
    ((Rres k)ᵀ * M k * Rres k).trace ≤ SmoothSubspace.frobSq (Rres k) * (PS * R.hessian k).trace ∧
      SmoothSubspace.frobSq (Rres k) * (PS * R.hessian k).trace ≤ CR * R.d k * (CS + LS * k) :=
  residual_energy_step R S LS hsmooth PS hPS Rres M hM CS hCS CR k (hfr k hk).2.2.2.2.1
    (hfr k hk).2.2.2.2.2

/-- The general form of display `C/02_M/disp/039` at one step $k$ with $d_k\le1$, with explicit
constants $C_1=1+2\max(C_T,0)$ and $C_2=2C_R(C_S+L_S)+C_0$ (for $L_S,C_0,C_R\ge0$):
\[ E_{k+1}\le(1+C_1d_k)(E_k-m/q_k)+C_2(k+1). \] -/
theorem residual_recurrence_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {p : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ) (hLS : 0 ≤ LS)
    (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (PS : Mat n) (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (CS : ℝ) (hCS : CS = (PS * R.hessian 0).trace)
    (m C0 CT CR : ℝ) (hC0 : 0 ≤ C0) (hCR : 0 ≤ CR) (k : ℕ) (hd1 : R.d k ≤ 1)
    (hvis : ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m)
    (hcor : ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k)
    (hVk : V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k)
    (hT : FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k)
    (hrange : ∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S)
    (hsize : SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k) :
    E (k + 1) ≤ (1 + (1 + 2 * max CT 0) * R.d k) * (E k - m / R.q k) +
      (2 * CR * (CS + LS) + C0) * ((k : ℝ) + 1) := by
  have hd := R.d_pos k
  have hq := R.q_pos k
  obtain ⟨h37, hX⟩ := frame_young_step R V T b Rres E hE M hM k hVk C0 hcor
  obtain ⟨h38a, h38b⟩ := residual_energy_step R S LS hsmooth PS hPS Rres M hM CS hCS CR k
    hrange hsize
  have hCS0 : 0 ≤ CS := by
    obtain ⟨r, U, hU, hS, _⟩ := projection_basis S
    rw [hCS, projection_matrix_eq S U hU hS PS hPS, ← SmoothSubspace.gram_trace_eq_projection_trace]
    exact FrameBounds.gram_trace_nonneg (R.hessian_posDef 0).posSemidef U
  set X := E k - ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 / R.q k with hXdef
  set Y := ((Rres k)ᵀ * M k * Rres k).trace with hYdef
  set τ := FrameNorms.euclideanOpNorm (T k) ^ 2 with hτ
  have hc0 : 0 ≤ max CT 0 := le_max_right _ _
  have hCTc : CT ≤ max CT 0 := le_max_left _ _
  have hτb : τ ≤ 1 + max CT 0 * R.d k :=
    hT.trans (by nlinarith [mul_le_mul_of_nonneg_right hCTc hd.le])
  have hfac : (1 + R.d k) * τ ≤ 1 + (1 + 2 * max CT 0) * R.d k := by
    have h1 : (1 + R.d k) * τ ≤ (1 + R.d k) * (1 + max CT 0 * R.d k) :=
      mul_le_mul_of_nonneg_left hτb (by linarith)
    nlinarith [mul_nonneg hc0 (mul_nonneg hd.le (by linarith : (0 : ℝ) ≤ 1 - R.d k))]
  have hXm : X ≤ E k - m / R.q k := by
    have : m / R.q k ≤ ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 / R.q k :=
      div_le_div_of_nonneg_right hvis hq.le
    rw [hXdef]
    linarith
  have hA : (1 + R.d k) * τ * X ≤ (1 + (1 + 2 * max CT 0) * R.d k) * (E k - m / R.q k) := by
    calc (1 + R.d k) * τ * X ≤ (1 + (1 + 2 * max CT 0) * R.d k) * X :=
          mul_le_mul_of_nonneg_right hfac hX
      _ ≤ _ := mul_le_mul_of_nonneg_left hXm (by positivity)
  have hY : Y ≤ CR * R.d k * (CS + LS * k) := h38a.trans h38b
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hB : (1 + (R.d k)⁻¹) * Y ≤ 2 * CR * (CS + LS) * ((k : ℝ) + 1) := by
    have h1 : (1 + (R.d k)⁻¹) * Y ≤ (1 + (R.d k)⁻¹) * (CR * R.d k * (CS + LS * k)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    have h2 : (1 + (R.d k)⁻¹) * (CR * R.d k * (CS + LS * k)) =
        CR * (R.d k + 1) * (CS + LS * k) := by
      field_simp
      ring
    have hlin : 0 ≤ CS + LS * k := by positivity
    have h3a : CR * (R.d k + 1) ≤ 2 * CR := by
      have := mul_le_mul_of_nonneg_left (by linarith : R.d k + 1 ≤ 2) hCR
      linarith
    have h3 : CR * (R.d k + 1) * (CS + LS * k) ≤ 2 * CR * (CS + LS * k) :=
      mul_le_mul_of_nonneg_right h3a hlin
    have h4a : CS + LS * (k : ℝ) ≤ (CS + LS) * ((k : ℝ) + 1) := by
      have := mul_nonneg hCS0 hk0
      linarith
    have h4 : 2 * CR * (CS + LS * k) ≤ 2 * CR * ((CS + LS) * ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h4a (by positivity)
    calc (1 + (R.d k)⁻¹) * Y ≤ (1 + (R.d k)⁻¹) * (CR * R.d k * (CS + LS * k)) := h1
      _ = CR * (R.d k + 1) * (CS + LS * k) := h2
      _ ≤ 2 * CR * (CS + LS * k) := h3
      _ ≤ 2 * CR * ((CS + LS) * ((k : ℝ) + 1)) := h4
      _ = 2 * CR * (CS + LS) * ((k : ℝ) + 1) := by ring
  have hC0k : C0 ≤ C0 * ((k : ℝ) + 1) := le_mul_of_one_le_right hC0 (by linarith)
  calc E (k + 1) ≤ (1 + R.d k) * τ * X + (1 + (R.d k)⁻¹) * Y + C0 := h37
    _ ≤ (1 + (1 + 2 * max CT 0) * R.d k) * (E k - m / R.q k) +
          2 * CR * (CS + LS) * ((k : ℝ) + 1) + C0 * ((k : ℝ) + 1) :=
        add_le_add (add_le_add hA hB) hC0k
    _ = _ := by ring

/-- Item `C/02_M/disp/039` (`companion/chapters/02_M.tex:265-267`), in the proof of Theorem
`M:residualtheorem`. Under the standing assumptions of display `C/02_M/disp/038`, on a tail with
$d_k\le1$ (the text keeps the name $J$ for it) there are constants $C_1,C_2\ge0$ with, for
every $k\ge J$,
\[ E_{k+1}\le(1+C_1d_k)(E_k-m/q_k)+C_2(k+1). \]
(One choice: $C_1=1+2\max(C_T,0)$, $C_2=2C_R(C_S+L_S)+C_0$, see `residual_recurrence_step`.) -/
theorem residual_recurrence {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ) (_hm : 0 < m)
    (hfr : ∀ k, J ≤ k →
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k)
    (PS : Mat n) (hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (CS : ℝ) (hCS : CS = (PS * R.hessian 0).trace) (hJ1 : ∀ k, J ≤ k → R.d k ≤ 1) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ k, J ≤ k →
      E (k + 1) ≤ (1 + C1 * R.d k) * (E k - m / R.q k) + C2 * ((k : ℝ) + 1) := by
  have hLS : 0 ≤ LS := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hsmooth 0))
    (R.curvature_pos 0)
  have hC0 : 0 ≤ C0 := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hfr J le_rfl).2.1)
    (R.curvature_pos J)
  have hCR : 0 ≤ CR := nonneg_of_mul_nonneg_left
    ((SmoothSubspace.frobSq_nonneg _).trans (hfr J le_rfl).2.2.2.2.2) (R.d_pos J)
  have hCS0 : 0 ≤ CS := by
    obtain ⟨r, U, hU, hS, _⟩ := projection_basis S
    rw [hCS, projection_matrix_eq S U hU hS PS hPS, ← SmoothSubspace.gram_trace_eq_projection_trace]
    exact FrameBounds.gram_trace_nonneg (R.hessian_posDef 0).posSemidef U
  refine ⟨1 + 2 * max CT 0, 2 * CR * (CS + LS) + C0, by positivity, by positivity,
    fun k hk => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfr k hk
  exact residual_recurrence_step R S LS hLS hsmooth PS hPS V T b Rres E hE M hM CS hCS m C0 CT CR
    hC0 hCR k (hJ1 k hk) h1 h2 h3 h4 h5 h6

/-- Normalized summation with additive errors $c_i\ge0$ (the scalar step behind display
`C/02_M/disp/040`): if $e_i\ge0$ for $i\le M$, $q_i>0$, $u_i\ge0$, the products
$P_i=\prod_{l<i}(1+u_l)$ satisfy $P_i\le B$ for $i\le M$, $m>0$, and
$e_{i+1}\le(1+u_i)(e_i-m/q_i)+c_i$ for $i<M$, then
$\frac mB\sum_{i<M}q_i^{-1}\le e_0+\sum_{i<M}c_i$. -/
theorem normalized_budget {e q u c : ℕ → ℝ} {m B : ℝ} (M : ℕ)
    (he : ∀ i, i ≤ M → 0 ≤ e i) (hq : ∀ i, 0 < q i) (hu : ∀ i, 0 ≤ u i)
    (hB : ∀ i, i ≤ M → ResidualBudget.driftProduct u i ≤ B) (hm : 0 < m) (hc : ∀ i, 0 ≤ c i)
    (hrec : ∀ i, i < M → e (i + 1) ≤ (1 + u i) * (e i - m / q i) + c i) :
    m / B * ∑ i ∈ Finset.range M, (q i)⁻¹ ≤ e 0 + ∑ i ∈ Finset.range M, c i := by
  set P := ResidualBudget.driftProduct u with hPdef
  have hP1 : ∀ i, 1 ≤ P i := ResidualBudget.one_le_driftProduct hu
  have hPpos : ∀ i, 0 < P i := fun i => lt_of_lt_of_le one_pos (hP1 i)
  have hnorm : ∀ i, i < M → e (i + 1) / P (i + 1) ≤ e i / P i - m / B * (q i)⁻¹ + c i := by
    intro i hi
    have hfactor : 0 < 1 + u i := by linarith [hu i]
    have hchange : ((1 + u i) * (e i - m / q i) + c i) / P (i + 1) =
        e i / P i - (m / q i) / P i + c i / P (i + 1) := by
      rw [show P (i + 1) = P i * (1 + u i) from ResidualBudget.driftProduct_succ u i]
      field_simp [(hPpos i).ne', hfactor.ne', (hq i).ne']
      ring
    have hdes : m / B * (q i)⁻¹ ≤ (m / q i) / P i := by
      rw [show m / B * (q i)⁻¹ = (m / q i) / B by ring]
      exact div_le_div_of_nonneg_left (div_nonneg hm.le (hq i).le) (hPpos i) (hB i hi.le)
    have hadd : c i / P (i + 1) ≤ c i := div_le_self (hc i) (hP1 (i + 1))
    have hdiv := div_le_div_of_nonneg_right (hrec i hi) (hPpos (i + 1)).le
    rw [hchange] at hdiv
    linarith
  have htel : ∀ i, i ≤ M →
      m / B * ∑ l ∈ Finset.range i, (q l)⁻¹ ≤ e 0 - e i / P i + ∑ l ∈ Finset.range i, c l := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [hPdef]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hnorm i (by omega)
      rw [Finset.sum_range_succ, mul_add, Finset.sum_range_succ]
      linarith
  have hfin := htel M le_rfl
  have hlast : 0 ≤ e M / P M := div_nonneg (he M le_rfl) (hPpos M).le
  linarith

/-- Item `C/02_M/disp/040` (`companion/chapters/02_M.tex:269-272`), in the proof of Theorem
`M:residualtheorem`. Under the standing assumptions of display `C/02_M/disp/039` and its
conclusion ($C_1,C_2\ge0$ with the recurrence on the tail), normalize by
$P_{k+1}=P_k(1+C_1d_k)$, $P_J=1$, with $P_k\le\overline P$ for $k\ge J$ (finite $\sum d_k$
gives such $\overline P$, e.g. $\exp(C_1\sum_{j\ge J}d_j)$). Summing and using final-energy
positivity gives, for every $N\ge J$,
\[ \frac m{\overline P}\sum_{k=J}^{N-1}q_k^{-1}\le E_J+C_2\sum_{k=J}^{N-1}(k+1)=O(N^2). \] -/
theorem residual_budget {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hsum : Summable R.d)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (LS : ℝ)
    (_hsmooth : ∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ LS * R.curvature k)
    (J p : ℕ) (V : ℕ → Matrix (Fin n) (Fin p) ℝ) (T : ℕ → Mat p) (b : ℕ → Vec p)
    (Rres : ℕ → Matrix (Fin n) (Fin p) ℝ) (m C0 CT CR : ℝ) (hm : 0 < m)
    (_hfr : ∀ k, J ≤ k →
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec p, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k)
    (PS : Mat n) (_hPS : ∀ v : Vec n, euclideanVector (PS *ᵥ v) =
      (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin n)))
    (E : ℕ → ℝ) (hE : ∀ k, E k = ((V k)ᵀ * R.hessian k * V k).trace)
    (M : ℕ → Mat n) (_hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))
    (CS : ℝ) (_hCS : CS = (PS * R.hessian 0).trace) (_hJ1 : ∀ k, J ≤ k → R.d k ≤ 1)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hrec : ∀ k, J ≤ k →
      E (k + 1) ≤ (1 + C1 * R.d k) * (E k - m / R.q k) + C2 * ((k : ℝ) + 1))
    (P : ℕ → ℝ) (hPJ : P J = 1) (hP : ∀ k, J ≤ k → P (k + 1) = P k * (1 + C1 * R.d k))
    (Pbar : ℝ) (hPbar : ∀ k, J ≤ k → P k ≤ Pbar) :
    (∀ N : ℕ, J ≤ N → m / Pbar * ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹ ≤
        E J + C2 * ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1)) ∧
      (fun N : ℕ => E J + C2 * ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ 2) := by
  have hEnn : ∀ k, 0 ≤ E k := fun k => by
    rw [hE]
    exact FrameBounds.gram_trace_nonneg (R.hessian_posDef k).posSemidef (V k)
  have hu : ∀ i, 0 ≤ C1 * R.d (J + i) := fun i => mul_nonneg hC1 (R.d_pos _).le
  have hPd : ∀ i, P (J + i) = ResidualBudget.driftProduct (fun i => C1 * R.d (J + i)) i := by
    intro i
    induction i with
    | zero => simpa using hPJ
    | succ i ih =>
      rw [← add_assoc, hP (J + i) (Nat.le_add_right J i), ih, ResidualBudget.driftProduct_succ]
  refine ⟨fun N hJN => ?_, ?_⟩
  · have h := normalized_budget (e := fun i => E (J + i)) (q := fun i => R.q (J + i))
      (u := fun i => C1 * R.d (J + i)) (c := fun i => C2 * (((J + i : ℕ) : ℝ) + 1)) (m := m)
      (B := Pbar) (N - J) (fun i _ => hEnn _) (fun i => R.q_pos _) hu
      (fun i _ => (hPd i) ▸ hPbar (J + i) (Nat.le_add_right J i)) hm
      (fun i => mul_nonneg hC2 (by positivity))
      (fun i _ => hrec (J + i) (Nat.le_add_right J i))
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    rw [← Finset.mul_sum] at h
    simpa only [add_zero] using h
  · apply Asymptotics.IsBigO.of_bound (E J + C2)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsum0 : 0 ≤ ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1) :=
      Finset.sum_nonneg fun k _ => by positivity
    have hsumN : ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1) ≤ (N : ℝ) ^ 2 := by
      calc ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1) ≤ ∑ _k ∈ Finset.Ico J N, (N : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkN : k + 1 ≤ N := (Finset.mem_Ico.mp hk).2
            exact_mod_cast hkN
        _ = ((N - J : ℕ) : ℝ) * N := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N J)
            (Nat.cast_nonneg N)
        _ = (N : ℝ) ^ 2 := by ring
    have hlhs : 0 ≤ E J + C2 * ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1) :=
      add_nonneg (hEnn J) (mul_nonneg hC2 hsum0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlhs, abs_of_nonneg (by positivity)]
    have h1 : E J ≤ E J * (N : ℝ) ^ 2 := le_mul_of_one_le_right (hEnn J) (by nlinarith)
    have h2 : C2 * ∑ k ∈ Finset.Ico J N, ((k : ℝ) + 1) ≤ C2 * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsumN hC2
    nlinarith

/-- Item `C/02_M/prose/027` (`companion/chapters/02_M.tex:275`): "Euclidean smallness alone
does not control a residual in a direction where $B_k$ may grow without this estimate." In
positive dimension, no bound of the residual energy $\tr(R^TBR)$ by its Euclidean size
$\|R\|_F^2$ holds uniformly over SPD metrics $B$: for every constant $c$ there are an SPD $B$
and a one-column residual $R$ with $\tr(R^TBR)>c\|R\|_F^2$ (take $B$ large in the direction of
$R$). This is why the proof bounds $\tr(R_k^TM_kR_k)$ through the derived estimate
$\tr(P_SB_k)\le C_S+L_Sk$ on $S$. -/
theorem euclidean_smallness_insufficient {n : ℕ} (hn : 1 ≤ n) :
    ¬ ∃ c : ℝ, ∀ B : Mat n, B.PosDef → ∀ W : Matrix (Fin n) (Fin 1) ℝ,
      (Wᵀ * B * W).trace ≤ c * SmoothSubspace.frobSq W := by
  rintro ⟨c, hc⟩
  set i0 : Fin n := ⟨0, hn⟩
  set W : Matrix (Fin n) (Fin 1) ℝ := fun i _ => if i = i0 then 1 else 0 with hW
  have hB : (Matrix.diagonal fun _ : Fin n => |c| + 1).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun _ => by positivity
  have h := hc _ hB W
  have hfrob : SmoothSubspace.frobSq W = 1 := by
    simp [SmoothSubspace.frobSq, hW]
  have htr : (Wᵀ * (Matrix.diagonal fun _ : Fin n => |c| + 1) * W).trace = |c| + 1 := by
    simp [Matrix.trace, Matrix.mul_apply, hW, Matrix.diagonal_apply]
  rw [hfrob, htr, mul_one] at h
  linarith [le_abs_self c]

/-- Item `C/02_M/prose/043` (`companion/chapters/02_M.tex:286`): "Its additive errors need
not be summable, so the earlier lemmas alone do not prove this residual theorem." The additive
errors $C_2(k+1)$ of display `C/02_M/disp/039` are not summable unless $C_2=0$: for $C_2>0$,
$\sum_kC_2(k+1)=\infty$. (The comparison with the cited lemmas is bibliographic.) -/
theorem additive_errors_not_summable (C2 : ℝ) (hC2 : 0 < C2) :
    ¬ Summable (fun k : ℕ => C2 * ((k : ℝ) + 1)) := by
  intro hs
  have h := hs.tendsto_atTop_zero
  have hge : ∀ k : ℕ, C2 ≤ C2 * ((k : ℝ) + 1) := fun k =>
    le_mul_of_one_le_right hC2.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have := ge_of_tendsto' h hge
  linarith

/-! ### Relation to earlier work -/

/-- Item `C/02_M/prose/030` (`companion/chapters/02_M.tex:282`): "The BFGS update, secant
equation, positive-definiteness preservation and determinant identity are classical." The
mathematical facts named (proved here; their attribution is bibliographic): for the inverse
update $H_+=(I-sy^T/t)H(I-ys^T/t)+ss^T/t$, $t=y^Ts$:
the secant equation $H_+y=s$ when $t\ne0$; positive-definiteness preservation, $H\succ0$ and
$t>0$ give $H_+\succ0$; and the determinant identity $\det H_+=(\alpha/\beta)\det H$ under the
assumptions of Theorem `M:hierarchy` ($s=-\alpha Hg$, $\alpha>0$, $q=g^THg>0$,
$\beta=-y^THg/q>0$). -/
theorem classical_facts {n : ℕ} :
    (∀ (H : Mat n) (s y : Vec n), dot y s ≠ 0 → inverseBFGS H s y *ᵥ y = s) ∧
      (∀ (H : Mat n) (s y : Vec n), H.PosDef → 0 < dot y s → (inverseBFGS H s y).PosDef) ∧
      ∀ (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ), H.PosDef → s = -α • (H *ᵥ g) →
        0 < α → q = dot g (H *ᵥ g) → 0 < q → β = -dot y (H *ᵥ g) / q → 0 < β →
        Hplus = inverseBFGS H s y → Hplus.det = α / β * H.det := by
  refine ⟨fun H s y ht => ?_, fun H s y hH ht => inverseBFGS_posDef hH s y ht,
    fun H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus =>
      BfgsCoverage.Article.MatrixAlgebra.det_update H Hplus g y s α q β hH hs hα hq_def hq hβ_def
        hβ hHplus⟩
  have hsy : dot s y = dot y s := by simp [dot, mul_comm]
  have hz : ((1 : Mat n) - (dot y s)⁻¹ • outer y s) *ᵥ y = 0 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, hsy, smul_smul, ht]
  simp only [inverseBFGS, Matrix.add_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, hsy,
    smul_smul, inv_mul_cancel₀ ht, one_smul]
  suffices ((1 - (dot y s)⁻¹ • outer s y) * H * (1 - (dot y s)⁻¹ • outer y s)) *ᵥ y = 0 by
    simp [this]
  rw [← Matrix.mulVec_mulVec, hz]
  simp

/-! ### Helpers for the non-vacuity examples -/

/-- Euclidean strong convexity (`FixedNormal.EuclideanStrongConvexOn`, constant $\mu>0$) gives
strict contours at every level: the boundary of $\{F\le\ell\}$ contains no nontrivial segment. -/
theorem strong_convex_strict_contours {n : ℕ} {F : Vec n → ℝ} (hcont : Continuous F)
    (μ : ℝ) (hμ : 0 < μ) (hs : FixedNormal.EuclideanStrongConvexOn Set.univ μ F) (ℓ : ℝ) :
    ∀ x z : Vec n, segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z := by
  intro x z hseg
  have hfr : ∀ w ∈ frontier {w | F w ≤ ℓ}, F w = ℓ := by
    intro w hw
    rw [(isClosed_le hcont continuous_const).frontier_eq] at hw
    obtain ⟨hle, hnint⟩ := hw
    by_contra hne
    exact hnint (interior_maximal (fun y (hy : F y < ℓ) => le_of_lt hy)
      (isOpen_lt hcont continuous_const) (lt_of_le_of_ne hle hne))
  have hx := hfr x (hseg (left_mem_segment ℝ x z))
  have hz := hfr z (hseg (right_mem_segment ℝ x z))
  have hm := hfr ((1 - 1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z)
    (hseg ⟨1 - 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩)
  have hc := hs.2 (Set.mem_univ x) (Set.mem_univ z) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [FixedNormal.sqNorm_convex_combination] at hc
  have hsq : sqNorm (z - x) ≤ 0 := by nlinarith
  have hzero : sqNorm (z - x) = 0 := le_antisymm hsq (sqNorm_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((z - x) i))).mp hzero
  funext i
  have := hall i (Finset.mem_univ i)
  have h0 : (z - x) i = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
  simp only [Pi.sub_apply, sub_eq_zero] at h0
  exact h0.symm

/-! ### Non-vacuity -/

namespace Examples

open BfgsCoverage.Article.Energy.Example

/-- On the quadratic run of the article ($F(x)=x^2/2$, $x_k=2^{-k}$, $H_k=1$,
$\alpha_k=1/2$), $q_k=4^{-k}$. -/
theorem run_q (k : ℕ) : run.q k = ((1 / 2 : ℝ) ^ k) ^ 2 := by
  simp [AdmissibleBFGSRun.q, run, metricEnergy, dot, pt]
  ring

theorem run_q_inv (k : ℕ) : (run.q k)⁻¹ = 4 ^ k := by
  rw [run_q, ← pow_mul, mul_comm, pow_mul, ← inv_pow]
  norm_num

/-- On the quadratic run with $x_*=0$, the secant corrections are $R_k=4^{-(k+1)}\le1$. -/
theorem run_correction (k : ℕ) :
    dot (run.gradientChange k) (run.x (k + 1) - 0) ^ 2 / run.curvature k ≤ 1 := by
  have hdisp : run.displacement k = pt (k + 1) - pt k := step_eq k
  have hy : run.gradientChange k = pt (k + 1) - pt k := rfl
  have hx : run.x (k + 1) - 0 = pt (k + 1) := sub_zero _
  unfold AdmissibleBFGSRun.curvature
  rw [hdisp, hy, hx]
  have hsucc : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k * (1 / 2) := pow_succ _ _
  simp only [dot, Fin.sum_univ_one, pt, Pi.sub_apply, hsucc]
  have ha0 : (0 : ℝ) < (1 / 2) ^ k := by positivity
  have ha1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set a := (1 / 2 : ℝ) ^ k with ha
  have hnum : ((a * (1 / 2) - a) * (a * (1 / 2))) ^ 2 = a ^ 2 / 4 * (a ^ 2 / 4) := by ring
  have hden : (a * (1 / 2) - a) * (a * (1 / 2) - a) = a ^ 2 / 4 := by ring
  rw [hnum, hden, div_le_one (by positivity)]
  have hsq : a ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg a]

/-- The assumptions of the run theorems of Sections `M:notation` and `M:reciprocal` (Theorems
`M:average`, `M:superquadratic`, displays `C/02_M/disp/017`-`C/02_M/disp/024`, and the finite
limiting value of `summable_of_finite_limit`) can all hold: the quadratic run has values tending
to $0$, bounded gradients ($G=1$), $\sum_kd_k<\infty$, hence $d_k\to0$, and the choices $K_0$,
$\eta$, $J$, $V_\eta$, $D_J$, $m$ of the proofs are definitions. -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (G K0 η DJ : ℝ) (J m : ℕ)
    (V : ℝ → Mat 1 → ℝ),
    (∃ ℓ : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) ∧
    (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ Tendsto R.d atTop (𝓝 0) ∧
      Summable R.d ∧ 0 < G ∧ (∀ k, ‖euclideanVector (R.g k)‖ ≤ G) ∧
      K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2 ∧ 0 < η ∧ (∀ k, J ≤ k → R.d k / (1 - R.c₂) ≤ η) ∧
      DJ = ∑' i, R.d (J + i) ∧ 2 ≤ m ∧
      (∀ η : ℝ, 0 < η → ∀ H : Mat 1, H.PosDef →
        V η H = ∑ j ∈ Finset.Icc 1 1, (K0 / η) ^ (j - 1) * principalSum H j) := by
  have hval : Tendsto (fun k => quad (run.x k)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).pow 2).div_const 2
    simpa [quad, run, pt] using h
  refine ⟨quad, run, 1, _, 1, _, 1, 2, fun η H => ∑ j ∈ Finset.Icc 1 1,
    (4 * 1 ^ 2 / (1 - run.c₂) ^ 2 / η) ^ (j - 1) * principalSum H j, ⟨0, hval⟩,
    ⟨1, run_bounded⟩, run_summable.tendsto_atTop_zero, run_summable, one_pos, run_bounded, rfl,
    one_pos, fun k hk => ?_, rfl, le_rfl, fun η _ H _ => rfl⟩
  rw [run_d]
  change 1 / 2 * ((1 / 2 : ℝ) ^ k) ^ 2 / (1 - 3 / 4) ≤ 1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : (1 / 2 : ℝ) ^ k' ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ k' := by positivity
  have hk1 : (1 / 2 : ℝ) ^ (k' + 1) = (1 / 2) ^ k' * (1 / 2) := pow_succ _ _
  rw [hk1, show 1 / 2 * ((1 / 2 : ℝ) ^ k' * (1 / 2)) ^ 2 / (1 - 3 / 4) =
    ((1 / 2 : ℝ) ^ k') ^ 2 / 2 by ring]
  nlinarith

/-- The assumptions of `average_full_bfgs` and `superquadratic_full_bfgs` (a full-BFGS sequence
with fixed weak Wolfe, bounded gradients and summable $d_k$) can hold: the data of the
quadratic run. -/
example : ∃ (H : ℕ → Mat 1) (g : ℕ → Vec 1) (α : ℕ → ℝ) (c₂ G : ℝ),
    (H 0).PosDef ∧ (∀ k, g k ≠ 0) ∧ (∀ k, 0 < α k) ∧ 0 < c₂ ∧ c₂ < 1 ∧
      (∀ k, c₂ * dot (g k) (-α k • (H k *ᵥ g k)) ≤ dot (g (k + 1)) (-α k • (H k *ᵥ g k))) ∧
      (∀ k, H (k + 1) = inverseBFGS (H k) (-α k • (H k *ᵥ g k)) (g (k + 1) - g k)) ∧
      0 < G ∧ (∀ k, ‖euclideanVector (g k)‖ ≤ G) ∧
      Summable (fun k => α k * dot (g k) (H k *ᵥ g k)) :=
  ⟨run.H, run.g, run.α, run.c₂, 1, run.initial_posDef, run.gradient_nonzero, run.alpha_pos,
    by norm_num [run], run.c₂_lt_one, run.weak_wolfe, run.update, one_pos, run_bounded,
    run_summable⟩

/-- The assumptions of Lemma `M:localization` can hold, and so can the condition of its
run-invariance conjunct: $n=1$, $F(x)=x^2/2$, $x_*=0$, $U=\R$, $r=2$, with $\omega_2$ its defining
infimum ($\omega_2=2$, attained on the sphere $|z|=2$); the quadratic run starts at $x_0=1$ with
$F(x_0)-F(x_*)=1/2<\omega_2$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (U : Set (Vec 1)) (r ω : ℝ),
    1 ≤ 1 ∧ ConvexOn ℝ Set.univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      U ∈ 𝓝 xstar ∧ 0 < r ∧ {x | ‖euclideanVector (x - xstar)‖ ≤ r} ⊆ U ∧
      ω = sInf ((fun z => F (xstar + z) - F xstar) '' {z | ‖euclideanVector z‖ = r}) ∧
      ∃ R : AdmissibleBFGSRun 1 F, F (R.x 0) - F xstar < ω := by
  have hq0 : quad 0 = 0 := by simp [quad]
  have hmin : ∀ x, quad 0 ≤ quad x := fun x => by rw [hq0]; exact quad_nonneg x
  have huniq : ∀ x, quad x = quad 0 → x = 0 := by
    intro x hx
    rw [hq0] at hx
    funext i
    fin_cases i
    simp [quad] at hx
    simpa using hx
  set ω := sInf ((fun z => quad (0 + z) - quad 0) '' {z : Vec 1 | ‖euclideanVector z‖ = 2})
    with hω
  obtain ⟨-, hleast, -⟩ := sphere_min le_rfl quad quad_convex 0 hmin huniq 2 two_pos ω hω
  obtain ⟨z0, hz0, hz0ω⟩ := hleast.1
  have hsq : sqNorm z0 = 4 := by
    have h := euclid_norm_sq z0
    rw [show ‖euclideanVector z0‖ = 2 from hz0] at h
    linarith
  have hωval : ω = 2 := by
    rw [← hz0ω]
    simp only [zero_add, hq0, sub_zero]
    simp only [sqNorm, Fin.sum_univ_one] at hsq
    simp only [quad]
    linarith
  refine ⟨quad, 0, Set.univ, 2, ω, le_rfl, quad_convex, hmin, huniq, Filter.univ_mem, two_pos,
    Set.subset_univ _, hω, run, ?_⟩
  rw [hωval, hq0]
  show quad (pt 0) - 0 < 2
  norm_num [quad, pt]

/-- The assumptions of Lemma `M:strictcontours` can all hold, with a positive limiting level:
an actual failing run of the article's Theorem `art:local-failure-lower` (constants
$(c_1,c_2)=(1/4,1/2)$) on its strongly convex objective `LUniform.smoothObjective`, whose
minimum is $F_*=0$ at the origin. The run converges to a nonstationary center at a level
$\ell>0$; strong convexity gives strict contours. -/
example : ∃ (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F) (b ℓ Fstar : ℝ),
    IsCompact {x | F x ≤ b} ∧ (∀ k, F (R.x k) ≤ b) ∧ Antitone (fun k => F (R.x k)) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) ∧ IsLeast (Set.range F) Fstar ∧ ℓ > Fstar ∧
      ∀ x z : Vec 2, segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z := by
  obtain ⟨hκ, -, hgeom, -, -, -, -, htarget, -⟩ := LUniform.uniformSmoothLocalFailure
  obtain ⟨hconv, hstrong, h0, hlower, -, hcompact, -, -⟩ := hgeom
  obtain ⟨x, H, g, -, -, hruns⟩ := htarget
  obtain ⟨R, hR, -⟩ := hruns (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, -, -, hfail⟩ := hR 0
  obtain ⟨-, -, -, -, hvlim, hpos, -⟩ := hfail
  have hmin : ∀ z, 0 ≤ LUniform.smoothObjective z := fun z =>
    le_trans (by have := sqNorm_nonneg z; positivity) (hlower z)
  refine ⟨LUniform.smoothObjective, R 0, LUniform.smoothObjective ((R 0).x 0), _, 0,
    hcompact _, fun k => (R 0).objective_le_initial k, (R 0).objective_antitone, hvlim,
    ⟨⟨0, h0⟩, ?_⟩, hpos, strong_convex_strict_contours (convex_continuous hconv) _ hκ hstrong _⟩
  rintro _ ⟨z, rfl⟩
  exact hmin z

/-- The assumptions of Theorem `M:hierarchy` and of its proof displays can hold at once:
$n=j=1$, $H=Z=I$, $g=1$, $y=-1$, $\alpha=1$, so that $s=-1$, $q=1$, $\beta=1$. -/
example : ∃ (H Hplus : Mat 1) (g y s : Vec 1) (α q β : ℝ) (Z : Matrix (Fin 1) (Fin 1) ℝ),
    H.PosDef ∧ s = -α • (H *ᵥ g) ∧ 0 < α ∧ q = dot g (H *ᵥ g) ∧ 0 < q ∧
      β = -dot y (H *ᵥ g) / q ∧ 0 < β ∧ Hplus = inverseBFGS H s y ∧
      Zᵀ * Z = 1 ∧ 1 ≤ 1 ∧ 1 ≤ 1 := by
  refine ⟨1, _, ![1], ![-1], _, 1, 1, 1, 1, Matrix.PosDef.one, rfl, one_pos, ?_, one_pos, ?_,
    one_pos, rfl, by simp, le_rfl, le_rfl⟩
  · simp [dot]
  · simp [dot]

/-- On the quadratic run with $x_*=0$: $\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$ and
$\sum_{k<N}R_k=O(N^2)$, so the assumptions of `negligible_corrections`,
`negligible_corrections_of_divergent` and `quadratic_corrections` (and of the energy
statements of Section `M:energy`) can all hold. -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (xstar : Vec 1) (Fstar : ℝ)
    (r : ℕ → Vec 1) (Rk : ℕ → ℝ),
    (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ Summable R.d ∧ (∀ z, F xstar ≤ F z) ∧
      Fstar = F xstar ∧ (∀ k, r k = R.x k - xstar) ∧
      (∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k) ∧
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop ∧
      ((fun N : ℕ => ∑ k ∈ Finset.range N, Rk k) =o[atTop]
        (fun N : ℕ => ∑ k ∈ Finset.range N, (R.q k)⁻¹)) ∧
      ((fun N : ℕ => ∑ k ∈ Finset.range N, Rk k) =O[atTop] (fun N : ℕ => (N : ℝ) ^ 2)) := by
  have hq0 : quad 0 = 0 := by simp [quad]
  have hRk_le : ∀ k, dot (run.gradientChange k) (run.x (k + 1) - 0) ^ 2 / run.curvature k ≤ 1 :=
    run_correction
  have hRk_nn : ∀ k, 0 ≤ dot (run.gradientChange k) (run.x (k + 1) - 0) ^ 2 / run.curvature k :=
    fun k => div_nonneg (sq_nonneg _) (run.curvature_pos k).le
  set f := fun N : ℕ => ∑ k ∈ Finset.range N,
    dot (run.gradientChange k) (run.x (k + 1) - 0) ^ 2 / run.curvature k with hf
  have hfN : ∀ N : ℕ, f N ≤ N := fun N => by
    calc f N ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun k _ => hRk_le k
      _ = N := by simp
  have hf0 : ∀ N, 0 ≤ f N := fun N => Finset.sum_nonneg fun k _ => hRk_nn k
  have hS : ∀ N : ℕ, 1 ≤ N → (4 : ℝ) ^ N ≤ 4 * ∑ k ∈ Finset.range N, (run.q k)⁻¹ := by
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ, run_q_inv]
    have hnn : 0 ≤ ∑ k ∈ Finset.range N', (run.q k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (run.q_pos k)).le
    rw [pow_succ]
    nlinarith
  have hdiv : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (run.q k)⁻¹) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h4 := hS N hN
    have hN4 : (N : ℝ) ≤ 4 ^ N / 4 := by
      have := Nat.lt_pow_self (by norm_num : 1 < 4) (n := N)
      have h' : (N : ℝ) < 4 ^ N := by exact_mod_cast this
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (4 : ℝ) ^ N = 4 * 4 ^ (N - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hN]
      have h4N : (N : ℝ) ≤ 4 ^ (N - 1) := by
        have := Nat.lt_pow_self (by norm_num : 1 < 4) (n := N - 1)
        have h'' : ((N - 1 : ℕ) : ℝ) + 1 ≤ 4 ^ (N - 1) := by exact_mod_cast this
        rw [Nat.cast_sub hN] at h''
        push_cast at h''
        linarith
      rw [this]
      linarith
    linarith
  have hO : f =O[atTop] (fun N : ℕ => (N : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with N
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 N),
      abs_of_nonneg (Nat.cast_nonneg N), one_mul]
    exact hfN N
  have hpow : (fun N : ℕ => (4 : ℝ) ^ N) =O[atTop]
      (fun N : ℕ => ∑ k ∈ Finset.range N, (run.q k)⁻¹) := by
    apply Asymptotics.IsBigO.of_bound 4
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hnn : 0 ≤ ∑ k ∈ Finset.range N, (run.q k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (run.q_pos k)).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hnn]
    exact hS N hN
  have hlo : f =o[atTop] (fun N : ℕ => ∑ k ∈ Finset.range N, (run.q k)⁻¹) :=
    (hO.trans_isLittleO
      (isLittleO_coe_const_pow_of_one_lt (R := ℝ) (by norm_num : (1 : ℝ) < 4))).trans_isBigO hpow
  have hO2 : f =O[atTop] (fun N : ℕ => (N : ℝ) ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with N
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 N), abs_of_nonneg (by positivity),
      one_mul]
    have hN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h
        simp
      · have : (1 : ℝ) ≤ N := by exact_mod_cast h
        nlinarith
    exact (hfN N).trans hN
  refine ⟨quad, run, 0, quad 0, fun k => run.x k - 0, fun k =>
    dot (run.gradientChange k) (run.x (k + 1) - 0) ^ 2 / run.curvature k, ⟨1, run_bounded⟩,
    run_summable, fun z => by rw [hq0]; exact quad_nonneg z, rfl, fun _ => rfl, fun _ => rfl,
    hdiv, hlo, hO2⟩

/-- The assumptions of `frame_identity` and `normalized_trace_step` can hold: on the quadratic
run, the frames $V_k=0\in\R^{1\times1}$, $T_k=I$, $b_k=0$ and $P_k=I$. (The full suppositions of
display `C/02_M/disp/030` and of `frame_criterion`, with $\|a_k\|\ge\epsilon>0$, are exhibited
on `logRun` below; they cannot hold together with bounded gradients and $d_k\to0$, which is what
`frame_criterion` shows.) -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (V : ℕ → Matrix (Fin 1) (Fin 1) ℝ)
    (T P : ℕ → Mat 1) (b : ℕ → Vec 1),
    (∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k)) ∧
      (∀ k, (P k).det ≠ 0) ∧ ∀ k, P (k + 1) = P k * T k := by
  refine ⟨quad, run, fun _ => 0, fun _ => 1, fun _ => 1, fun _ => 0, fun k => ?_,
    fun k => by simp, fun k => by simp⟩
  ext i j
  simp [EnergyIdentities.rectOuter]

/-- The assumptions of Theorem `M:residualtheorem` and of the general forms of its proof
displays (`projection_trace_step`, `frame_energy_step`, `frame_young_step`,
`residual_energy_step`, `residual_recurrence_step`) can all hold: the quadratic run (bounded
gradients, $\sum_kd_k<\infty$), $S=\{0\}$ with $P_S=0$ and $L_S=0$, frames of width one
$V_k=0$, $T_k=0$, $b_k=0$, $R_k=0$, $m=C_0=C_T=C_R=0$, and $k=0$ ($d_0=1/2\le1$). (The proof's
standing assumptions add frames with $m>0$ on a tail, which the theorem excludes.) -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (S : Submodule ℝ (EuclideanSpace ℝ (Fin 1)))
    (PS : Mat 1) (LS : ℝ) (V : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (T : ℕ → Mat 1) (b : ℕ → Vec 1)
    (Rres : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (m C0 CT CR : ℝ) (k : ℕ),
    (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ Summable R.d ∧
      (∀ k, ‖(S.orthogonalProjection (euclideanVector (R.gradientChange k)) :
        EuclideanSpace ℝ (Fin 1))‖ ^ 2 ≤ LS * R.curvature k) ∧
      (∀ v : Vec 1, euclideanVector (PS *ᵥ v) =
        (S.orthogonalProjection (euclideanVector v) : EuclideanSpace ℝ (Fin 1))) ∧
      0 ≤ LS ∧ 0 ≤ C0 ∧ 0 ≤ CR ∧ R.d k ≤ 1 ∧
      ‖euclideanVector ((V k)ᵀ *ᵥ R.g k)‖ ^ 2 ≥ m ∧
      ‖euclideanVector ((V (k + 1))ᵀ *ᵥ R.gradientChange k)‖ ^ 2 ≤ C0 * R.curvature k ∧
      V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k) + Rres k ∧
      FrameNorms.euclideanOpNorm (T k) ^ 2 ≤ 1 + CT * R.d k ∧
      (∀ v : Vec 1, euclideanVector (Rres k *ᵥ v) ∈ S) ∧
      SmoothSubspace.frobSq (Rres k) ≤ CR * R.d k := by
  have hproj : ∀ v : EuclideanSpace ℝ (Fin 1),
      ((⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 1))).orthogonalProjection v :
        EuclideanSpace ℝ (Fin 1)) = 0 := by
    intro v
    rw [Submodule.orthogonalProjection_bot]
    rfl
  refine ⟨quad, run, ⊥, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0,
    ⟨1, run_bounded⟩, run_summable, fun k => by rw [hproj]; simp,
    fun v => by rw [hproj, Matrix.zero_mulVec]; rfl,
    le_rfl, le_rfl, le_rfl, ?_, by simp [euclideanVector_zero], by simp [euclideanVector_zero],
    ?_, ?_, fun v => by simp [euclideanVector_zero], by simp [SmoothSubspace.frobSq]⟩
  · rw [run_d]
    norm_num
  · ext i j
    simp [EnergyIdentities.rectOuter]
  · simp [FrameNorms.euclideanOpNorm]

/-! #### A run satisfying the suppositions of the moving-frame criterion

The objective $f(t)=1-t$ for $t\le1$, $f(t)=-\log t$ for $t\ge1$ on $\R^1$ ($C^1$ and convex,
unbounded below) and the run $x_k=2^{k+1}$, $H_k=x_k^2/2$, $\alpha_k=2$,
$(c_1,c_2)=(1/4,1/2)$: $s_k=x_k$, $g_k=-1/x_k$, $y_k=1/(2x_k)$, $t_k=1/2$, $q_k=1/2$, $d_k=1$. -/

/-- The scalar profile $f(t)=1-t$ for $t\le1$, $f(t)=-\log t$ for $t>1$. -/
def logScalar (t : ℝ) : ℝ := if t ≤ 1 then 1 - t else -Real.log t

/-- The objective $F(x)=f(x_0)$ on $\R^1$. -/
def logObjective (x : Vec 1) : ℝ := logScalar (x 0)

/-- Every point has a supporting line of $f$: slope $-1$ at $z\le1$, $-1/z$ at $z>1$. -/
theorem logScalar_support (z w : ℝ) :
    logScalar z + (if z ≤ 1 then -1 else -z⁻¹) * (w - z) ≤ logScalar w := by
  have hlog2 : ∀ u : ℝ, 0 < u → Real.log u ≤ u - 1 := fun u hu => Real.log_le_sub_one_of_pos hu
  unfold logScalar
  by_cases hz : z ≤ 1
  · by_cases hw : w ≤ 1
    · simp only [hz, hw, if_true]
      linarith
    · simp only [hz, hw, if_true, if_false]
      have hw1 : 1 < w := lt_of_not_le hw
      linarith [hlog2 w (by linarith)]
  · have hz1 : 1 < z := lt_of_not_le hz
    have hzpos : 0 < z := by linarith
    have hinv : 1 - z⁻¹ ≤ Real.log z := by
      have h := hlog2 z⁻¹ (inv_pos.mpr hzpos)
      rw [Real.log_inv] at h
      linarith
    by_cases hw : w ≤ 1
    · simp only [hz, hw, if_true, if_false]
      have hpos : 0 ≤ 1 - z⁻¹ := by
        have : z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz1.le
        linarith
      have h1 : w * (1 - z⁻¹) ≤ 1 - z⁻¹ := by nlinarith
      have h2 : -z⁻¹ * (w - z) = 1 - w * z⁻¹ := by field_simp
      rw [h2]
      nlinarith
    · simp only [hz, hw, if_false]
      have hw1 : 1 < w := lt_of_not_le hw
      have hwpos : 0 < w := by linarith
      have h := hlog2 (w / z) (div_pos hwpos hzpos)
      rw [Real.log_div hwpos.ne' hzpos.ne'] at h
      have h2 : -z⁻¹ * (w - z) = 1 - w / z := by field_simp
      rw [h2]
      linarith

theorem logObjective_convex : ConvexOn ℝ Set.univ logObjective := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set z := (a • x + b • y) 0 with hz
  have hzv : z = a * x 0 + b * y 0 := by simp [hz]
  have h1 := logScalar_support z (x 0)
  have h2 := logScalar_support z (y 0)
  set m := (if z ≤ 1 then -1 else -z⁻¹ : ℝ)
  simp only [logObjective, smul_eq_mul]
  rw [← hz]
  have hcomb : a * (logScalar z + m * (x 0 - z)) + b * (logScalar z + m * (y 0 - z)) =
      logScalar z := by
    rw [hzv]
    have hb' : b = 1 - a := by linarith
    subst hb'
    ring
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem logScalar_hasDerivAt (t : ℝ) (ht : 1 < t) : HasDerivAt logScalar (-t⁻¹) t := by
  have hlog : HasDerivAt (fun s => -Real.log s) (-t⁻¹) t :=
    (Real.hasDerivAt_log (by linarith)).neg
  apply hlog.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  simp [logScalar, not_le.mpr hs]

theorem logObjective_embed (t : ℝ) (ht : 1 < t) :
    logObjective (OneDimensional.embed t) = -Real.log t := by
  simp [logObjective, logScalar, not_le.mpr ht]

theorem dot_embed (a b : ℝ) : dot (OneDimensional.embed a) (OneDimensional.embed b) = a * b := by
  simp [dot]

theorem sqNorm_embed (t : ℝ) : sqNorm (OneDimensional.embed t) = t ^ 2 := by
  simp [sqNorm]

theorem diagonal_mulVec_embed (h t : ℝ) :
    (Matrix.diagonal fun _ : Fin 1 => h) *ᵥ OneDimensional.embed t =
      OneDimensional.embed (h * t) := by
  funext i
  simp [Matrix.mulVec_diagonal]

/-- $H_k=x_k^2/2=2(2^k)^2$. -/
def logMetric (k : ℕ) : Mat 1 := Matrix.diagonal fun _ => 2 * (2 ^ k) ^ 2

/-- $g_k=-1/x_k$ with $x_k=2\cdot2^k$. -/
def logGrad (k : ℕ) : Vec 1 := OneDimensional.embed (-(2 * 2 ^ k)⁻¹)

theorem log_step (k : ℕ) :
    bfgsStep (logMetric k) (logGrad k) 2 = OneDimensional.embed (2 * 2 ^ k) := by
  funext i
  simp [bfgsStep, logMetric, logGrad, Matrix.mulVec_diagonal]
  field_simp
  ring

theorem log_gradChange (k : ℕ) :
    logGrad (k + 1) - logGrad k = OneDimensional.embed (4 * 2 ^ k)⁻¹ := by
  funext i
  simp [logGrad, pow_succ]
  field_simp
  ring

/-- The inverse BFGS update in dimension one: $H_+=s/y$ when $sy\ne0$. -/
theorem inverseBFGS_one_dim (h s y : ℝ) (hsy : s * y ≠ 0) :
    inverseBFGS (Matrix.diagonal fun _ : Fin 1 => h) (OneDimensional.embed s)
        (OneDimensional.embed y) = Matrix.diagonal fun _ => s / y := by
  have hs : s ≠ 0 := left_ne_zero_of_mul hsy
  have hy : y ≠ 0 := right_ne_zero_of_mul hsy
  ext i j
  fin_cases i
  fin_cases j
  simp [inverseBFGS, outer, dot, Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  field_simp
  ring

/-- The run of the witness: $x_k=2\cdot2^k$, $H_k=2(2^k)^2$, $g_k=-1/x_k$, $\alpha_k=2$,
$(c_1,c_2)=(1/4,1/2)$ on `logObjective`. -/
def logRun : AdmissibleBFGSRun 1 logObjective where
  convex := logObjective_convex
  x := fun k => OneDimensional.embed (2 * 2 ^ k)
  H := logMetric
  g := logGrad
  α := fun _ => 2
  c₁ := 1 / 4
  c₂ := 1 / 2
  c₁_pos := by norm_num
  c₁_lt_c₂ := by norm_num
  c₂_lt_one := by norm_num
  initial_posDef := Matrix.posDef_diagonal_iff.mpr fun _ => by norm_num
  alpha_pos := fun _ => by norm_num
  gradient_nonzero := fun k h => by
    have := congrFun h 0
    simp [logGrad] at this
  hasGradient := fun k =>
    ScalarCounterexamples.coordinate_hasGradient (logScalar_hasDerivAt (2 * 2 ^ k)
      (by have := one_le_pow₀ (M₀ := ℝ) (n := k) one_le_two; linarith))
  step := fun k => by
    rw [log_step]
    funext i
    simp [pow_succ]
    ring
  update := fun k => by
    rw [log_step, log_gradChange]
    unfold logMetric
    rw [inverseBFGS_one_dim _ _ _ (by positivity)]
    ext i j
    simp [Matrix.diagonal_apply, pow_succ]
    split_ifs
    · field_simp
      ring
    · rfl
  armijo := fun k => by
    have hk1 : (1 : ℝ) < 2 * 2 ^ k := by
      have := one_le_pow₀ (M₀ := ℝ) (n := k) one_le_two
      linarith
    have hk2 : (1 : ℝ) < 2 * 2 ^ (k + 1) := by
      have := one_le_pow₀ (M₀ := ℝ) (n := k + 1) one_le_two
      linarith
    rw [log_step, logObjective_embed _ hk1, logObjective_embed _ hk2]
    have hdot : dot (logGrad k) (OneDimensional.embed (2 * 2 ^ k)) = -1 := by
      rw [logGrad, dot_embed, neg_mul, inv_mul_cancel₀ (by positivity)]
    rw [hdot, pow_succ, show (2 : ℝ) * (2 ^ k * 2) = 2 * (2 * 2 ^ k) by ring,
      Real.log_mul two_ne_zero (by positivity)]
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      rw [one_div, Real.log_inv] at h
      linarith
    linarith
  weak_wolfe := fun k => by
    rw [log_step, logGrad, logGrad, dot_embed, dot_embed, neg_mul, inv_mul_cancel₀ (by positivity),
      pow_succ]
    have h : -(2 * (2 ^ k * 2))⁻¹ * (2 * 2 ^ k) = (-1 / 2 : ℝ) := by
      field_simp
      ring
    rw [h]
    norm_num

theorem logRun_displacement (k : ℕ) :
    logRun.displacement k = OneDimensional.embed (2 * 2 ^ k) :=
  log_step k

theorem logRun_gradientChange (k : ℕ) :
    logRun.gradientChange k = OneDimensional.embed (4 * 2 ^ k)⁻¹ :=
  log_gradChange k

theorem logRun_curvature (k : ℕ) : logRun.curvature k = 1 / 2 := by
  rw [AdmissibleBFGSRun.curvature, logRun_displacement, logRun_gradientChange]
  simp [dot]
  field_simp
  ring

/-- The frames $V_k=[x_k]\in\R^{1\times1}$ of the witness. -/
def logFrame (k : ℕ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 2 * 2 ^ k

theorem logFrame_mulVec (k : ℕ) (t : ℝ) :
    (logFrame k)ᵀ *ᵥ OneDimensional.embed t = OneDimensional.embed (2 * 2 ^ k * t) := by
  funext i
  simp [logFrame, Matrix.mulVec, dotProduct]

/-- $a_k=V_k^Tg_k=-1$. -/
theorem log_a (k : ℕ) : (logFrame k)ᵀ *ᵥ logRun.g k = OneDimensional.embed (-1) := by
  change (logFrame k)ᵀ *ᵥ logGrad k = _
  rw [logGrad, logFrame_mulVec, mul_neg, mul_inv_cancel₀ (by positivity)]

/-- $c_k=V_{k+1}^Ty_k=1$. -/
theorem log_c (k : ℕ) :
    (logFrame (k + 1))ᵀ *ᵥ logRun.gradientChange k = OneDimensional.embed 1 := by
  rw [logRun_gradientChange, logFrame_mulVec, pow_succ,
    show (2 : ℝ) * (2 ^ k * 2) = 4 * 2 ^ k by ring, mul_inv_cancel₀ (by positivity)]

/-- The suppositions of the moving-frame criterion (display `C/02_M/disp/030`, the O(N) part of
`frame_criterion`) are satisfiable: on `logRun` take frames $V_k=[x_k]$, $T_k=1$, $b_k=1$,
$P_k=1$, $J=0$, $\epsilon=1$, $C=2$ (then $a_k=-1$ and $c_k=1$). The run has bounded gradients but
$d_k=1$ for every $k$, so Theorem `M:average` does not apply; its values tend to
$\inf F=-\infty$, so the tail is not "nonoptimal" in the sense of line 204 (a descriptive word,
not a hypothesis of the Lean statements). -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (V : ℕ → Matrix (Fin 1) (Fin 1) ℝ)
    (T : ℕ → Mat 1) (b : ℕ → Vec 1) (A : ℕ → Mat 1) (a c : ℕ → Vec 1) (J : ℕ) (ε C : ℝ)
    (P At : ℕ → Mat 1),
    (∀ k, V (k + 1) = V k * T k + EnergyIdentities.rectOuter (R.displacement k) (b k)) ∧
      (∀ k, A k = (V k)ᵀ * R.hessian k * V k) ∧ (∀ k, a k = (V k)ᵀ *ᵥ R.g k) ∧
      (∀ k, c k = (V (k + 1))ᵀ *ᵥ R.gradientChange k) ∧
      0 < ε ∧ (∀ k, J ≤ k → ‖euclideanVector (a k)‖ ≥ ε) ∧
      (∀ k, J ≤ k → sqNorm (c k) / R.curvature k ≤ C) ∧
      P J = 1 ∧ (∀ k, J ≤ k → P (k + 1) = P k * T k) ∧
      (∃ K : ℝ, ∀ k, J ≤ k → FrameNorms.euclideanOpNorm (P k) ≤ K) ∧
      (∀ k, J ≤ k → (P k).det ≠ 0) ∧
      (∃ L : ℝ, ∀ k, J ≤ k → FrameNorms.euclideanOpNorm (P k)⁻¹ ≤ L) ∧
      (∀ k, At k = ((P k)⁻¹)ᵀ * A k * (P k)⁻¹) ∧
      (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ ∀ k, R.d k = 1 := by
  refine ⟨logObjective, logRun, logFrame, fun _ => 1, fun _ => OneDimensional.embed 1,
    fun k => (logFrame k)ᵀ * logRun.hessian k * logFrame k, fun k => (logFrame k)ᵀ *ᵥ logRun.g k,
    fun k => (logFrame (k + 1))ᵀ *ᵥ logRun.gradientChange k, 0, 1, 2, fun _ => 1,
    fun k => ((1 : Mat 1)⁻¹)ᵀ * ((logFrame k)ᵀ * logRun.hessian k * logFrame k) * (1 : Mat 1)⁻¹,
    fun k => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, one_pos, fun k _ => ?_, fun k _ => ?_,
    rfl, fun k _ => by simp, ⟨_, fun k _ => le_rfl⟩, fun k _ => by simp, ⟨_, fun k _ => le_rfl⟩,
    fun _ => rfl, ⟨1, fun k => ?_⟩, fun k => ?_⟩
  · rw [logRun_displacement]
    ext i j
    simp only [logFrame, Matrix.mul_one, Matrix.add_apply, EnergyIdentities.rectOuter,
      OneDimensional.embed_apply, mul_one, pow_succ]
    ring
  · dsimp only
    rw [log_a]
    have h := euclid_norm_sq (OneDimensional.embed (-1 : ℝ))
    rw [sqNorm_embed] at h
    nlinarith [norm_nonneg (euclideanVector (OneDimensional.embed (-1 : ℝ)))]
  · dsimp only
    rw [log_c, sqNorm_embed, logRun_curvature]
    norm_num
  · apply euclid_norm_le_of_sqNorm_le zero_le_one
    change sqNorm (logGrad k) ≤ 1 ^ 2
    have hk : (1 : ℝ) ≤ 2 * 2 ^ k := by
      have := one_le_pow₀ (M₀ := ℝ) (n := k) one_le_two
      linarith
    rw [logGrad, sqNorm_embed, neg_sq, one_pow]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hk)
  · change 2 * dot (logGrad k) (logMetric k *ᵥ logGrad k) = 1
    rw [logGrad, logMetric, diagonal_mulVec_embed, dot_embed]
    field_simp
    ring

end Examples

end BfgsCoverage.Companion.Ch02M
