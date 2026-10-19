import BfgsVerification.HomogeneousSourceConsequences
import BfgsVerification.HomogeneousPlanarEscape
import BfgsVerification.HomogeneousRelativeInteriorConvergence
import BfgsVerification.HomogeneousCardinality
import BfgsVerification.SeedRecurrentRank
import BfgsVerification.TwoPieceTargets
import BfgsVerification.HomogeneousBlockStitching
import BfgsVerification.HomogeneousPlanarFiniteValue
import BfgsVerification.HomogeneousLowRankConvergence
import BfgsVerification.HomogeneousBlockControl
import BfgsVerification.HomogeneousBlockTransport
import BfgsArticle.Coverage.Article.Global
import BfgsArticle.Coverage.Article.Energy
import BfgsArticle.Coverage.Article.Master
import BfgsArticle.AdmissibleRunExistence

/-!
# Lean coverage: `companion/chapters/07_H.tex`

Chapter 7 of the companion ("Homogeneous objectives without compactness"): Theorems 7.A, 7.B,
7.C (stated as subsection headings), Lemma 7.3 (bold text), the displays (several numbered by
hand, (7.2.1)-(7.8.1)), and the claims of the running text. Register:
`editorial/lean_coverage/register/C_07_H.json`.

## Standing assumptions and Lean forms

* "$f$ finite, convex, positively homogeneous of degree one" is `F : Vec n → ℝ` with
  `ConvexOn ℝ univ F` and `Homogeneous.PositiveDegreeOne F` ($F(tx)=tF(x)$ for $t\ge0$); the
  dimension `n` is arbitrary.
* A finite max-linear objective $f(x)=\max_{1\le i\le m}a_i^Tx$ (display `disp/001`) is
  `a : Fin m → Vec n` with `hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)`
  (the article's form); `maxLinear_family` and `maxLinear_eq` identify it with the library's
  `Homogeneous.finiteMaxLinear` of the slope set.
* An infinite admissible run is `R : AdmissibleBFGSRun n F` (Definition `art:admissible` of the
  article, the convention of `companion/chapters/01_I.tex:25-46`: nonzero gradients at
  differentiable accepted points, $H_0\succ0$, positive lengths, fixed $0<c_1<c_2<1$ with
  Armijo and weak Wolfe; the structure also records convexity of `F`). Statements about every
  run quantify `∀ R`. Lemma 7.3, which needs no convexity, is stated for explicit sequences
  `x H g α` and an arbitrary `F` (see its section).
* The recurrent gradients $G$ (gradients occurring infinitely often) are a variable with its
  defining equation `G = {v | ∃ᶠ k in atTop, R.g k = v}` (the library's
  `Homogeneous.recurrentValues R.g`); $\operatorname{aff}$ is `affineSpan ℝ`,
  $\operatorname{span}$ is `Submodule.span ℝ`, $\dim$ is `Module.finrank ℝ`.
* Objects that the text introduces are variables with their defining equations: $p_k$, $c$,
  $\beta_k$ (Section 7.2), $h_k,\ell_k,\gamma,\Phi_k$ (Section 7.5.2), $M$ (line 363), $v$
  (Lemma 7.3), $\widehat x_k,\widehat H_k,\widehat g_k,L_K$ (Section 7.7.1), $g,\kappa$ of a
  block (Section 7.7.4), $S,P$ and $x_*$ (Section 7.8). A hypothesis whose name starts with `_`
  is a standing assumption that the Lean proof does not use.

## Notation

| TeX | Lean |
|---|---|
| $g_k,\ x_k,\ H_k,\ \alpha_k,\ c_1,\ c_2$ | `R.g k`, `R.x k`, `R.H k`, `R.α k`, `R.c₁`, `R.c₂` |
| $s_k=-\alpha_kH_kg_k$, $y_k$, $t_k=y_k^Ts_k$ | `R.displacement k`, `R.gradientChange k`, `R.curvature k` |
| $B_k=H_k^{-1}$, $q_k=g_k^TH_kg_k$, $d_k=\alpha_kq_k$, $\beta_k$ | `R.hessian k`, `R.q k`, `R.d k`, `R.beta k` |
| $f_k=f(x_k)$, $\Delta_k$ | `F (R.x k)`, `F (R.x k) - F (R.x (k + 1))` |
| $x^TBx$ | `dot x (B *ᵥ x)` |
| $\|v\|$ | `‖euclideanVector v‖` (Euclidean); `‖v‖` is the sup norm of `Vec n` |
| $\inf f=-\infty$ | `¬ BddBelow (Set.range F)` |
| $u,v$ linearly independent | `LinearIndependent ℝ ![u, v]` (in the plane: `HomogeneousPlanar.pairDet u v ≠ 0`, `linearIndependent_pair_iff`) |
| $\partial f(x)$ | `ConvexSubdifferential.subdifferential F x`, or the subgradient inequality written out |
| $(u,t)\in\R^{n+1}$, $t$ last | `Fin.snoc u t` |

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/001` (definition) | 32-34 | `maxLinear_family` |
| `heading/001` Theorem 7.A (with `disp/002`) | 47-56 | `theorem_7A` |
| `prose/007`-`prose/009` | 62-66 | `bounded_below_consequence`, `coercive_consequence`, `nonpositive_value_consequence` |
| `heading/002` Theorem 7.B (with `disp/003`, `disp/004`) | 72-89 | `theorem_7B` |
| `disp/005`, `prose/011` | 94-99 | `tilt_family`, `tilt_family_escape` |
| `heading/003` Theorem 7.C (with `disp/006`, `disp/007`) | 117-133 | `theorem_7C` |
| `prose/013`, `prose/014`, `prose/016` | 135-143 | `theorem_7C_nonstationary`, `seed_attains_first_alternative`, `recurrent_rank_le_two_convergence` |
| `prose/018` (open question) | 153-157 | `ZeroValueIterateQuestion` |
| `prose/003`, `disp/008`-`disp/012`, `prose/020`, `prose/021` | 24-28, 181-229 | `run_setting`, `notation_display`, `line_search_conditions`, `curvature_and_beta`, `inverse_update`, `hessian_form`, `zero_gradient_stationary`, `admissible_convention` |
| `disp/013`, `prose/023`, `disp/014`, `prose/025`, `prose/026` | 258-272 | `euler_identity`, `subgradients_at_zero`, `subgradient_sphere_bound`, `dimension_zero`, `bounded_gradients_automatic` |
| `disp/015`-`disp/020`, `prose/027` | 283-328 | `new_pairing`, `pairings_nonneg`, `decrease_sandwich`, `energy_identity`, `alpha_terms_cancel`, `correction_bounds`, `potential_step` |
| `disp/021`-`disp/024` (proof of 7.A) | 346-372 | `predicted_decrease_budget`, `weighted_sum_finite`, `energy_bound`, `value_sq_bound` |
| `prose/032` | 378 | `alternative_arrangement` |
| `prose/034`, `prose/035` | 388-395 | `bounded_below_nonneg`, `bounded_sublevels_iterates` |
| `heading/004` Lemma 7.3 | 416-419 | `lemma_7_3` |
| `disp/025`, `disp/026` (proof of Lemma 7.3) | 428-436 | `common_vector`, `common_vector_energy_step` (general forms `common_vector_general`, `common_vector_energy_step_general`) |
| `prose/040` | 442-444 | `lemma_7_3_value_limit` |
| `prose/042`, `disp/027`, `prose/044`, `prose/047`, `prose/048` | 459-482 | `two_piece_gradients`, `tilt_model_gradients`, `two_piece_finite_termination`, `recurrent_cardinality`, `seed_cardinality_sharp` |
| `prose/045` (open question) | 472-474 | `TiltNoInfiniteRunQuestion` |
| `disp/028` (definition), `prose/049`-`prose/053`, `disp/029`, `disp/030` | 509-545 | `hat_definitions`, `projected_run`, `steps_in_fixed_subspace`, `restriction_invertible`, `iterate_lift`, `limit_lift`, `zero_limit_formula`, `projected_hessian_distinction` |
| `disp/031`, `prose/054`-`prose/057` | 554-574 | `endpoint_pairings`, `independent_endpoints`, `unchanged_gradient_fails_wolfe`, `positive_multiples_active`, `dependent_transition_opposite` |
| `prose/059`, `disp/032`-`disp/036`, `prose/061` | 605-668 | `planar_finite_value_convergence`, `block_decrease`, `block_contraction`, `block_window`, `block_endpoint_difference`, `block_parameter_bound` (general form `block_general`), `recurrent_reduction_nonzero_limit` |
| `prose/062`, `disp/037` (definition), `disp/038`, `disp/039`, `prose/065`-`prose/068` | 686-730 | `flat_directions_noncompact`, `relint_def`, `relint_coercive`, `relint_limit`, `relint_limit_projection`, `relint_includes_seminorms`, `recurrent_relint_convergence`, `zero_objective_no_run` |

Undisplayed proof steps are stated too: `values_dichotomy`, `q_not_bounded_away`,
`potential_lower_bound`, `reciprocal_summable_of_weighted`, `bounded_away_of_pointwise`,
`finite_limit_zero` (proof of Theorem 7.A); `no_recurrent_subset` (proof of Theorem 7.B);
`unbounded_transitions_independent` (proof of Theorem 7.C); `no_stationary_point` (lines 593-596,
the proof of the remark `prose/013`); `block_general` (proof of the planar finite-value branch).
The displays inside proofs by contradiction (`disp/025`, `disp/026`) are stated under the
standing assumptions of the proof (`common_vector`, `common_vector_energy_step`), which are
jointly inconsistent, and in general forms (`common_vector_general`,
`common_vector_energy_step_general`) whose assumptions are satisfiable.

## Corrected discrepancy (15 October 2026)

Item `prose/028` (line 295, M17): the cross-references used the numbering of the source note, not
the chapter's: the seven equation references "(2.1)" (lines 295, 432) for (7.2.1), "(5.2)"
(line 352) for (7.5.2), "(7.3)" (lines 588, 610) for (7.7.3), "(7.1)" (line 666) for (7.7.1),
"(7.2)" (line 725) for (7.7.2), and the title of Section 7.5 (lines 245-246), "proof of Theorem
A", for Theorem 7.A. In the companion's numbering (2.1) and (5.2) are unrelated equations of
Chapters 2 and 5, (7.1)-(7.3) and a Theorem A do not exist. Since the correction the chapter
prints the intended numbers; the mathematics is proved with them (`energy_identity` from
`hessian_form`, etc.). Wording point W8 ("This chapter continues", line 23) was applied on the
same day; after the independent review of that day also W8 at line 330 ("in an earlier source
note") and W10 at line 481 ("The three-gradient, rank-two stagnation example of
Chapter~\ref{comp:D}", the seed run of Chapter 12, which comes later; before "The earlier …").

## Non-vacuity

See the examples at the end: $|x|$ on $\R$ with `Global.absRun`, the three-piece seed with
`SeedOrbit.run`, $|v|$ on $\R^2$ with `Master.absVRun`, and $|u|+|v|$ with the run of
`bw_run_exists` (the anchor hypotheses of the block displays) cover the standing assumptions of
the theorems with runs. Exception: Theorem 7.B's second part and the run statements on the
common-tilt family, for which no admissible run is exhibited. On many of these objectives none
exists (slopes on one line, in particular in dimension at most two, or the family with at most
two distinct pieces: `maxLinear_line_no_run`, `maxLinear_affine_free_no_run`,
`tilt_collinear_no_run`), so the statements are vacuous there; for slopes not on one line (at
least three pieces, dimension at least three) existence is not known (`TiltNoInfiniteRunQuestion`).
See the section "Non-vacuity".
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch07H

/-! ### Helpers -/

/-- A finite max-linear objective $F(x)=\max_ia_i^Tx$, written as `IsGreatest` of the values
$a_i^Tx$, is the library's `Homogeneous.finiteMaxLinear` of its slope set. -/
theorem maxLinear_eq {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) :
    ∃ hA : (Finset.univ.image a).Nonempty,
      F = Homogeneous.finiteMaxLinear (Finset.univ.image a) hA := by
  obtain ⟨⟨i, -⟩, -⟩ := hF_def 0
  refine ⟨⟨a i, Finset.mem_image_of_mem a (Finset.mem_univ i)⟩, funext fun x => ?_⟩
  apply le_antisymm
  · obtain ⟨⟨j, hj⟩, -⟩ := hF_def x
    rw [← hj]
    exact Homogeneous.slope_le_finiteMaxLinear _ _
      (Finset.mem_image_of_mem a (Finset.mem_univ j)) x
  · apply Finset.sup'_le
    intro b hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact (hF_def x).2 ⟨j, rfl⟩

/-- The slope set of `maxLinear_eq` is the range of the slopes. -/
theorem coe_image_univ {n m : ℕ} (a : Fin m → Vec n) :
    ((Finset.univ.image a : Finset (Vec n)) : Set (Vec n)) = Set.range a := by
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- Item `C/07_H/disp/001` (`companion/chapters/07_H.tex:32-34`): the principal family
\[ f(x)=\max_{1\le i\le m}a_i^\top x,\qquad m<\infty. \]
For finitely many slopes $a_1,\dots,a_m$ ($m\ge1$), the maximum of the values $a_i^Tx$ exists at
every $x$ and is the library's `Homogeneous.finiteMaxLinear` of the slope set; it is the only
function $F$ with $F(x)$ the greatest of the $a_i^Tx$ (the form
`∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)` used for the family throughout this
module). -/
theorem maxLinear_family {n m : ℕ} (a : Fin m → Vec n) (hm : 0 < m) :
    ∃ hA : (Finset.univ.image a).Nonempty,
      (∀ x, IsGreatest (Set.range fun i => dot (a i) x)
        (Homogeneous.finiteMaxLinear (Finset.univ.image a) hA x)) ∧
      ∀ F : Vec n → ℝ, (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) →
        F = Homogeneous.finiteMaxLinear (Finset.univ.image a) hA := by
  have hA : (Finset.univ.image a).Nonempty :=
    ⟨a ⟨0, hm⟩, Finset.mem_image_of_mem a (Finset.mem_univ _)⟩
  refine ⟨hA, fun x => ⟨?_, ?_⟩, fun F hF => ?_⟩
  · obtain ⟨b, hb, he⟩ := Homogeneous.finiteMaxLinear_active _ hA x
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨i, he.symm⟩
  · rintro _ ⟨i, rfl⟩
    exact Homogeneous.slope_le_finiteMaxLinear _ hA (Finset.mem_image_of_mem a (Finset.mem_univ i)) x
  · obtain ⟨_, h⟩ := maxLinear_eq a F hF
    exact h

/-- $(b,s)^T(u,t)=b^Tu+st$ for the vectors $(b,s),(u,t)\in\R^{n+1}$ (last coordinate $s$, $t$). -/
theorem dot_snoc {n : ℕ} (b u : Vec n) (s t : ℝ) :
    dot (Fin.snoc b s : Vec (n + 1)) (Fin.snoc u t : Vec (n + 1)) = dot b u + s * t := by
  simp only [dot, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-! ### Section 7.1: Theorem 7.A and its consequences (lines 3-66) -/

/-- Item `C/07_H/heading/001` (`companion/chapters/07_H.tex:47`), Theorem 7.A ("an
unconditional objective-value dichotomy", lines 47-56), with its display `C/07_H/disp/002`
(lines 54-56): "Let $f:\mathbb R^n\to\mathbb R$ be finite, convex, and positively homogeneous of
degree one. Every infinite admissible full-BFGS run satisfies
\[ f(x_k)\longrightarrow0\quad\text{or}\quad f(x_k)\longrightarrow-\infty. \]"
Finite means real-valued (`F : Vec n → ℝ`); positive homogeneity of degree one is
`Homogeneous.PositiveDegreeOne F` ($F(tx)=tF(x)$ for $t\ge0$); an infinite admissible run is
`AdmissibleBFGSRun n F` (whose fields include convexity of `F`, so `_hF` is not used); the
dimension `n` is arbitrary. The library proves this as
`AdmissibleBFGSRun.homogeneous_value_dichotomy` (`homogeneousDichotomy`). -/
theorem theorem_7A {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) :
    ∀ R : AdmissibleBFGSRun n F,
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∨ Tendsto (fun k => F (R.x k)) atTop atBot :=
  fun R => R.homogeneous_value_dichotomy hhom

/-- Item `C/07_H/prose/007` (`companion/chapters/07_H.tex:62`): "Consequently, if $f$ is
bounded below, then $f(x_k)\to0=\min f$." Under the hypotheses of Theorem 7.A, if $F$ is
bounded below then $0$ is the least value of $F$ and every admissible run has $F(x_k)\to0$. -/
theorem bounded_below_consequence {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hbdd : ∃ L : ℝ, ∀ x, L ≤ F x) :
    IsLeast (Set.range F) 0 ∧
      ∀ R : AdmissibleBFGSRun n F, Tendsto (fun k => F (R.x k)) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := hbdd
  refine ⟨⟨⟨0, Homogeneous.value_zero hhom⟩, ?_⟩,
    fun R => (R.homogeneous_bounded_below_convergence hhom L hL).2.2⟩
  rintro _ ⟨x, rfl⟩
  exact Homogeneous.nonneg_of_bounded_below hhom L hL x

/-- Item `C/07_H/prose/008` (`companion/chapters/07_H.tex:63`): "If $f$ is coercive, then
$x_k\to0$, its unique minimizer." Under the hypotheses of Theorem 7.A, if $F$ is coercive
(`Tendsto F (cocompact (Vec n)) atTop`), zero is the unique minimizer of $F$ and every
admissible run has $x_k\to0$. -/
theorem coercive_consequence {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hcoer : Tendsto F (cocompact (Vec n)) atTop) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨h0, hpos⟩ := BfgsCoverage.Article.Global.coercive_homogeneous_positive hhom hcoer
  refine ⟨⟨fun x => ?_, fun y hy => ?_⟩, fun R => R.homogeneous_coercive_iterates_zero hhom hcoer⟩
  · by_cases hx : x = 0
    · rw [hx]
    · rw [h0]
      exact (hpos x hx).le
  · by_contra hne
    have h1 := hpos y hne
    have h2 := hy 0
    linarith

/-- Item `C/07_H/prose/009` (`companion/chapters/07_H.tex:63-66`): "If an infinite run ever
attains $f(x_k)\le0$, its values must tend to $-\infty$; the finite-value branch has
$f(x_k)>0$ at every iteration." Under the hypotheses of Theorem 7.A, for every admissible
run: a value $F(x_k)\le0$ forces $F(x_k)\to-\infty$, and if the values have a finite limit,
then $F(x_k)>0$ for every $k$. -/
theorem nonpositive_value_consequence {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) :
    ((∃ k, F (R.x k) ≤ 0) → Tendsto (fun k => F (R.x k)) atTop atBot) ∧
      ((∃ L : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) → ∀ k, 0 < F (R.x k)) :=
  ⟨fun ⟨k, hk⟩ => R.homogeneous_nonpositive_forces_escape hhom k hk,
    fun ⟨L, hL⟩ k => R.homogeneous_finite_branch_positive hhom L hL k⟩

/-! ### Theorem 7.B and the common-tilt family (lines 72-100) -/

/-- Item `C/07_H/heading/002` (`companion/chapters/07_H.tex:72`), Theorem 7.B ("a many-piece
extension of the common-tilt geometry", lines 72-89), with its displays `C/07_H/disp/003`
(lines 79-81) and `C/07_H/disp/004` (lines 85-89): "For a finite max-linear objective, let $G$
be the set of gradients occurring infinitely often. If the objective values have a finite
limit, then $0\in\operatorname{aff}G$. [...] In particular,
\[ 0\notin\operatorname{aff}\{a_1,\ldots,a_m\}\Longrightarrow f(x_k)\longrightarrow-\infty \]
for every infinite admissible run."
The objective is $F(x)=\max_{1\le i\le m}a_i^Tx$ (`IsGreatest` of the values $a_i^Tx$); $G$ is
the variable with its defining equation $G=\{v : g_k=v$ for infinitely many $k\}$;
$\operatorname{aff}$ is `affineSpan ℝ`. The library proves both parts as
`AdmissibleBFGSRun.maxLinear_recurrent_affine_zero` (`recurrentAffineHull`) and
`AdmissibleBFGSRun.maxLinear_escape_of_zero_not_mem_affineSpan` (`maxLinearAffineEscape`). Part
(ii) is vacuous when the slopes lie on one line, in particular in dimension at most two: no
admissible run exists there (`maxLinear_line_no_run`, `maxLinear_affine_free_no_run`). -/
theorem theorem_7B {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) :
    (∀ (R : AdmissibleBFGSRun n F) (G : Set (Vec n)), G = {v | ∃ᶠ k in atTop, R.g k = v} →
        (∃ L : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) → (0 : Vec n) ∈ affineSpan ℝ G) ∧
      ((0 : Vec n) ∉ affineSpan ℝ (Set.range a) →
        ∀ R : AdmissibleBFGSRun n F, Tendsto (fun k => F (R.x k)) atTop atBot) := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  refine ⟨fun R G hG ⟨L, hL⟩ => ?_, fun h0 R => ?_⟩
  · rw [hG]
    exact AdmissibleBFGSRun.maxLinear_recurrent_affine_zero _ hA R L hL
  · apply AdmissibleBFGSRun.maxLinear_escape_of_zero_not_mem_affineSpan _ hA R
    rwa [coe_image_univ]

/-- Item `C/07_H/disp/005` (`companion/chapters/07_H.tex:94-96`): "A useful
arbitrary-many-piece family is
\[ f(u,t)=t+\max_{1\le i\le m}b_i^\top u. \]"
Points of $\R^{n+1}$ are written $(u,t)$ with $u\in\R^n$ first and $t$ last (`Fin.snoc u t`).
If $F(u,t)=t+\max_ib_i^Tu$ for all $u,t$, then $F$ is the finite max-linear objective (the
principal family of display `C/07_H/disp/001`) with the $m$ slopes $(b_i,1)$, for every $m$
and $n$. -/
theorem tilt_family {n m : ℕ} (b : Fin m → Vec n) (F : Vec (n + 1) → ℝ)
    (hF_def : ∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) :
    ∀ x, IsGreatest (Set.range fun i => dot (Fin.snoc (b i) 1 : Vec (n + 1)) x) (F x) := by
  intro x
  have hx : x = Fin.snoc (Fin.init x) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
  have hfun : (fun i => dot (Fin.snoc (b i) 1 : Vec (n + 1)) x) =
      fun i => x (Fin.last n) + dot (b i) (Fin.init x) := by
    funext i
    conv_lhs => rw [hx]
    rw [dot_snoc]
    ring
  rw [hfun]
  have h := hF_def (Fin.init x) (x (Fin.last n))
  rwa [← hx] at h

/-- Item `C/07_H/prose/011` (`companion/chapters/07_H.tex:98-99`): "All its gradients have last
component one, so every infinite admissible run drives the values to $-\infty$." For
$F(u,t)=t+\max_ib_i^Tu$ (display `C/07_H/disp/005`): every gradient $g=\nabla F(x)$ at a
differentiable point has last component $g_{n+1}=1$, and every admissible run has
$F(x_k)\to-\infty$. The library's version, with $t$ as the first coordinate, is
`AdmissibleBFGSRun.commonTilt_value_escape`. The run statement is vacuous when the $b_i$ lie on
one line (no admissible run exists, `tilt_collinear_no_run`); otherwise existence is not known
(`TiltNoInfiniteRunQuestion`). -/
theorem tilt_family_escape {n m : ℕ} (b : Fin m → Vec n) (F : Vec (n + 1) → ℝ)
    (hF_def : ∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) :
    (∀ x g : Vec (n + 1), HasFDerivAt F (gradientFunctional g) x → g (Fin.last n) = 1) ∧
      ∀ R : AdmissibleBFGSRun (n + 1) F, Tendsto (fun k => F (R.x k)) atTop atBot := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq _ F (tilt_family b F hF_def)
  have hlast : ∀ a ∈ Finset.univ.image (fun i => (Fin.snoc (b i) 1 : Vec (n + 1))),
      a (Fin.last n) = 1 := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    simp only [Fin.snoc_last]
  refine ⟨fun x g hg => hlast g (Homogeneous.finiteMaxLinear_gradient_mem _ hA hg), fun R => ?_⟩
  apply AdmissibleBFGSRun.maxLinear_common_component_escape _ hA R (Pi.single (Fin.last n) 1)
  intro a ha
  change (Pi.single (Fin.last n) (1 : ℝ)) ⬝ᵥ a = 1
  rw [dotProduct_comm, dotProduct_single_one]
  exact hlast a ha

/-! ### Theorem 7.C (lines 117-143) -/

/-- Item `C/07_H/heading/003` (`companion/chapters/07_H.tex:116`), Theorem 7.C ("complete
iterate dichotomy in the planar unbounded-below case", lines 117-133), with its displays
`C/07_H/disp/006` (lines 125-127) and `C/07_H/disp/007` (lines 131-133): "For a finite
max-linear objective on $\mathbb R^2$ with $\inf f=-\infty$, every infinite admissible run
satisfies exactly one of $x_k\to0$, $f(x_k)\downarrow0$, or $f(x_k)\to-\infty$,
$\|x_k\|\to\infty$."
$\inf f=-\infty$ is `¬ BddBelow (Set.range F)`; "exactly one of" is `Xor'`; $f(x_k)\downarrow0$
is convergence to $0$ of the antitone (nonincreasing) sequence $F(x_k)$; $\|x_k\|$ is the
Euclidean norm. The library proves the statement with strictly decreasing positive values as
`AdmissibleBFGSRun.maxLinear_planar_unbounded_complete` (`planarHomogeneousEscape`). -/
theorem theorem_7C {m : ℕ} (a : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (hinf : ¬ BddBelow (Set.range F)) :
    ∀ R : AdmissibleBFGSRun 2 F,
      Xor' (Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧
          Antitone (fun k => F (R.x k)))
        (Tendsto (fun k => F (R.x k)) atTop atBot ∧
          Tendsto (fun k => ‖euclideanVector (R.x k)‖) atTop atTop) := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  intro R
  rcases R.maxLinear_planar_unbounded_dichotomy _ hA hinf with h | h
  · left
    exact ⟨⟨h.1, h.2.1, R.objective_antitone⟩,
      fun h' => not_tendsto_atBot_of_tendsto_nhds h.2.1 h'.1⟩
  · right
    exact ⟨h, fun h' => not_tendsto_nhds_of_tendsto_atBot h.1 0 h'.2.1⟩

/-- Item `C/07_H/prose/013` (`companion/chapters/07_H.tex:134`): "In the first alternative
the limit is nonstationary." Under the hypotheses of Theorem 7.C, the limit $0$ of the first
alternative is not a stationary point: $0\notin\partial f(0)$ (the convex subdifferential,
`ConvexSubdifferential.subdifferential`). In fact no point is stationary (`no_stationary_point`,
the proof of lines 593-596; library `Homogeneous.no_stationary_support_of_unboundedBelow`). -/
theorem theorem_7C_nonstationary {m : ℕ} (a : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (hinf : ¬ BddBelow (Set.range F)) :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F 0 :=
  Homogeneous.no_stationary_support_of_unboundedBelow hinf 0

/-- The seed objective $G(z)=\max_ig_i^Tz$ (`SeedOrbit.objective seedC seedD`) is the finite
max-linear objective with the three slopes `SeedOrbit.gradient seedC seedD`. -/
theorem seed_isGreatest (x : Vec 2) :
    IsGreatest (Set.range fun i => dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x)
      (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).branch i x)
    refine ⟨i, ?_⟩
    change _ = (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).objective x
    rw [MaxAffine.Family.objective, hi]
    simp [MaxAffine.Family.branch, SeedOrbit.family]
  · rintro _ ⟨i, rfl⟩
    have h := (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).branch_le i x
    simpa [MaxAffine.Family.branch, SeedOrbit.family] using h

/-- The seed objective is unbounded below: $G(t(-1,16))=-t$ for $t\ge0$. -/
theorem seed_unbounded :
    ¬ BddBelow (Set.range (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD)) := by
  rintro ⟨L, hL⟩
  have h := hL ⟨(|L| + 1) • SeedOrbit.downhill, rfl⟩
  rw [SeedOrbit.objective_downhill_ray (by positivity)] at h
  linarith [neg_abs_le L]

/-- Item `C/07_H/prose/014` (`companion/chapters/07_H.tex:134-135`): "The previously
constructed exact three-piece example attains that alternative." The seed objective
$G(z)=\max_{i<3}g_i^Tz$ (`SeedOrbit.objective seedC seedD`, three distinct slopes) is a finite
max-linear objective on $\R^2$ with $\inf G=-\infty$, and for every pair
$0<c_1\le1/3$, $c_1<c_2<1$ its admissible run `SeedOrbit.run` (the exact three-piece example)
satisfies the first alternative of Theorem 7.C: $x_k\to0$, $G(x_k)\downarrow0$. -/
theorem seed_attains_first_alternative :
    Function.Injective (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD) ∧
      (∀ x, IsGreatest
        (Set.range fun i => dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x)
        (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x)) ∧
      ¬ BddBelow (Set.range (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD)) ∧
      ∀ (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1),
        Tendsto (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).x atTop (𝓝 0) ∧
        Tendsto (fun k => SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD
          ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).x k)) atTop (𝓝 0) ∧
        Antitone (fun k => SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD
          ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).x k)) := by
  refine ⟨SeedOrbit.seed_gradient_injective, seed_isGreatest, seed_unbounded,
    fun c₁ c₂ hc₁ hc₁' hc hc₂ => ?_⟩
  obtain ⟨-, hx, hv, -⟩ := SeedOrbit.actual_run_failure hc₁ hc₁' hc hc₂
  exact ⟨hx, hv, (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).objective_antitone⟩

/-- Item `C/07_H/prose/016` (`companion/chapters/07_H.tex:137-140`): "More generally, for any
finite max-linear objective, if the span of the recurrent gradients has dimension at most two,
every finite-value-limit run has convergent iterates. Section 7.7 proves this broader
statement, including the noncoercive bounded-below case." For $F=\max_ia_i^Tx$ on $\R^n$ and
an admissible run whose recurrent gradient set $G$ spans a space of dimension at most two: if
$F(x_k)$ has a finite limit, then $x_k$ converges; in particular, if $F$ is bounded below
(coercive or not), $x_k$ converges. -/
theorem recurrent_rank_le_two_convergence {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (G : Set (Vec n)) (hG : G = {v | ∃ᶠ k in atTop, R.g k = v})
    (hrank : Module.finrank ℝ (Submodule.span ℝ G) ≤ 2) :
    ((∃ L : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) →
        ∃ xstar, Tendsto R.x atTop (𝓝 xstar)) ∧
      ((∃ L : ℝ, ∀ x, L ≤ F x) → ∃ xstar, Tendsto R.x atTop (𝓝 xstar)) := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  subst hG
  refine ⟨fun ⟨L, hL⟩ => ?_, fun ⟨L, hL⟩ => ?_⟩
  · obtain ⟨-, xstar, hx, -⟩ := R.maxLinear_recurrent_span_le_two_finite_value _ hA hrank L hL
    exact ⟨xstar, hx⟩
  · obtain ⟨xstar, hx, -⟩ :=
      R.maxLinear_recurrent_span_le_two_lower_bound _ hA hrank L (fun k => hL _)
    exact ⟨xstar, hx⟩

/-! ### What this does not yet establish (lines 149-162) -/

/-- Item `C/07_H/prose/018` (`companion/chapters/07_H.tex:149-151`), an open question: "The
remaining unresolved iterate question in this investigation is the zero-value branch for
noncompact objectives when the recurrent gradient span has dimension at least three. We have
neither proved that all such iterate sequences converge nor constructed a nonconvergent
zero-value-limit trajectory."
The Prop says that every such iterate sequence converges: for every finite max-linear
objective $F=\max_ia_i^Tx$ that is not coercive (noncompact sublevels) and every admissible run
whose recurrent gradients span a space of dimension at least three and whose values tend to
zero, the iterates converge. A nonconvergent zero-value-limit trajectory would refute it.
Stated without proof (status `OPEN`). -/
def ZeroValueIterateQuestion : Prop :=
  ∀ (n m : ℕ) (a : Fin m → Vec n) (F : Vec n → ℝ),
    (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) →
    ¬ Tendsto F (cocompact (Vec n)) atTop →
    ∀ R : AdmissibleBFGSRun n F,
      3 ≤ Module.finrank ℝ (Submodule.span ℝ {v | ∃ᶠ k in atTop, R.g k = v}) →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) →
      ∃ xstar, Tendsto R.x atTop (𝓝 xstar)

/-! ### Section 7.2: notation and BFGS identities (lines 23-28, 176-229) -/

/-- Item `C/07_H/prose/003` (`companion/chapters/07_H.tex:24-28`): "The accepted steps satisfy
fixed Armijo and weak Wolfe inequalities. Accepted iterates are differentiable; the inverse
matrices are positive definite; no damping, restarts, smoothing, spectral safeguards, or
particular line-search implementation is imposed." Every admissible run has fixed constants
$0<c_1<c_2<1$ with Armijo and weak Wolfe at every step, $F$ is differentiable at every
accepted iterate, every $H_k$ is positive definite (only $H_0\succ0$ is assumed), and
$H_{k+1}$ is exactly the inverse-BFGS update of $H_k$ (no modification of the update). -/
theorem run_setting {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1) ∧
      (∀ k, F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (R.g k) (R.displacement k) ∧
        dot (R.g (k + 1)) (R.displacement k) ≥ R.c₂ * dot (R.g k) (R.displacement k)) ∧
      (∀ k, DifferentiableAt ℝ F (R.x k)) ∧ (∀ k, (R.H k).PosDef) ∧
      ∀ k, R.H (k + 1) = inverseBFGS (R.H k) (R.displacement k) (R.gradientChange k) :=
  ⟨⟨R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩, fun k => ⟨R.armijo k, R.weak_wolfe k⟩,
    fun k => (R.hasGradient k).differentiableAt, R.positive_definite, R.update⟩

/-- Item `C/07_H/disp/008` (`companion/chapters/07_H.tex:171-178`): the notation
\[ g_k=\nabla f(x_k),\ p_k=-H_kg_k,\ s_k=\alpha_kp_k,\ x_{k+1}=x_k+s_k,\ y_k=g_{k+1}-g_k,\
   B_k=H_k^{-1},\ q_k=g_k^\top H_kg_k>0,\ d_k=-g_k^\top s_k=\alpha_kq_k>0,\ t_k=y_k^\top s_k,\
   \Delta_k=f(x_k)-f(x_{k+1}). \]
The display defines notation and asserts $g_k=\nabla f(x_k)$, $x_{k+1}=x_k+s_k$, $q_k>0$,
$d_k=-g_k^Ts_k=\alpha_kq_k>0$. In Lean $s_k,y_k,B_k,q_k,d_k,t_k$ are `R.displacement k`,
`R.gradientChange k`, `R.hessian k`, `R.q k`, `R.d k` (defined as $\alpha_kq_k$),
`R.curvature k`; $p_k$ is the variable `p` with its defining equation; $\Delta_k$ is written
out. -/
theorem notation_display {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ)
    (p : Vec n) (hp : p = -(R.H k *ᵥ R.g k)) :
    HasFDerivAt F (gradientFunctional (R.g k)) (R.x k) ∧ R.displacement k = R.α k • p ∧
      R.x (k + 1) = R.x k + R.displacement k ∧ R.gradientChange k = R.g (k + 1) - R.g k ∧
      R.hessian k = (R.H k)⁻¹ ∧ R.q k = dot (R.g k) (R.H k *ᵥ R.g k) ∧ 0 < R.q k ∧
      R.d k = -dot (R.g k) (R.displacement k) ∧
      -dot (R.g k) (R.displacement k) = R.α k * R.q k ∧ 0 < R.d k ∧
      R.curvature k = dot (R.gradientChange k) (R.displacement k) := by
  have h : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
  refine ⟨R.hasGradient k, ?_, R.step k, rfl, rfl, rfl, R.q_pos k, by rw [h, neg_neg],
    by rw [h, neg_neg]; rfl, R.d_pos k, rfl⟩
  rw [hp, smul_neg]
  exact neg_smul _ _

/-- Item `C/07_H/disp/009` (`companion/chapters/07_H.tex:182-187`): the line-search
conditions
\[ f(x_{k+1})\le f(x_k)+c_1g_k^\top s_k,\qquad g_{k+1}^\top s_k\ge c_2g_k^\top s_k,\qquad
   0<c_1<c_2<1, \]
satisfied at every step of every admissible run, with fixed constants. -/
theorem line_search_conditions {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (∀ k, F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (R.g k) (R.displacement k) ∧
        dot (R.g (k + 1)) (R.displacement k) ≥ R.c₂ * dot (R.g k) (R.displacement k)) ∧
      0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1 :=
  ⟨fun k => ⟨R.armijo k, R.weak_wolfe k⟩, R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩

/-- Item `C/07_H/disp/010` (`companion/chapters/07_H.tex:191-196`): "In particular, with
$c=1-c_2>0$,
\[ t_k\ge c\,d_k>0,\qquad \beta_k:=\frac{t_k}{d_k}=-\frac{y_k^\top H_kg_k}{q_k}\ge c." \]
$c$ and $\beta_k$ are variables with their defining equations; the second equality says that
$\beta_k$ is the library's `R.beta k`. -/
theorem curvature_and_beta {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ)
    (c : ℝ) (hc : c = 1 - R.c₂) (β : ℝ) (hβ : β = R.curvature k / R.d k) :
    0 < c ∧ R.curvature k ≥ c * R.d k ∧ c * R.d k > 0 ∧
      β = -dot (R.gradientChange k) (R.H k *ᵥ R.g k) / R.q k ∧ β ≥ c := by
  have hd := R.d_pos k
  have hc0 : 0 < c := hc ▸ R.wolfe_constant_pos
  have ht : R.curvature k = R.beta k * R.d k := R.toFullBFGSRun.curvature_eq_beta_mul_d k
  have hβeq : β = R.beta k := by rw [hβ, ht, mul_div_assoc, div_self hd.ne', mul_one]
  refine ⟨hc0, ?_, mul_pos hc0 hd, by rw [hβeq]; rfl, ?_⟩
  · rw [hc]
    exact R.curvature_lower_bound k
  · rw [hβeq, hc]
    exact R.beta_lower_bound k

/-- Item `C/07_H/disp/011` (`companion/chapters/07_H.tex:200-206`): the full inverse-BFGS
update
\[ H_{k+1}=\Bigl(I-\frac{s_ky_k^\top}{t_k}\Bigr)H_k\Bigl(I-\frac{y_ks_k^\top}{t_k}\Bigr)
   +\frac{s_ks_k^\top}{t_k}. \]
(`(R.curvature k)⁻¹` is Lean's total inverse; $t_k>0$ by `curvature_and_beta`.) -/
theorem inverse_update {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.H (k + 1) = (1 - (R.curvature k)⁻¹ • outer (R.displacement k) (R.gradientChange k)) *
        R.H k * (1 - (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.displacement k)) +
      (R.curvature k)⁻¹ • outer (R.displacement k) (R.displacement k) :=
  R.update k

/-- Item `C/07_H/disp/012` (`companion/chapters/07_H.tex:210-214`), equation (7.2.1): "Its
Hessian form, after substituting $s_k=-\alpha_kH_kg_k$, is
\[ B_{k+1}=B_k-\frac{g_kg_k^\top}{q_k}+\frac{y_ky_k^\top}{t_k}." \] -/
theorem hessian_form {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.hessian (k + 1) = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
      (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) :=
  R.hessian_update k

/-- Item `C/07_H/prose/020` (`companion/chapters/07_H.tex:216-217`): "A zero gradient
corresponds to a stationary termination rather than an infinite strict-descent run." For
finite convex $F$, a point with zero gradient is a global minimizer (stationary: no point has a
smaller value), and the BFGS step from it is zero for every matrix and length, so the
iteration stops there. -/
theorem zero_gradient_stationary {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (x : Vec n)
    (hx : HasFDerivAt F (gradientFunctional 0) x) :
    (∀ z, F x ≤ F z) ∧ ∀ (H : Mat n) (α : ℝ), x + bfgsStep H 0 α = x := by
  refine ⟨fun z => ?_, fun H α => by simp [bfgsStep]⟩
  have h := convex_supporting_inequality hF hx z
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  linarith

/-- Item `C/07_H/prose/021` (`companion/chapters/07_H.tex:217-219`): "Throughout, ``infinite
admissible'' therefore includes nonzero accepted gradients and well-defined positive-curvature
updates." Every admissible run has $g_k\ne0$ and $t_k>0$ for all $k$. -/
theorem admissible_convention {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    ∀ k, R.g k ≠ 0 ∧ 0 < R.curvature k :=
  fun k => ⟨R.gradient_nonzero k, R.curvature_pos k⟩

/-! ### Section 7.5.1: bounded subgradients and Euler's identity (lines 252-272) -/

/-- Item `C/07_H/disp/013` (`companion/chapters/07_H.tex:248-250`): "For finite convex
positively homogeneous $f$, every subgradient $g\in\partial f(x)$ satisfies
\[ g^\top x=f(x),\qquad g^\top z\le f(z)\quad\text{for every }z." \]
A subgradient at $x$ is a $g$ with $F(z)\ge F(x)+g^T(z-x)$ for all $z$. Library:
`Homogeneous.supporting_euler`, `Homogeneous.supporting_linear_le`. -/
theorem euler_identity {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (x g : Vec n)
    (hg : ∀ z, F x + dot g (z - x) ≤ F z) :
    dot g x = F x ∧ ∀ z, dot g z ≤ F z := by
  have hs : Homogeneous.Supports F x g := fun z => by linarith [hg z]
  exact ⟨Homogeneous.supporting_euler hhom hs, Homogeneous.supporting_linear_le hhom hs⟩

/-- Item `C/07_H/prose/023` (`companion/chapters/07_H.tex:254-255`): "In particular, all
subgradients belong to $\partial f(0)$." For finite convex positively homogeneous $F$, every
subgradient at any point $x$ is a subgradient at $0$. -/
theorem subgradients_at_zero {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (x g : Vec n)
    (hg : ∀ z, F x + dot g (z - x) ≤ F z) : ∀ z, F 0 + dot g (z - 0) ≤ F z := by
  have hs : Homogeneous.Supports F x g := fun z => by linarith [hg z]
  intro z
  have h := Homogeneous.supports_at_zero hhom hs z
  linarith

/-- Item `C/07_H/disp/014` (`companion/chapters/07_H.tex:256-258`), with the claims of line
265: "In positive dimension, the unit sphere is nonempty and $f$ is finite and continuous
there, so
\[ \|g\|\le\max_{\|z\|=1}f(z)<\infty." \]
For $n\ge1$ and finite convex positively homogeneous $F$: the Euclidean unit sphere is
nonempty, $F$ is continuous, $F$ attains a (finite) maximum $M$ on the sphere, and every
subgradient $g$ at every point satisfies $\|g\|\le M$ (Euclidean norm). -/
theorem subgradient_sphere_bound {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hhom : Homogeneous.PositiveDegreeOne F) :
    {z : Vec n | ‖euclideanVector z‖ = 1}.Nonempty ∧ Continuous F ∧
      ∃ M : ℝ, IsGreatest (F '' {z : Vec n | ‖euclideanVector z‖ = 1}) M ∧
        ∀ x g : Vec n, (∀ z, F x + dot g (z - x) ≤ F z) → ‖euclideanVector g‖ ≤ M := by
  have hne := BfgsCoverage.Article.Global.unit_sphere_nonempty hn
  have hc := convex_continuous hF
  obtain ⟨z₀, hz₀, hmax⟩ :=
    BfgsCoverage.Article.Global.unit_sphere_compact.exists_isMaxOn hne hc.continuousOn
  refine ⟨hne, hc, F z₀, ⟨⟨z₀, hz₀, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hmax hz
  · intro x g hg
    have hs : Homogeneous.Supports F x g := fun z => by linarith [hg z]
    by_cases hg0 : g = 0
    · subst hg0
      have h1 := Homogeneous.supporting_linear_le hhom hs z₀
      simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h1
      rw [BfgsCoverage.Article.Global.norm_euclideanVector]
      simpa [sqNorm] using h1
    · have h := Homogeneous.supporting_unit_direction hhom x g hs hg0
      dsimp only at h
      exact h.2.trans (hmax h.1)

/-- Item `C/07_H/prose/025` (`companion/chapters/07_H.tex:259`): "In dimension zero the
space is a singleton and every gradient is zero; boundedness and the later bounded-sublevel or
coercive convergence conclusions hold directly. [...] an infinite admissible run with nonzero
gradients cannot occur in dimension zero." In $\R^0$ every vector is $0$ (so every gradient is
zero), every sublevel is bounded, every sequence converges to $0$, and no admissible run
exists. (Theorem 7.A, `theorem_7A`, is stated for every dimension, so it holds in dimension
zero vacuously.) -/
theorem dimension_zero (F : Vec 0 → ℝ) :
    (∀ x : Vec 0, x = 0) ∧ (∀ x g : Vec 0, HasFDerivAt F (gradientFunctional g) x → g = 0) ∧
      (∀ c : ℝ, Bornology.IsBounded {x | F x ≤ c}) ∧ (∀ x : ℕ → Vec 0, Tendsto x atTop (𝓝 0)) ∧
      IsEmpty (AdmissibleBFGSRun 0 F) := by
  have h0 : ∀ x : Vec 0, x = 0 := fun x => funext fun i => i.elim0
  refine ⟨h0, fun _ g _ => h0 g, fun c => ?_, fun x => ?_, ⟨fun R => ?_⟩⟩
  · exact (Bornology.isBounded_singleton (x := (0 : Vec 0))).subset (fun x _ => h0 x)
  · have hx : x = fun _ => 0 := funext fun k => h0 (x k)
    rw [hx]
    exact tendsto_const_nhds
  · exact absurd R.dimension_pos (lt_irrefl 0)

/-- Item `C/07_H/prose/026` (`companion/chapters/07_H.tex:261-262`): "Thus the bounded-gradient
assumption in Theorem M:average is automatic, even for an infinite-piece sublinear
function." For every finite convex positively homogeneous $F$ (no finite-piece assumption;
for instance the Euclidean norm, which is not a finite maximum of linear forms,
`BfgsCoverage.Article.Global.euclidean_norm_not_maxLinear`), every admissible run has bounded
gradients ($\|g_k\|\le\Lambda$, Euclidean norm), so the conclusion of Theorem `M:average`
(the article's Theorem `art:reciprocal-growth`, `BfgsCoverage.Article.Energy.reciprocal_growth`)
holds whenever $d_k\to0$. -/
theorem bounded_gradients_automatic {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) :
    (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧
      (Tendsto R.d atTop (𝓝 0) →
        Tendsto (fun N : ℕ => (∏ k ∈ Finset.range N, (R.q k)⁻¹) ^ (1 / (N : ℝ))) atTop atTop ∧
        Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop) := by
  obtain ⟨G, hG, hg⟩ := R.homogeneous_global_gradient_bound hhom
  have hb : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ :=
    ⟨G, fun k => BfgsCoverage.Article.Global.norm_le_of_sqNorm_le hG.le (hg k)⟩
  exact ⟨hb, fun hd => BfgsCoverage.Article.Energy.reciprocal_growth R hb hd⟩

/-! ### Section 7.5.2: the exact energy identity (lines 278-332)

Standing assumptions: `F` finite, convex and positively homogeneous of degree one, `R` an
admissible run; $f_k$ is written `F (R.x k)`. The pairings $h_k,\ell_k$, the constant
$\gamma$ and the potential $\Phi_k$ are variables with their defining equations. -/

/-- Item `C/07_H/disp/015` (`companion/chapters/07_H.tex:273-276`): "Set $f_k=f(x_k)$ and
\[ h_k=y_k^\top x_{k+1}=d_k-\Delta_k,\qquad \ell_k=-y_k^\top x_k." \]
The display defines $h_k,\ell_k$ and asserts $y_k^Tx_{k+1}=d_k-\Delta_k$ (library
`AdmissibleBFGSRun.homogeneous_new_pairing`); $\ell_k$ enters `pairings_nonneg`. -/
theorem new_pairing {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F)
    (h : ℕ → ℝ) (hh : ∀ k, h k = dot (R.gradientChange k) (R.x (k + 1))) (k : ℕ) :
    h k = R.d k - (F (R.x k) - F (R.x (k + 1))) := by
  rw [hh]
  exact R.homogeneous_new_pairing hhom k

/-- Item `C/07_H/prose/027` (`companion/chapters/07_H.tex:278-279`): "Convexity and homogeneity
give $h_k,\ell_k\ge0$ and $t_k=h_k+\ell_k$." -/
theorem pairings_nonneg {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F)
    (h ℓ : ℕ → ℝ) (hh : ∀ k, h k = dot (R.gradientChange k) (R.x (k + 1)))
    (hℓ : ∀ k, ℓ k = -dot (R.gradientChange k) (R.x k)) (k : ℕ) :
    0 ≤ h k ∧ 0 ≤ ℓ k ∧ R.curvature k = h k + ℓ k := by
  rw [hh, hℓ]
  exact ⟨R.homogeneous_new_pairing_nonneg hhom k,
    by linarith [R.homogeneous_old_pairing_nonpos hhom k], R.homogeneous_curvature_pairings k⟩

/-- Item `C/07_H/disp/016` (`companion/chapters/07_H.tex:281-283`): "Armijo and convexity give
\[ c_1d_k\le\Delta_k\le d_k." \] -/
theorem decrease_sandwich {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (_hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.c₁ * R.d k ≤ F (R.x k) - F (R.x (k + 1)) ∧ F (R.x k) - F (R.x (k + 1)) ≤ R.d k :=
  R.homogeneous_decrease_sandwich k

/-- Item `C/07_H/disp/017` (`companion/chapters/07_H.tex:287-293`), equation (7.5.1):
"Expanding (7.2.1) at $x_{k+1}=x_k-\alpha_kH_kg_k$ yields
\[ x_{k+1}^\top B_{k+1}x_{k+1}=x_k^\top B_kx_k-\frac{f_k^2}{q_k}+\frac{h_k^2}{t_k}." \]
(7.2.1) is the Hessian form, `hessian_form`.

Also Item `C/07_H/prose/028` (`companion/chapters/07_H.tex:285`), the lead-in, corrected on 15
October 2026 (M17; before "Expanding (2.1) at", with (2.1) an unrelated equation of Chapter 2):
"Expanding (7.2.1) at $x_{k+1}=x_k-\alpha_kH_kg_k$ yields". Library:
`AdmissibleBFGSRun.homogeneous_energy_identity`. -/
theorem energy_identity {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F)
    (h : ℕ → ℝ) (hh : ∀ k, h k = dot (R.gradientChange k) (R.x (k + 1))) (k : ℕ) :
    dot (R.x (k + 1)) (R.hessian (k + 1) *ᵥ R.x (k + 1)) =
      dot (R.x k) (R.hessian k *ᵥ R.x k) - F (R.x k) ^ 2 / R.q k + h k ^ 2 / R.curvature k := by
  have he := R.homogeneous_energy_identity hhom k
  simp only [AdmissibleBFGSRun.referenceEnergy, AdmissibleBFGSRun.referenceCorrection, sub_zero,
    metricEnergy] at he
  rw [hh]
  exact he

/-- Item `C/07_H/disp/018` (`companion/chapters/07_H.tex:298-302`), with the claim of lines
305-306: "The explicit terms involving $\alpha_k$ cancel because $g_k^\top x_k=f_k$:
\[ -2\alpha_k f_k+\alpha_k^2q_k-\frac{(f_k-\alpha_kq_k)^2}{q_k}=-\frac{f_k^2}{q_k}." \]
Stated with the explicit terms: Euler's identity $g_k^Tx_k=f_k$; the expansion
$x_{k+1}^TB_kx_{k+1}=x_k^TB_kx_k-2\alpha_kf_k+\alpha_k^2q_k$; the new pairing
$g_k^Tx_{k+1}=f_k-\alpha_kq_k$ (whose square over $q_k$ is the subtracted term of the Hessian
form); and the displayed cancellation. -/
theorem alpha_terms_cancel {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (k : ℕ) :
    dot (R.g k) (R.x k) = F (R.x k) ∧
      dot (R.x (k + 1)) (R.hessian k *ᵥ R.x (k + 1)) =
        dot (R.x k) (R.hessian k *ᵥ R.x k) - 2 * R.α k * F (R.x k) + R.α k ^ 2 * R.q k ∧
      dot (R.g k) (R.x (k + 1)) = F (R.x k) - R.α k * R.q k ∧
      -2 * R.α k * F (R.x k) + R.α k ^ 2 * R.q k - (F (R.x k) - R.α k * R.q k) ^ 2 / R.q k =
        -(F (R.x k) ^ 2 / R.q k) := by
  have heul := R.homogeneous_euler hhom k
  have hpd := R.positive_definite k
  have hsym : (R.hessian k).IsSymm :=
    BfgsCoverage.Article.Energy.isSymm_of_posDef (R.hessian_posDef k)
  have hBs : R.hessian k *ᵥ R.displacement k = -R.α k • R.g k := by
    change (R.H k)⁻¹ *ᵥ (-R.α k • (R.H k *ᵥ R.g k)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hpd.det_pos.ne'.isUnit, Matrix.one_mulVec]
  have hcomm : ∀ u v : Vec n, dot u (R.hessian k *ᵥ v) = dot v (R.hessian k *ᵥ u) := by
    intro u v
    change u ⬝ᵥ (R.hessian k *ᵥ v) = v ⬝ᵥ (R.hessian k *ᵥ u)
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym.eq, dotProduct_comm]
  have hgs : dot (R.g k) (R.displacement k) = -(R.α k * R.q k) := R.dot_step_eq_neg_d k
  have hq := (R.q_pos k).ne'
  refine ⟨heul, ?_, ?_, by field_simp; ring⟩
  · rw [R.step k]
    change dot (R.x k + R.displacement k) (R.hessian k *ᵥ (R.x k + R.displacement k)) = _
    have e1 : dot (R.x k + R.displacement k) (R.hessian k *ᵥ (R.x k + R.displacement k)) =
        dot (R.x k) (R.hessian k *ᵥ R.x k) + dot (R.displacement k) (R.hessian k *ᵥ R.x k) +
          (dot (R.x k) (R.hessian k *ᵥ R.displacement k) +
            dot (R.displacement k) (R.hessian k *ᵥ R.displacement k)) := by
      simp only [dot, Matrix.mulVec_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, hcomm (R.displacement k) (R.x k), hBs]
    have e2 : dot (R.x k) (-R.α k • R.g k) = -R.α k * F (R.x k) := by
      rw [dot_smul_right, show dot (R.x k) (R.g k) = dot (R.g k) (R.x k) from
        dotProduct_comm _ _, heul]
    have e3 : dot (R.displacement k) (-R.α k • R.g k) = R.α k ^ 2 * R.q k := by
      rw [dot_smul_right, show dot (R.displacement k) (R.g k) = dot (R.g k) (R.displacement k) from
        dotProduct_comm _ _, hgs]
      ring
    rw [e2, e3]
    ring
  · rw [R.homogeneous_old_endpoint_pairing hhom k]
    rfl

/-- Item `C/07_H/disp/019` (`companion/chapters/07_H.tex:306-309`): "Also,
\[ \frac{h_k^2}{t_k}\le h_k=d_k-\Delta_k\le\frac{1-c_1}{c_1}\Delta_k." \] -/
theorem correction_bounds {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F)
    (h : ℕ → ℝ) (hh : ∀ k, h k = dot (R.gradientChange k) (R.x (k + 1))) (k : ℕ) :
    h k ^ 2 / R.curvature k ≤ h k ∧ h k = R.d k - (F (R.x k) - F (R.x (k + 1))) ∧
      R.d k - (F (R.x k) - F (R.x (k + 1))) ≤
        (1 - R.c₁) / R.c₁ * (F (R.x k) - F (R.x (k + 1))) := by
  have hnn := R.homogeneous_new_pairing_nonneg hhom k
  have hle := R.homogeneous_pairing_le_curvature hhom k
  have ht : 0 < R.curvature k := R.curvature_pos k
  have heq := R.homogeneous_new_pairing hhom k
  have hc := R.c₁_pos
  have harm := R.armijo_decrease k
  refine ⟨?_, by rw [hh]; exact heq, ?_⟩
  · rw [hh, div_le_iff₀ ht]
    nlinarith [mul_nonneg hnn (sub_nonneg.mpr hle)]
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith

/-- Item `C/07_H/disp/020` (`companion/chapters/07_H.tex:313-318`), equation (7.5.2):
"Consequently, with $\gamma=(1-c_1)/c_1$,
\[ \Phi_k=x_k^\top B_kx_k+\gamma f_k,\qquad \Phi_{k+1}\le\Phi_k-\frac{f_k^2}{q_k}." \]
$\gamma$ and $\Phi$ are variables with their defining equations; $\Phi$ is the library's
`AdmissibleBFGSRun.homogeneousPotential` (`homogeneous_potential_step`). -/
theorem potential_step {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F)
    (γ : ℝ) (hγ : γ = (1 - R.c₁) / R.c₁) (Φ : ℕ → ℝ)
    (hΦ : ∀ k, Φ k = dot (R.x k) (R.hessian k *ᵥ R.x k) + γ * F (R.x k)) (k : ℕ) :
    Φ (k + 1) ≤ Φ k - F (R.x k) ^ 2 / R.q k := by
  have h := R.homogeneous_potential_step hhom k
  simp only [AdmissibleBFGSRun.homogeneousPotential, AdmissibleBFGSRun.referenceEnergy, sub_zero,
    metricEnergy] at h
  rw [hΦ, hΦ, hγ]
  exact h

/-- The potential $\Phi_k=x_k^TB_kx_k+\gamma f_k$, $\gamma=(1-c_1)/c_1$, is the library's
`AdmissibleBFGSRun.homogeneousPotential`. -/
theorem potential_eq {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (γ : ℝ) (hγ : γ = (1 - R.c₁) / R.c₁) (Φ : ℕ → ℝ)
    (hΦ : ∀ k, Φ k = dot (R.x k) (R.hessian k *ᵥ R.x k) + γ * F (R.x k)) (k : ℕ) :
    Φ k = R.homogeneousPotential k := by
  rw [hΦ, hγ]
  simp only [AdmissibleBFGSRun.homogeneousPotential, AdmissibleBFGSRun.referenceEnergy, sub_zero,
    metricEnergy]

/-! ### Section 7.5.3: every finite value limit is zero (lines 338-378)

Lines 341-376 are the proof of Theorem 7.A. Its displays are stated under the hypotheses of
Theorem 7.A and the finite limit `L` of the values ("In the latter case", line 344), with
$\gamma,\Phi$ as in display `C/07_H/disp/020` and $M$ (line 363) as variables with their
defining equations. The undisplayed steps are stated as `values_dichotomy` (lines 341-342),
`q_not_bounded_away` (line 350), `potential_lower_bound` (lines 350-351),
`reciprocal_summable_of_weighted` (lines 357-358), `bounded_away_of_pointwise` (lines 374-375)
and `finite_limit_zero` (line 375); the last three are general forms, since the standing
assumptions together with $L\ne0$ are inconsistent (that is the theorem). -/

/-- Proof of Theorem 7.A, lines 341-342 (not a register item): "Armijo gives strictly decreasing
values. Either they tend to $-\infty$ or they have a finite limit $L$." -/
theorem values_dichotomy {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    StrictAnti (fun k => F (R.x k)) ∧
      (Tendsto (fun k => F (R.x k)) atTop atBot ∨
        ∃ L : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) :=
  ⟨strictAnti_nat_of_succ_lt R.objective_strict_decrease, tendsto_of_antitone R.objective_antitone⟩

/-- Item `C/07_H/disp/021` (`companion/chapters/07_H.tex:336-338`), in the proof of Theorem
7.A: "In the latter case,
\[ \sum_kd_k\le\frac{f_0-L}{c_1}<\infty." \] -/
theorem predicted_decrease_budget {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (_hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) :
    Summable R.d ∧ ∑' k, R.d k ≤ (F (R.x 0) - L) / R.c₁ := by
  have hlow : ∀ k, L ≤ F (R.x k) := R.objective_antitone.le_of_tendsto hL
  refine ⟨R.summable_predicted_decreases_of_lower_bound L hlow, ?_⟩
  simpa using R.tail_budget_le L hlow 0

/-- Proof of Theorem 7.A, line 350 (not a register item): "so $d_k\to0$ and
Theorem~\ref{M:average} gives $\liminf q_k=0$." With a finite limit of the values: $d_k\to0$
and, for every $\varepsilon>0$, $q_k<\varepsilon$ for infinitely many $k$ (as $q_k>0$, this is
$\liminf q_k=0$). -/
theorem q_not_bounded_away {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) :
    Tendsto R.d atTop (𝓝 0) ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, R.q k < ε := by
  have hd : Tendsto R.d atTop (𝓝 0) :=
    (R.summable_predicted_decreases_of_value_limit L hL).tendsto_atTop_zero
  refine ⟨hd, fun ε hε => ?_⟩
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hcon
  let Q := R.shift J
  obtain ⟨G, hG, hg⟩ := Q.homogeneous_global_gradient_bound hhom
  have hb : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (Q.g k)‖ ≤ Λ :=
    ⟨G, fun k => BfgsCoverage.Article.Global.norm_le_of_sqNorm_le hG.le (hg k)⟩
  have hmean := (BfgsCoverage.Article.Energy.reciprocal_growth Q hb
    (R.shift_d_tendsto_zero hd J)).2
  obtain ⟨N, hN1, hN⟩ := ((eventually_ge_atTop 1).and
    (hmean.eventually (eventually_gt_atTop (1 / ε)))).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hterm : ∀ k ∈ Finset.range N, (Q.q k)⁻¹ ≤ 1 / ε := by
    intro k _
    have hk : ε ≤ Q.q k := not_lt.mp (hJ (J + k) (Nat.le_add_right J k))
    rw [one_div]
    exact inv_anti₀ hε hk
  have hsum : ∑ k ∈ Finset.range N, (Q.q k)⁻¹ ≤ N * (1 / ε) := by
    have h := Finset.sum_le_sum hterm
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hle : 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (Q.q k)⁻¹ ≤ 1 / ε := by
    rw [one_div, inv_mul_le_iff₀ hNpos]
    linarith
  linarith

/-- Proof of Theorem 7.A, lines 350-351 (not a register item): "On the other hand,
$\Phi_k\ge\gamma L$." -/
theorem potential_lower_bound {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (_hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L))
    (γ : ℝ) (hγ : γ = (1 - R.c₁) / R.c₁) (Φ : ℕ → ℝ)
    (hΦ : ∀ k, Φ k = dot (R.x k) (R.hessian k *ᵥ R.x k) + γ * F (R.x k)) (k : ℕ) :
    Φ k ≥ γ * L := by
  have hlow : ∀ k, L ≤ F (R.x k) := R.objective_antitone.le_of_tendsto hL
  have hγ0 : 0 ≤ γ := by
    rw [hγ]
    exact div_nonneg (sub_nonneg.mpr (R.c₁_lt_c₂.trans R.c₂_lt_one).le) R.c₁_pos.le
  have hE := R.referenceEnergy_nonneg 0 k
  simp only [AdmissibleBFGSRun.referenceEnergy, sub_zero, metricEnergy] at hE
  rw [hΦ]
  nlinarith [mul_le_mul_of_nonneg_left (hlow k) hγ0]

/-- Item `C/07_H/disp/022` (`companion/chapters/07_H.tex:343-345`), in the proof of Theorem
7.A: "On the other hand, $\Phi_k\ge\gamma L$, and telescoping (7.5.2) gives
\[ \sum_k\frac{f_k^2}{q_k}<\infty." \]
Stated as summability, with the telescoped bound $\sum_kf_k^2/q_k\le\Phi_0-\gamma L$. (The
companion prints "telescoping (7.5.2)", `potential_step`, since the correction M17 of 15 October
2026; before "(5.2)", item `C/07_H/prose/028`.) -/
theorem weighted_sum_finite {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L))
    (γ : ℝ) (hγ : γ = (1 - R.c₁) / R.c₁) (Φ : ℕ → ℝ)
    (hΦ : ∀ k, Φ k = dot (R.x k) (R.hessian k *ᵥ R.x k) + γ * F (R.x k)) :
    Summable (fun k => F (R.x k) ^ 2 / R.q k) ∧
      ∑' k, F (R.x k) ^ 2 / R.q k ≤ Φ 0 - γ * L := by
  have hlow : ∀ k, L ≤ F (R.x k) := R.objective_antitone.le_of_tendsto hL
  refine ⟨R.homogeneous_weighted_summable hhom L hlow, ?_⟩
  rw [potential_eq R γ hγ Φ hΦ 0, hγ]
  exact R.homogeneous_weighted_tsum_budget hhom L hlow

/-- Proof of Theorem 7.A, lines 357-358 (not a register item), general form: "If $L\ne0$, this
would imply $\sum_k1/q_k<\infty$ and therefore $q_k\to\infty$." For positive $q_k$ and $f_k\to
L\ne0$, $\sum_kf_k^2/q_k<\infty$ implies $\sum_kq_k^{-1}<\infty$ and $q_k\to\infty$. -/
theorem reciprocal_summable_of_weighted (f q : ℕ → ℝ) (hq : ∀ k, 0 < q k) (L : ℝ) (hL0 : L ≠ 0)
    (hf : Tendsto f atTop (𝓝 L)) (hs : Summable (fun k => f k ^ 2 / q k)) :
    Summable (fun k => (q k)⁻¹) ∧ Tendsto q atTop atTop := by
  have habs : 0 < |L| := abs_pos.mpr hL0
  have hev : ∀ᶠ k in atTop, |L| / 2 ≤ |f k| :=
    (hf.abs.eventually (lt_mem_nhds (by linarith : |L| / 2 < |L|))).mono (fun _ h => h.le)
  have hc : 0 < (|L| / 2) ^ 2 := by positivity
  have hsum : Summable (fun k => (q k)⁻¹) := by
    have hs' : Summable (fun k => ((|L| / 2) ^ 2)⁻¹ * (f k ^ 2 / q k)) := hs.mul_left _
    refine Summable.of_norm_bounded_eventually_nat _ hs' ?_
    filter_upwards [hev] with k hk
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hq k))]
    have hk2 : (|L| / 2) ^ 2 ≤ f k ^ 2 := by
      rw [← sq_abs (f k)]
      exact pow_le_pow_left₀ (by positivity) hk 2
    rw [inv_mul_eq_div, div_div, le_div_iff₀ (mul_pos (hq k) hc),
      inv_mul_cancel_left₀ (hq k).ne']
    exact hk2
  refine ⟨hsum, ?_⟩
  have h0 : Tendsto (fun k => (q k)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsum.tendsto_atTop_zero,
      Eventually.of_forall fun k => inv_pos.mpr (hq k)⟩
  refine h0.inv_tendsto_nhdsGT_zero.congr (fun k => ?_)
  simp only [Pi.inv_apply, inv_inv]

/-- Item `C/07_H/disp/023` (`companion/chapters/07_H.tex:352-354`), in the proof of Theorem
7.A: "There is also a direct pointwise argument. The potential bounds
\[ x_k^\top B_kx_k\le\Phi_0-\gamma L=:M<\infty." \]
$M$ is the variable with its defining equation (it is a real number, so $M<\infty$). -/
theorem energy_bound {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L))
    (γ : ℝ) (hγ : γ = (1 - R.c₁) / R.c₁) (Φ : ℕ → ℝ)
    (hΦ : ∀ k, Φ k = dot (R.x k) (R.hessian k *ᵥ R.x k) + γ * F (R.x k))
    (M : ℝ) (hM : M = Φ 0 - γ * L) :
    ∀ k, dot (R.x k) (R.hessian k *ᵥ R.x k) ≤ M := by
  have hlow : ∀ k, L ≤ F (R.x k) := R.objective_antitone.le_of_tendsto hL
  intro k
  have h := R.homogeneous_energy_bound_of_lower_bound hhom L hlow k
  simp only [AdmissibleBFGSRun.referenceEnergy, sub_zero, metricEnergy] at h
  rw [hM, potential_eq R γ hγ Φ hΦ 0, hγ]
  exact h

/-- Item `C/07_H/disp/024` (`companion/chapters/07_H.tex:358-362`), in the proof of Theorem
7.A: "Metric Cauchy--Schwarz and Euler's identity imply
\[ f_k^2=(g_k^\top x_k)^2\le(g_k^\top H_kg_k)(x_k^\top B_kx_k)\le Mq_k." \] -/
theorem value_sq_bound {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L))
    (γ : ℝ) (hγ : γ = (1 - R.c₁) / R.c₁) (Φ : ℕ → ℝ)
    (hΦ : ∀ k, Φ k = dot (R.x k) (R.hessian k *ᵥ R.x k) + γ * F (R.x k))
    (M : ℝ) (hM : M = Φ 0 - γ * L) (k : ℕ) :
    F (R.x k) ^ 2 = dot (R.g k) (R.x k) ^ 2 ∧
      dot (R.g k) (R.x k) ^ 2 ≤ dot (R.g k) (R.H k *ᵥ R.g k) * dot (R.x k) (R.hessian k *ᵥ R.x k) ∧
      dot (R.g k) (R.H k *ᵥ R.g k) * dot (R.x k) (R.hessian k *ᵥ R.x k) ≤ M * R.q k := by
  have heul := R.homogeneous_euler hhom k
  have hcs := R.homogeneous_value_sq_le_energy_mul_q hhom k
  simp only [AdmissibleBFGSRun.referenceEnergy, sub_zero, metricEnergy] at hcs
  have hEM := energy_bound hF hhom R L hL γ hγ Φ hΦ M hM k
  have hq : dot (R.g k) (R.H k *ᵥ R.g k) = R.q k := rfl
  refine ⟨by rw [heul], ?_, ?_⟩
  · rw [heul, hq, mul_comm]
    exact hcs
  · rw [hq, mul_comm]
    exact mul_le_mul_of_nonneg_right hEM (R.q_pos k).le

/-- Proof of Theorem 7.A, lines 374-375 (not a register item), general form: "A finite nonzero
limit would thus force $q_k$ to be bounded away from zero." If $q_k>0$, $f_k^2\le Mq_k$ for all
$k$ and $f_k\to L\ne0$, then $q_k\ge\varepsilon$ for some $\varepsilon>0$ and all large $k$. -/
theorem bounded_away_of_pointwise (f q : ℕ → ℝ) (hq : ∀ k, 0 < q k) (M : ℝ)
    (hfq : ∀ k, f k ^ 2 ≤ M * q k) (L : ℝ) (hL0 : L ≠ 0) (hf : Tendsto f atTop (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ε ≤ q k := by
  have habs : 0 < |L| := abs_pos.mpr hL0
  have hev : ∀ᶠ k in atTop, |L| / 2 ≤ |f k| :=
    (hf.abs.eventually (lt_mem_nhds (by linarith : |L| / 2 < |L|))).mono (fun _ h => h.le)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hev
  have hc : 0 < (|L| / 2) ^ 2 := by positivity
  have hsq : ∀ k, J ≤ k → (|L| / 2) ^ 2 ≤ f k ^ 2 := fun k hk => by
    rw [← sq_abs (f k)]
    exact pow_le_pow_left₀ (by positivity) (hJ k hk) 2
  have hMq : (|L| / 2) ^ 2 ≤ M * q J := (hsq J le_rfl).trans (hfq J)
  have hM : 0 < M := by
    by_contra hM
    push_neg at hM
    nlinarith [hq J]
  refine ⟨(|L| / 2) ^ 2 / M, div_pos hc hM, eventually_atTop.mpr ⟨J, fun k hk => ?_⟩⟩
  rw [div_le_iff₀ hM, mul_comm]
  exact (hsq k hk).trans (hfq k)

/-- Proof of Theorem 7.A, line 375 (not a register item): "Hence $L=0$." Library:
`AdmissibleBFGSRun.homogeneous_finite_value_limit_zero`. -/
theorem finite_limit_zero {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) : L = 0 :=
  R.homogeneous_finite_value_limit_zero hhom L hL

/-- The tail energy budget behind the alternative arrangement of line 378: if
$|f_k|\ge c\ge0$ for $k\ge J$, then summing the energy identity (7.5.1) from $J$ gives
$c^2\sum_{k<N}q_{J+k}^{-1}\le x_J^TB_Jx_J+\sum_{k<N}h_{J+k}^2/t_{J+k}$. -/
theorem tail_energy_bound {n : ℕ} {F : Vec n → ℝ} (hhom : Homogeneous.PositiveDegreeOne F)
    (R : AdmissibleBFGSRun n F) (J : ℕ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ k, J ≤ k → c ≤ |F (R.x k)|) (N : ℕ) :
    c ^ 2 * ∑ k ∈ Finset.range N, (R.q (J + k))⁻¹ ≤
      dot (R.x J) (R.hessian J *ᵥ R.x J) +
        ∑ k ∈ Finset.range N,
          dot (R.gradientChange (J + k)) (R.x (J + k + 1)) ^ 2 / R.curvature (J + k) := by
  have hstep : ∀ N : ℕ, c ^ 2 * ∑ k ∈ Finset.range N, (R.q (J + k))⁻¹ +
      R.referenceEnergy 0 (J + N) ≤
        R.referenceEnergy 0 J + ∑ k ∈ Finset.range N, R.referenceCorrection 0 (J + k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, show J + (N + 1) = J + N + 1 by omega,
        R.homogeneous_energy_identity hhom (J + N)]
      have hq := R.q_pos (J + N)
      have hf2 : c ^ 2 ≤ F (R.x (J + N)) ^ 2 := by
        rw [← sq_abs (F (R.x (J + N)))]
        exact pow_le_pow_left₀ hc0 (hc (J + N) (Nat.le_add_right J N)) 2
      have hdiv : c ^ 2 * (R.q (J + N))⁻¹ ≤ F (R.x (J + N)) ^ 2 / R.q (J + N) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hf2 (inv_pos.mpr hq).le
      nlinarith
  have h := hstep N
  have hE := R.referenceEnergy_nonneg 0 (J + N)
  simp only [AdmissibleBFGSRun.referenceEnergy, AdmissibleBFGSRun.referenceCorrection, sub_zero,
    metricEnergy] at h hE
  linarith

/-- Item `C/07_H/prose/032` (`companion/chapters/07_H.tex:368`), the mathematics of the
paragraph on the formal finite-value theorem: "If $L\ne0$, shift to a tail with
$|f_k|\ge|L|/2$. The actual homogeneous corrections are nonnegative and bounded by $d_k$, so
they are summable. Chapter~\ref{comp:M} gives divergent reciprocal sums, and the energy identity
would bound $(|L|/2)^2\sum q_k^{-1}$ by the initial tail energy plus a finite correction sum, a
contradiction." Under the hypotheses of Theorem 7.A with a finite limit $L$: the corrections
$h_k^2/t_k$ lie in $[0,d_k]$ and are summable; $\sum_{k<N}q_k^{-1}\to\infty$; if $L\ne0$ a
tail $k\ge J$ with $|f_k|\ge|L|/2$ exists; on such a tail
$(|L|/2)^2\sum_{k<N}q_{J+k}^{-1}\le x_J^TB_Jx_J+\sum_{k<N}h_{J+k}^2/t_{J+k}$; hence $L=0$. -/
theorem alternative_arrangement {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) :
    (∀ k, 0 ≤ dot (R.gradientChange k) (R.x (k + 1)) ^ 2 / R.curvature k ∧
        dot (R.gradientChange k) (R.x (k + 1)) ^ 2 / R.curvature k ≤ R.d k) ∧
      Summable (fun k => dot (R.gradientChange k) (R.x (k + 1)) ^ 2 / R.curvature k) ∧
      Tendsto (fun N => ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop ∧
      (L ≠ 0 → ∃ J : ℕ, ∀ k, J ≤ k → |L| / 2 ≤ |F (R.x k)|) ∧
      (∀ J : ℕ, (∀ k, J ≤ k → |L| / 2 ≤ |F (R.x k)|) → ∀ N : ℕ,
        (|L| / 2) ^ 2 * ∑ k ∈ Finset.range N, (R.q (J + k))⁻¹ ≤
          dot (R.x J) (R.hessian J *ᵥ R.x J) +
            ∑ k ∈ Finset.range N,
              dot (R.gradientChange (J + k)) (R.x (J + k + 1)) ^ 2 / R.curvature (J + k)) ∧
      L = 0 := by
  have hcorr : ∀ k, R.referenceCorrection 0 k =
      dot (R.gradientChange k) (R.x (k + 1)) ^ 2 / R.curvature k := fun k => by
    simp only [AdmissibleBFGSRun.referenceCorrection, sub_zero]
  obtain ⟨G, hG, hg⟩ := R.homogeneous_global_gradient_bound hhom
  have hgrowth := objectiveGrowth_of_value_limit R G L hG hg hL
  refine ⟨fun k => ⟨?_, ?_⟩, ?_, EnergyBudget.tendsto_atTop_of_superquadratic hgrowth.2.2.2,
    fun hL0 => ?_, fun J hJ N => tail_energy_bound hhom R J (|L| / 2) (by positivity) hJ N,
    R.homogeneous_finite_value_limit_zero hhom L hL⟩
  · rw [← hcorr]
    exact R.referenceCorrection_nonneg 0 k
  · rw [← hcorr]
    exact R.homogeneous_referenceCorrection_le_d hhom k
  · have h := R.homogeneous_corrections_summable hhom hgrowth.1
    exact h.congr hcorr
  · have habs : 0 < |L| := abs_pos.mpr hL0
    have hev : ∀ᶠ k in atTop, |L| / 2 ≤ |F (R.x k)| :=
      (hL.abs.eventually (lt_mem_nhds (by linarith : |L| / 2 < |L|))).mono (fun _ h => h.le)
    exact eventually_atTop.mp hev

/-! ### Section 7.5.4: bounded-below and coercive consequences (lines 384-399) -/

/-- Item `C/07_H/prose/034` (`companion/chapters/07_H.tex:378-381`): "A positively homogeneous
function bounded below cannot take a negative value: otherwise $f(tx)=tf(x)\to-\infty$. Thus its
minimum value is zero, attained at the origin, and Theorem 7.A gives unconditional objective
convergence." For positively homogeneous $F$ (no convexity needed for the first claims): a
negative value $F(x)<0$ gives $F(tx)\to-\infty$ as $t\to\infty$; if $F$ is bounded below, then
$F\ge0$, its least value is $0=F(0)$, and every admissible run (on the then convex $F$) has
$F(x_k)\to0$. -/
theorem bounded_below_nonneg {n : ℕ} {F : Vec n → ℝ} (hhom : Homogeneous.PositiveDegreeOne F)
    (hbdd : ∃ L : ℝ, ∀ x, L ≤ F x) :
    (∀ x, F x < 0 → Tendsto (fun t : ℝ => F (t • x)) atTop atBot) ∧ (∀ x, 0 ≤ F x) ∧
      IsLeast (Set.range F) 0 ∧ F 0 = 0 ∧
      ∀ R : AdmissibleBFGSRun n F, Tendsto (fun k => F (R.x k)) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := hbdd
  have hnn := Homogeneous.nonneg_of_bounded_below hhom L hL
  refine ⟨fun x hx => ?_, hnn, ⟨⟨0, Homogeneous.value_zero hhom⟩, ?_⟩,
    Homogeneous.value_zero hhom, fun R => (R.homogeneous_bounded_below_convergence hhom L hL).2.2⟩
  · have h := tendsto_id.atTop_mul_const_of_neg hx
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hhom t ht x).symm
  · rintro _ ⟨x, rfl⟩
    exact hnn x

/-- Item `C/07_H/prose/035` (`companion/chapters/07_H.tex:383-385`): "If its sublevels are
bounded, then $f(x)>0$ for $x\ne0$. Compactness of the unit sphere gives $f(x)\ge\mu\|x\|$ for
some $\mu>0$, so $f_k\to0$ forces $x_k\to0$." For finite convex positively homogeneous $F$
with bounded sublevels: $F>0$ off zero; $F(x)\ge\mu\|x\|$ (Euclidean norm) for some $\mu>0$;
every sequence with $F(x_k)\to0$ tends to $0$; in particular every admissible run has
$x_k\to0$. -/
theorem bounded_sublevels_iterates {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hb : ∀ c : ℝ, Bornology.IsBounded {x | F x ≤ c}) :
    (∀ x, x ≠ 0 → 0 < F x) ∧ (∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖euclideanVector x‖ ≤ F x) ∧
      (∀ x : ℕ → Vec n, Tendsto (fun k => F (x k)) atTop (𝓝 0) → Tendsto x atTop (𝓝 0)) ∧
      ∀ R : AdmissibleBFGSRun n F, Tendsto R.x atTop (𝓝 0) := by
  have hpos : ∀ x, x ≠ 0 → 0 < F x := fun x hx =>
    Homogeneous.positive_of_bounded_zero_sublevel hhom (hb 0) hx
  obtain ⟨μ, hμ, hlow⟩ := Homogeneous.positive_homogeneous_euclidean_lower_bound hF hhom hpos
  exact ⟨hpos, ⟨μ, hμ, hlow⟩, fun x hx => BfgsCoverage.Article.Global.iterates_of_values hμ hlow hx,
    fun R => R.homogeneous_iterates_zero_of_bounded_zero_sublevel hhom (hb 0)⟩

/-! ### Section 7.6: Lemma 7.3 and the proof of Theorem 7.B (lines 413-449)

Lemma 7.3 needs neither homogeneity nor convexity, so it is stated for explicit sequences
`x H g α` and an arbitrary `F : Vec n → ℝ` (not an `AdmissibleBFGSRun`, whose fields include
convexity): $H_0\succ0$, $\alpha_k>0$, nonzero gradients $g_k=\nabla F(x_k)$, the step
$x_{k+1}=x_k+s_k$ with $s_k=-\alpha_kH_kg_k$ (`bfgsStep (H k) (g k) (α k)`, definitionally
`-α k • (H k *ᵥ g k)`), the inverse-BFGS update, and Armijo and weak Wolfe with fixed
$0<c_1<c_2<1$. -/

/-- The matrix run (`FullBFGSRun`) of the data of Lemma 7.3; positive definiteness of every
$H_k$, $q_k>0$ and $t_k>0$ follow from $H_0\succ0$, $g_k\ne0$, $\alpha_k>0$, weak Wolfe and the
update (`fullBFGS_positive_invariants`). -/
def lemmaRun {n : ℕ} (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ) (c₂ : ℝ) (hc₂ : c₂ < 1)
    (hH0 : (H 0).PosDef) (hα : ∀ k, 0 < α k) (hg : ∀ k, g k ≠ 0)
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k))
    (hwolfe : ∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
      c₂ * dot (g k) (bfgsStep (H k) (g k) (α k))) : FullBFGSRun n where
  H := H
  g := g
  α := α
  positive_definite k := (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hwolfe hupd k).1
  alpha_pos := hα
  energy_pos k := (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hwolfe hupd k).2.1
  curvature_pos k := (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hwolfe hupd k).2.2
  update := hupd

/-- Item `C/07_H/heading/004` (`companion/chapters/07_H.tex:405`), Lemma 7.3 (lines 416-419):
"Suppose a full-BFGS run satisfies Armijo--weak-Wolfe, has a finite gradient alphabet, and has
objective values bounded below along the run. Let $G$ be the recurrent gradients. Then
$0\in\operatorname{aff}G$."
No convexity or homogeneity of `F` is assumed (lines 441-442). The finite alphabet is
`(Set.range g).Finite`; "bounded below along the run" is $\exists L\ \forall k\ L\le F(x_k)$;
$G$ is the variable with its defining equation. `_hgrad` ($g_k=\nabla F(x_k)$), `_hstep` and
`_hc₁₂` are part of the run but not used. Proof along the paper's (lines 421-439): Armijo gives
$\sum d_k<\infty$, the library's `FullBFGSRun.zero_mem_recurrent_affineSpan` does the rest
(Theorem `M:average` as `reciprocalGrowth`, the common vector and the energy step). -/
theorem lemma_7_3 {n : ℕ} (F : Vec n → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n) (g : ℕ → Vec n)
    (α : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hH0 : (H 0).PosDef) (hα : ∀ k, 0 < α k) (hg : ∀ k, g k ≠ 0)
    (_hgrad : ∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k))
    (_hstep : ∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k))
    (harmijo : ∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hwolfe : ∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
      c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hfinite : (Set.range g).Finite) (hbdd : ∃ L : ℝ, ∀ k, L ≤ F (x k))
    (G : Set (Vec n)) (hG : G = {v | ∃ᶠ k in atTop, g k = v}) :
    (0 : Vec n) ∈ affineSpan ℝ G := by
  obtain ⟨L, hL⟩ := hbdd
  let Rf := lemmaRun H g α c₂ hc₂ hH0 hα hg hupd hwolfe
  have hdec : ∀ k, c₁ * Rf.d k ≤ F (x k) - F (x (k + 1)) := by
    intro k
    have h := harmijo k
    rw [dot_bfgsStep] at h
    change c₁ * (α k * metricEnergy (H k) (g k)) ≤ _
    linarith
  have hsum := DescentBudget.armijo_summable (f := fun k => F (x k)) hc₁
    (fun k => (mul_pos (hα k) (Rf.energy_pos k)).le) hdec hL
  rw [hG]
  exact Rf.zero_mem_recurrent_affineSpan hfinite (1 - c₂) (sub_pos.mpr hc₂)
    (fun k => Rf.beta_ge_of_weakWolfe k c₂ (hwolfe k)) hsum.tendsto_atTop_zero

/-- General form of display `C/07_H/disp/025` (lines 428-430): for every nonempty set $G$ with
$0\notin\operatorname{aff}G$, some $v$ has $v^Tg=1$ for all $g\in G$. (Library:
`Homogeneous.common_component_of_zero_not_mem_affineSpan`.) -/
theorem common_vector_general {n : ℕ} (G : Set (Vec n)) (hne : G.Nonempty)
    (h0 : (0 : Vec n) ∉ affineSpan ℝ G) : ∃ v : Vec n, ∀ g ∈ G, dot v g = 1 :=
  Homogeneous.common_component_of_zero_not_mem_affineSpan hne h0

/-- Item `C/07_H/disp/025` (`companion/chapters/07_H.tex:417-419`), in the proof of Lemma 7.3:
"Discard a finite prefix so that all remaining gradients belong to $G$. If
$0\notin\operatorname{aff}G$, a vector $v$ exists with
\[ v^\top g=1\quad(g\in G)." \]
Under the standing assumptions of the proof: the hypotheses of Lemma 7.3, a prefix $J$ after
which all gradients lie in $G$ (line 425), and the assumption $0\notin\operatorname{aff}G$ of
the proof by contradiction. These assumptions are jointly inconsistent (that is Lemma 7.3); the
proof uses only the general form `common_vector_general`, whose assumptions are satisfiable. -/
theorem common_vector {n : ℕ} (F : Vec n → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n) (g : ℕ → Vec n)
    (α : ℕ → ℝ) (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (_hH0 : (H 0).PosDef) (_hα : ∀ k, 0 < α k) (_hg : ∀ k, g k ≠ 0)
    (_hgrad : ∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k))
    (_hstep : ∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k))
    (_hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k))
    (_harmijo : ∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (_hwolfe : ∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
      c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hfinite : (Set.range g).Finite) (_hbdd : ∃ L : ℝ, ∀ k, L ≤ F (x k))
    (G : Set (Vec n)) (hG : G = {v | ∃ᶠ k in atTop, g k = v})
    (J : ℕ) (_hJ : ∀ k, J ≤ k → g k ∈ G) (h0 : (0 : Vec n) ∉ affineSpan ℝ G) :
    ∃ v : Vec n, ∀ g' ∈ G, dot v g' = 1 := by
  have hne : G.Nonempty := by
    rw [hG]
    exact Homogeneous.recurrentValues_nonempty g hfinite
  exact common_vector_general G hne h0

/-- General form of display `C/07_H/disp/026` (lines 434-436) for one update: for $H\succ0$,
$g\ne0$, $\alpha>0$, $s=-\alpha Hg$, $y=g'-g$ with $y^Ts>0$, and $v$ with $v^Tg=v^Tg'=1$:
$v^Ty=0$ and $v^TH_+^{-1}v=v^TH^{-1}v-1/q$, $q=g^THg$, where $H_+$ is the inverse-BFGS update
(library: `FullBFGSRun.common_component_energy_step`). -/
theorem common_vector_energy_step_general {n : ℕ} (H : Mat n) (hH : H.PosDef) (g g' : Vec n)
    (hg : g ≠ 0) (α : ℝ) (hα : 0 < α) (ht : 0 < dot (g' - g) (bfgsStep H g α)) (v : Vec n)
    (hv : dot v g = 1) (hv' : dot v g' = 1) :
    dot v (g' - g) = 0 ∧
      dot v ((inverseBFGS H (bfgsStep H g α) (g' - g))⁻¹ *ᵥ v) =
        dot v (H⁻¹ *ᵥ v) - 1 / dot g (H *ᵥ g) := by
  have hy : dot v (g' - g) = 0 := by
    change v ⬝ᵥ (g' - g) = 0
    rw [dotProduct_sub]
    change dot v g' - dot v g = 0
    rw [hv, hv', sub_self]
  refine ⟨hy, ?_⟩
  have hvg : dot g v = 1 := (dotProduct_comm g v).trans hv
  have hyv : dot (g' - g) v = 0 := (dotProduct_comm _ _).trans hy
  change metricEnergy _ v = metricEnergy H⁻¹ v - 1 / metricEnergy H g
  rw [hessianUpdate hH hg _ hα ht, EnergyIdentities.energy_add_matrix,
    EnergyIdentities.energy_sub_matrix, EnergyIdentities.energy_smul_matrix,
    EnergyIdentities.energy_smul_matrix, EnergyIdentities.energy_outer,
    EnergyIdentities.energy_outer, hvg, hyv]
  ring

/-- Item `C/07_H/disp/026` (`companion/chapters/07_H.tex:423-425`), in the proof of Lemma 7.3:
"In particular $v^\top y_k=0$. Equation (7.2.1) then implies
\[ v^\top B_{k+1}v=v^\top B_kv-\frac1{q_k}." \]
Under the standing assumptions of `common_vector` and the vector $v$ of display
`C/07_H/disp/025`: for $k\ge J$, $v^Ty_k=0$ and $v^TB_{k+1}v=v^TB_kv-1/q_k$ ($B_k=H_k^{-1}$).
(7.2.1) printed "(2.1)" before the correction M17 of 15 October 2026 (item `C/07_H/prose/028`).
The assumptions
are jointly inconsistent; the proof uses only the general form
`common_vector_energy_step_general`, whose assumptions are satisfiable. -/
theorem common_vector_energy_step {n : ℕ} (F : Vec n → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (g : ℕ → Vec n) (α : ℕ → ℝ) (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hH0 : (H 0).PosDef) (hα : ∀ k, 0 < α k) (hg : ∀ k, g k ≠ 0)
    (_hgrad : ∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k))
    (_hstep : ∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k))
    (_harmijo : ∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hwolfe : ∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
      c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (_hfinite : (Set.range g).Finite) (_hbdd : ∃ L : ℝ, ∀ k, L ≤ F (x k))
    (G : Set (Vec n)) (_hG : G = {v | ∃ᶠ k in atTop, g k = v})
    (J : ℕ) (hJ : ∀ k, J ≤ k → g k ∈ G) (_h0 : (0 : Vec n) ∉ affineSpan ℝ G)
    (v : Vec n) (hv : ∀ g' ∈ G, dot v g' = 1) (k : ℕ) (hk : J ≤ k) :
    dot v (g (k + 1) - g k) = 0 ∧
      dot v ((H (k + 1))⁻¹ *ᵥ v) = dot v ((H k)⁻¹ *ᵥ v) - 1 / dot (g k) (H k *ᵥ g k) := by
  have hinv := fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hwolfe hupd k
  rw [hupd k]
  exact common_vector_energy_step_general (H k) hinv.1 (g k) (g (k + 1)) (hg k) (α k) (hα k)
    hinv.2.2 v (hv _ (hJ k hk)) (hv _ (hJ (k + 1) (by omega)))

/-- Item `C/07_H/prose/040` (`companion/chapters/07_H.tex:431-433`): "It is a necessary
condition for any finite-gradient, finite-value-limit trajectory under these BFGS and
line-search assumptions." Under the assumptions of Lemma 7.3 with a finite limit of the
values $F(x_k)$ in place of the lower bound: $0\in\operatorname{aff}G$. -/
theorem lemma_7_3_value_limit {n : ℕ} (F : Vec n → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (g : ℕ → Vec n) (α : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hH0 : (H 0).PosDef) (hα : ∀ k, 0 < α k) (hg : ∀ k, g k ≠ 0)
    (hgrad : ∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k))
    (hstep : ∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k))
    (harmijo : ∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hwolfe : ∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
      c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hfinite : (Set.range g).Finite) (hlim : ∃ L : ℝ, Tendsto (fun k => F (x k)) atTop (𝓝 L))
    (G : Set (Vec n)) (hG : G = {v | ∃ᶠ k in atTop, g k = v}) :
    (0 : Vec n) ∈ affineSpan ℝ G := by
  have hanti : Antitone (fun k => F (x k)) := antitone_nat_of_succ_le fun k => by
    have h := harmijo k
    rw [dot_bfgsStep] at h
    have hq := (fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hwolfe hupd k).2.1
    linarith [mul_pos hc₁ (mul_pos (hα k) hq)]
  obtain ⟨L, hL⟩ := hlim
  exact lemma_7_3 F x H g α c₁ c₂ hc₁ hc₁₂ hc₂ hH0 hα hg hgrad hstep hupd harmijo hwolfe hfinite
    ⟨L, hanti.le_of_tendsto hL⟩ G hG

/-- Proof of Theorem 7.B, line 446-447 (not a register item): "For max-linear objectives, if
$0\notin\operatorname{aff}\{a_i\}$, no recurrent subset can have an affine hull containing
zero." -/
theorem no_recurrent_subset {n m : ℕ} (a : Fin m → Vec n)
    (h0 : (0 : Vec n) ∉ affineSpan ℝ (Set.range a)) (G : Set (Vec n)) (hG : G ⊆ Set.range a) :
    (0 : Vec n) ∉ affineSpan ℝ G :=
  fun h => h0 (affineSpan_mono ℝ hG h)

/-! ### Section 7.6.1: connection to the two-piece paper (lines 455-482) -/

/-- Item `C/07_H/prose/042` (`companion/chapters/07_H.tex:448-449`): "The model $|u|+t$ has
gradients $(1,1)$ and $(-1,1)$, both with last component one." For $F(u,t)=|u|+t$ on $\R^2$:
the gradient is $(1,1)$ where $u>0$ and $(-1,1)$ where $u<0$, every gradient is one of these
two, and both have last component one. -/
theorem two_piece_gradients (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = |x 0| + x 1) :
    (∀ x : Vec 2, 0 < x 0 → HasFDerivAt F (gradientFunctional ![1, 1]) x) ∧
      (∀ x : Vec 2, x 0 < 0 → HasFDerivAt F (gradientFunctional ![-1, 1]) x) ∧
      (∀ x g : Vec 2, HasFDerivAt F (gradientFunctional g) x → g = ![1, 1] ∨ g = ![-1, 1]) ∧
      (![1, 1] : Vec 2) 1 = 1 ∧ (![-1, 1] : Vec 2) 1 = 1 := by
  have hF : F = TwoPieceBudget.objective := funext hF_def
  subst hF
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x g hg => ?_, rfl, rfl⟩
  · have hd := hasFDerivAt_coordinateGradient (TwoPieceBudget.differentiableAt_of_ne hx.ne')
    have he := supporting_vector_eq_gradient (TwoPieceBudget.support_positive hx.le) hd
    rw [← he] at hd
    exact hd
  · have hd := hasFDerivAt_coordinateGradient (TwoPieceBudget.differentiableAt_of_ne hx.ne)
    have he := supporting_vector_eq_gradient (TwoPieceBudget.support_negative hx.le) hd
    rw [← he] at hd
    exact hd
  · obtain ⟨hsq, hgeq, -, -⟩ := TwoPieceBudget.actual_gradient_shape hg
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · left
      rw [hgeq, h1]
      rfl
    · right
      rw [hgeq, h1]
      rfl

/-- Item `C/07_H/disp/027` (`companion/chapters/07_H.tex:451-453`): "The arbitrary-many-piece
model
\[ f(u,t)=t+\max_ib_i^\top u \]
has precisely the same common-component property": every gradient of
$F(u,t)=t+\max_ib_i^Tu$ ($t$ last) has last component one. -/
theorem tilt_model_gradients {n m : ℕ} (b : Fin m → Vec n) (F : Vec (n + 1) → ℝ)
    (hF_def : ∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) :
    ∀ x g : Vec (n + 1), HasFDerivAt F (gradientFunctional g) x → g (Fin.last n) = 1 :=
  (tilt_family_escape b F hF_def).1

/-- Item `C/07_H/prose/044` (`companion/chapters/07_H.tex:459-461`): "Xie--W\"achter proves
the stronger finite-termination conclusion for its two-piece model: a search direction exposing
unboundedness is reached after finitely many iterations." For the two-piece model
$F(u,t)=|u|+t$ (`TwoPieceBudget.objective`) and every $0<c_1<c_2<1$: a state is a point $x$, a
matrix $H\succ0$ and the gradient $g=\nabla F(x)$ (`TwoPieceBudget.State`); a step is an
accepted full-BFGS step (some $\alpha>0$ with $x_+=x-\alpha Hg$, the inverse-BFGS update,
Armijo and weak Wolfe, `TwoPieceBudget.Step`). Every run of accepted steps is finite: there is
no infinite sequence of states joined by steps (equivalently, the reversed step relation is well
founded); every state from which no accepted step exists exposes unboundedness along its search
direction, $F(x_T-tH_Tg_T)\to-\infty$ as $t\to\infty$; and from every state such a terminal
state is reached after finitely many steps. Together: every run reaches, after finitely many
iterations, a state whose search direction exposes unboundedness. Library:
`TwoPieceBudget.twoPieceTermination`, `TwoPieceBudget.terminal_direction_unbounded`; the
attribution to the literature is not checked. -/
theorem two_piece_finite_termination :
    (∀ x : Vec 2, TwoPieceBudget.objective x = |x 0| + x 1) ∧
      ConvexOn ℝ univ TwoPieceBudget.objective ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → c₂ < 1 →
        (¬ ∃ S : ℕ → TwoPieceBudget.State, ∀ k, TwoPieceBudget.Step c₁ c₂ (S k) (S (k + 1))) ∧
        WellFounded (fun T S => TwoPieceBudget.Step c₁ c₂ S T) ∧
        (∀ T : TwoPieceBudget.State,
          (¬ ∃ U : TwoPieceBudget.State, TwoPieceBudget.Step c₁ c₂ T U) →
            Tendsto (fun t : ℝ => TwoPieceBudget.objective (T.x + bfgsStep T.H T.g t))
              atTop atBot) ∧
        ∀ S : TwoPieceBudget.State, ∃ T : TwoPieceBudget.State,
          Relation.ReflTransGen (TwoPieceBudget.Step c₁ c₂) S T ∧
          (¬ ∃ U : TwoPieceBudget.State, TwoPieceBudget.Step c₁ c₂ T U) ∧
          Tendsto (fun t : ℝ => TwoPieceBudget.objective (T.x + bfgsStep T.H T.g t))
            atTop atBot := by
  obtain ⟨hconv, hall⟩ := TwoPieceBudget.twoPieceTermination
  refine ⟨fun _ => rfl, hconv, fun c₁ c₂ h1 h2 h3 => ?_⟩
  obtain ⟨hwf, hreach⟩ := hall c₁ c₂ h1 h2 h3
  exact ⟨fun ⟨S, hS⟩ => (WellFounded.wellFounded_iff_no_descending_seq.1 hwf).elim ⟨S, hS⟩, hwf,
    fun T hT => TwoPieceBudget.terminal_direction_unbounded h1 h2 h3 T hT, hreach⟩

/-! #### Objectives with no admissible run (non-vacuity of Theorem 7.B (ii) and of the family)

Theorem 7.B (ii) and the statements on $f(u,t)=t+\max_ib_i^Tu$ quantify over the admissible runs
of objectives whose slopes avoid $0$ affinely. On many of them no admissible run exists, so those
statements are vacuous there: linear objectives (`linear_objective_no_run`), and finite maxima
whose slopes lie on one affine line missing $0$, in every dimension (`maxLinear_line_no_run`, a
reduction to the two-piece model $|u|+t$, `TwoPieceBudget.no_infinite_independent_two_piece`).
Hence no admissible run exists for any objective of Theorem 7.B (ii) in dimension at most two
(`maxLinear_affine_free_no_run`), nor on the family when the $b_i$ lie on one line
(`tilt_collinear_no_run`), in particular with at most two distinct $b_i$ in every dimension
(`tilt_two_values_no_run`, `tilt_two_pieces_no_run`) and for every member in $\R^2$
(`tilt_plane_no_run`). Whether an admissible run exists when the slopes do not lie on one line (at
least three pieces, ambient dimension at least $3$) is not known (`TiltNoInfiniteRunQuestion`);
the text conditions every statement on infinite runs and does not claim that one exists. -/

/-- $(c+\beta d)^Tx=c^Tx+\beta\,d^Tx$. -/
theorem dot_add_smul {n : ℕ} (c d x : Vec n) (β : ℝ) :
    dot (c + β • d) x = dot c x + β * dot d x := by
  change (c + β • d) ⬝ᵥ x = c ⬝ᵥ x + β * (d ⬝ᵥ x)
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

/-- A linear objective $F(x)=w^Tx$ has no admissible run: its gradient is constant, while
consecutive gradients of an admissible run differ (`unchanged_gradient_fails_wolfe`). -/
theorem linear_objective_no_run {n : ℕ} (w : Vec n) (F : Vec n → ℝ) (hF : ∀ x, F x = dot w x) :
    IsEmpty (AdmissibleBFGSRun n F) := by
  refine ⟨fun R => ?_⟩
  have hfun : F = (gradientFunctional w : Vec n → ℝ) :=
    funext fun z => by rw [hF, gradientFunctional_apply]
  have hlin : ∀ x, HasFDerivAt F (gradientFunctional w) x := fun x => by
    rw [hfun]
    exact (gradientFunctional w).hasFDerivAt
  have hg : ∀ k, R.g k = w := fun k =>
    AffineProjection.gradientFunctional_injective ((R.hasGradient k).unique (hlin (R.x k)))
  exact R.gradient_transition_ne 0 (by rw [hg, hg])

/-- Item `C/07_H/prose/079` (`companion/chapters/07_H.tex:106-108`) explains this reduction (M42).

A finite max-linear objective whose slopes lie on one line $\{c+\beta d\}$ with $c,d$
linearly independent (an affine line missing $0$) has no admissible run. It is the maximum of the
two extreme slopes: linear when they coincide (`linear_objective_no_run`), otherwise
$|p^Tx|+q^Tx$ with $p=\frac{\beta_{\max}-\beta_{\min}}2d$, $q=c+\frac{\beta_{\max}+\beta_{\min}}2d$
linearly independent, a linear image of the two-piece model
(`TwoPieceBudget.no_infinite_independent_two_piece`). -/
theorem maxLinear_line_no_run {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (c d : Vec n) (β : Fin m → ℝ) (ha : ∀ i, a i = c + β i • d)
    (hcd : LinearIndependent ℝ ![c, d]) : IsEmpty (AdmissibleBFGSRun n F) := by
  obtain ⟨⟨i₀, -⟩, -⟩ := hF_def 0
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ β hne
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ β hne
  have hdot : ∀ i x, dot (a i) x = dot c x + β i * dot d x := fun i x => by
    rw [ha i, dot_add_smul]
  have hFx : ∀ x, F x = max (dot (a imin) x) (dot (a imax) x) := by
    intro x
    refine (hF_def x).unique ⟨?_, ?_⟩
    · rcases le_total (dot (a imin) x) (dot (a imax) x) with h | h
      · exact ⟨imax, (max_eq_right h).symm⟩
      · exact ⟨imin, (max_eq_left h).symm⟩
    · rintro _ ⟨i, rfl⟩
      change dot (a i) x ≤ max (dot (a imin) x) (dot (a imax) x)
      rw [hdot, hdot, hdot]
      rcases le_total 0 (dot d x) with h | h
      · have := mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ i)) h
        exact le_max_of_le_right (by linarith)
      · have := mul_le_mul_of_nonpos_right (hmin i (Finset.mem_univ i)) h
        exact le_max_of_le_left (by linarith)
  by_cases heq : β imin = β imax
  · have hall : ∀ i, a i = a imin := fun i => by
      have h1 := hmin i (Finset.mem_univ i)
      have h2 := hmax i (Finset.mem_univ i)
      rw [ha i, ha imin, show β i = β imin by linarith]
    refine linear_objective_no_run (a imin) F (fun x => ?_)
    rw [hFx, hall imax, max_self]
  · have hlt : β imin < β imax := lt_of_le_of_ne (hmin imax (Finset.mem_univ _)) heq
    set p : Vec n := ((β imax - β imin) / 2) • d with hp
    set q : Vec n := c + ((β imax + β imin) / 2) • d with hq
    have hFeq : F = fun x => |dot p x| + dot q x := by
      funext x
      rw [hFx, hdot, hdot, hp, hq, HomogeneousBlock.dot_smul_first, dot_add_smul]
      rcases le_total 0 (dot d x) with h | h
      · rw [max_eq_right (by nlinarith), abs_of_nonneg (by nlinarith)]
        ring
      · rw [max_eq_left (by nlinarith), abs_of_nonpos (by nlinarith)]
        ring
    have hind : LinearIndependent ℝ ![p, q] := by
      rw [LinearIndependent.pair_iff] at hcd ⊢
      intro s r hsr
      have hcomb : r • c + (s * ((β imax - β imin) / 2) + r * ((β imax + β imin) / 2)) • d =
          s • p + r • q := by
        rw [hp, hq]
        module
      obtain ⟨hr, hs'⟩ := hcd r _ (hcomb.trans hsr)
      refine ⟨?_, hr⟩
      rw [hr, zero_mul, add_zero] at hs'
      exact (mul_eq_zero.mp hs').resolve_right (by linarith)
    exact ⟨fun R =>
      TwoPieceBudget.no_infinite_independent_two_piece p q hind (R.congrObjective hFeq)⟩

/-- Item `C/07_H/prose/078` (`companion/chapters/07_H.tex:103-105`) now states this case (M42).

The common-tilt objective $f(u,t)=t+\max_ib_i^Tu$ ($t$ last) has no admissible run, in every
dimension, when its slopes $b_i$ lie on one line $\{c+\beta d\}$: the slopes $(b_i,1)$ of
the max-linear form then lie on the line through $(c,1)$ with direction $(d,0)$, which misses
$0$ (`maxLinear_line_no_run`; if $d=0$ the objective is linear). -/
theorem tilt_collinear_no_run {n m : ℕ} (b : Fin m → Vec n) (F : Vec (n + 1) → ℝ)
    (hF_def : ∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t)))
    (c d : Vec n) (β : Fin m → ℝ) (hb : ∀ i, b i = c + β i • d) :
    IsEmpty (AdmissibleBFGSRun (n + 1) F) := by
  have hmax := tilt_family b F hF_def
  by_cases hd : d = 0
  · have hbc : ∀ i, b i = c := fun i => by rw [hb i, hd, smul_zero, add_zero]
    refine linear_objective_no_run (Fin.snoc c 1) F (fun x => ?_)
    obtain ⟨⟨i, hi⟩, -⟩ := hmax x
    rw [← hi]
    change dot (Fin.snoc (b i) 1 : Vec (n + 1)) x = dot (Fin.snoc c 1 : Vec (n + 1)) x
    rw [hbc i]
  · have hsnoc : ∀ i, (Fin.snoc (b i) 1 : Vec (n + 1)) =
        (Fin.snoc c 1 : Vec (n + 1)) + β i • (Fin.snoc d 0 : Vec (n + 1)) := by
      intro i
      rw [hb i]
      ext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [Fin.snoc_last]
      · simp [Fin.snoc_castSucc]
    refine maxLinear_line_no_run (fun i => (Fin.snoc (b i) 1 : Vec (n + 1))) F hmax
      (Fin.snoc c 1) (Fin.snoc d 0) β hsnoc ?_
    rw [LinearIndependent.pair_iff]
    intro s r hsr
    have hlast := congrFun hsr (Fin.last n)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.snoc_last, Pi.zero_apply] at hlast
    have hs : s = 0 := by linarith
    refine ⟨hs, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (funext h)
    have h2 := congrFun hsr (Fin.castSucc j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.snoc_castSucc, Pi.zero_apply, hs,
      zero_mul, zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_right hj

/-- The common-tilt objective with two pieces $b_1,b_2$ (distinct or not),
$f(u,t)=t+\max(b_1^Tu,b_2^Tu)$, has no admissible run, in every dimension. -/
theorem tilt_two_pieces_no_run {n : ℕ} (b : Fin 2 → Vec n) (F : Vec (n + 1) → ℝ)
    (hF_def : ∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) :
    IsEmpty (AdmissibleBFGSRun (n + 1) F) :=
  tilt_collinear_no_run b F hF_def (b 0) (b 1 - b 0) ![0, 1] (fun i => by fin_cases i <;> simp)

/-- Item `C/07_H/prose/078` (`companion/chapters/07_H.tex:103-105`), the two-value subcase (M42).

The common-tilt objective whose slopes $b_i$ take at most two values (any number of pieces,
any dimension) has no admissible run. -/
theorem tilt_two_values_no_run {n m : ℕ} (b : Fin m → Vec n) (u₀ u₁ : Vec n)
    (hb : ∀ i, b i = u₀ ∨ b i = u₁) (F : Vec (n + 1) → ℝ)
    (hF_def : ∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) :
    IsEmpty (AdmissibleBFGSRun (n + 1) F) := by
  classical
  refine tilt_collinear_no_run b F hF_def u₀ (u₁ - u₀) (fun i => if b i = u₀ then 0 else 1)
    (fun i => ?_)
  by_cases h : b i = u₀
  · simp [h]
  · simp only [h, if_false, one_smul, add_sub_cancel]
    exact (hb i).resolve_left h

/-- Every common-tilt objective in the plane, $f(u,t)=t+\max_ib_iu$ with $u,b_i\in\R$ (any
number of pieces), has no admissible run: in dimension one all slopes lie on a line. -/
theorem tilt_plane_no_run {m : ℕ} (b : Fin m → Vec 1) (F : Vec 2 → ℝ)
    (hF_def : ∀ (u : Vec 1) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) :
    IsEmpty (AdmissibleBFGSRun 2 F) :=
  tilt_collinear_no_run b F hF_def 0 (fun _ => 1) (fun i => b i 0)
    (fun i => by ext j; fin_cases j; simp)

/-- In the plane, a vector orthogonal to $v\ne0$ is a multiple of $d=(-v_2,v_1)$. -/
theorem perp_eq_smul (v w : Vec 2) (hv : v ≠ 0) (hw : dot v w = 0) :
    w = (dot w ![-(v 1), v 0] / dot ![-(v 1), v 0] ![-(v 1), v 0]) • ![-(v 1), v 0] := by
  have hD : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    by_contra h
    push_neg at h
    apply hv
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply]; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Pi.zero_apply]; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hdd : dot ![-(v 1), v 0] ![-(v 1), v 0] = v 0 ^ 2 + v 1 ^ 2 := by
    simp [dot, Fin.sum_univ_two]
    ring
  have hwd : dot w ![-(v 1), v 0] = -(w 0 * v 1) + w 1 * v 0 := by
    simp [dot, Fin.sum_univ_two]
  have hw' : v 0 * w 0 + v 1 * w 1 = 0 := by simpa [dot, Fin.sum_univ_two] using hw
  rw [hdd, hwd]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
    linear_combination (v 0) * hw'
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_zero]
    rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
    linear_combination (v 1) * hw'

/-- Item `C/07_H/prose/077` (`companion/chapters/07_H.tex:101-103`) now states this case (M42).

In dimension at most two, a finite max-linear objective with
$0\notin\operatorname{aff}\{a_1,\dots,a_m\}$ (the hypothesis of Theorem 7.B (ii)) has no
admissible run: there is $v$ with $v^Ta_i=1$ for all $i$; in dimension one all slopes then
coincide (a linear objective), in dimension two they lie on the line $a_{i_0}+\R d$,
$d=(-v_2,v_1)$, which misses $0$ (`maxLinear_line_no_run`). So Theorem 7.B (ii) is vacuous in
dimension at most two. -/
theorem maxLinear_affine_free_no_run {n m : ℕ} (hn : n ≤ 2) (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (h0 : (0 : Vec n) ∉ affineSpan ℝ (Set.range a)) : IsEmpty (AdmissibleBFGSRun n F) := by
  obtain ⟨⟨i₀, -⟩, -⟩ := hF_def 0
  obtain ⟨v, hv⟩ := Homogeneous.common_component_of_zero_not_mem_affineSpan
    (⟨a i₀, i₀, rfl⟩ : (Set.range a).Nonempty) h0
  have hva : ∀ i, dot v (a i) = 1 := fun i => hv (a i) ⟨i, rfl⟩
  interval_cases n
  · exact ⟨fun R => absurd R.dimension_pos (lt_irrefl 0)⟩
  · have hall : ∀ i, a i = a i₀ := by
      intro i
      have h1 := hva i
      have h2 := hva i₀
      simp only [dot, Fin.sum_univ_one] at h1 h2
      have hv0 : v 0 ≠ 0 := by
        intro h
        rw [h, zero_mul] at h1
        norm_num at h1
      ext j
      fin_cases j
      exact mul_left_cancel₀ hv0 (h1.trans h2.symm)
    refine linear_objective_no_run (a i₀) F (fun x => (hF_def x).unique ⟨⟨i₀, rfl⟩, ?_⟩)
    rintro _ ⟨i, rfl⟩
    change dot (a i) x ≤ dot (a i₀) x
    rw [hall i]
  · have hv0 : v ≠ 0 := by
      intro h
      have := hva i₀
      rw [h] at this
      simp [dot] at this
    set d : Vec 2 := ![-(v 1), v 0] with hd
    refine maxLinear_line_no_run a F hF_def (a i₀) d
      (fun i => dot (a i - a i₀) d / dot d d) (fun i => ?_) ?_
    · have hperp : dot v (a i - a i₀) = 0 := by
        change v ⬝ᵥ (a i - a i₀) = 0
        rw [dotProduct_sub]
        change dot v (a i) - dot v (a i₀) = 0
        rw [hva, hva, sub_self]
      have h := perp_eq_smul v (a i - a i₀) hv0 hperp
      rw [← hd] at h
      rw [← h]
      abel
    · rw [LinearIndependent.pair_iff]
      intro s r hsr
      have hvd : dot v d = 0 := by
        simp [hd, dot, Fin.sum_univ_two]
        ring
      have h2 : dot v (s • a i₀ + r • d) = s * dot v (a i₀) + r * dot v d := by
        change v ⬝ᵥ (s • a i₀ + r • d) = s * (v ⬝ᵥ a i₀) + r * (v ⬝ᵥ d)
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      rw [hsr, hva, hvd] at h2
      have hz : dot v (0 : Vec 2) = 0 := by simp [dot]
      have hs : s = 0 := by linarith
      refine ⟨hs, ?_⟩
      rw [hs, zero_smul, zero_add] at hsr
      have hd0 : d ≠ 0 := by
        intro h
        apply hv0
        ext i
        fin_cases i
        · have := congrFun h 1
          simpa [hd] using this
        · have := congrFun h 0
          simpa [hd] using this
      exact (smul_eq_zero.mp hsr).resolve_right hd0

/-- Item `C/07_H/prose/045` (`companion/chapters/07_H.tex:461-463`), an open question: "The
argument here does \textbf{not} establish finite termination for the general many-piece family."
Finite termination of every run on every member of the family $f(u,t)=t+\max_ib_i^Tu$ ($t$ last)
implies that no infinite admissible run exists on it; the Prop states this part. Stated without
proof (status `OPEN`). It holds when the $b_i$ lie on one line (`tilt_collinear_no_run`; in
particular with at most two distinct pieces in every dimension, `tilt_two_values_no_run`, and for
every member in $\R^2$, `tilt_plane_no_run`); for $b_i$ not on one line (at least three pieces,
ambient dimension at least three) it is not known. Where it holds, the run statements about the
family (`tilt_family_escape`, and Theorem 7.B (ii) on these objectives) are vacuous.
Item `C/07_H/prose/080` (`companion/chapters/07_H.tex:109-110`) repeats the open case (M42). -/
def TiltNoInfiniteRunQuestion : Prop :=
  ∀ (n m : ℕ) (b : Fin m → Vec n) (F : Vec (n + 1) → ℝ),
    (∀ (u : Vec n) (t : ℝ),
      IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t))) →
    IsEmpty (AdmissibleBFGSRun (n + 1) F)

/-- $\operatorname{vectorSpan}$ (the span of the differences) lies in the span. -/
theorem vectorSpan_le_span {n : ℕ} (G : Set (Vec n)) : vectorSpan ℝ G ≤ Submodule.span ℝ G := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨u, hu, w, hw, rfl⟩
  exact Submodule.sub_mem _ (Submodule.subset_span hu) (Submodule.subset_span hw)

/-- Item `C/07_H/prose/047` (`companion/chapters/07_H.tex:465-468`): "If
$r=\dim\operatorname{span}G$, a finite-value-limit run needs at least $r+1$ distinct recurrent
gradients. Indeed, $0\in\operatorname{aff}G$ implies that the gradient differences span the same
$r$-dimensional space; $|G|-1$ differences must span it." Under the assumptions of Lemma 7.3
with a finite value limit (as in `lemma_7_3_value_limit`): $r+1\le|G|$ (`Set.ncard`; $G$ is
finite) and the span of the differences, `vectorSpan ℝ G`, equals $\operatorname{span}G$. -/
theorem recurrent_cardinality {n : ℕ} (F : Vec n → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (g : ℕ → Vec n) (α : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hH0 : (H 0).PosDef) (hα : ∀ k, 0 < α k) (hg : ∀ k, g k ≠ 0)
    (hgrad : ∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k))
    (hstep : ∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k))
    (hupd : ∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k))
    (harmijo : ∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hwolfe : ∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
      c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)))
    (hfinite : (Set.range g).Finite) (hlim : ∃ L : ℝ, Tendsto (fun k => F (x k)) atTop (𝓝 L))
    (G : Set (Vec n)) (hG : G = {v | ∃ᶠ k in atTop, g k = v})
    (r : ℕ) (hr : r = Module.finrank ℝ (Submodule.span ℝ G)) :
    r + 1 ≤ G.ncard ∧ vectorSpan ℝ G = Submodule.span ℝ G := by
  have h0 := lemma_7_3_value_limit F x H g α c₁ c₂ hc₁ hc₁₂ hc₂ hH0 hα hg hgrad hstep hupd
    harmijo hwolfe hfinite hlim G hG
  have hfin : G.Finite := by
    rw [hG]
    exact Homogeneous.recurrentValues_finite g hfinite
  have hne : G.Nonempty := by
    rw [hG]
    exact Homogeneous.recurrentValues_nonempty g hfinite
  rw [hr]
  exact ⟨Homogeneous.finrank_span_add_one_le_ncard hfin hne h0,
    le_antisymm (vectorSpan_le_span G) (Homogeneous.span_le_vectorSpan_of_affine_zero h0)⟩

/-- Item `C/07_H/prose/048` (`companion/chapters/07_H.tex:469-470`): "The three-gradient,
rank-two stagnation example of Chapter~\ref{comp:D} attains this lower bound." (since 15 October
2026, wording point W10; before "The earlier three-gradient, …": the example is the seed run of
Chapter 12, which comes later). For every pair
$0<c_1\le1/3$, $c_1<c_2<1$, the seed run `SeedOrbit.run` has values converging (to $0$), three
distinct recurrent gradients spanning a space of dimension two, so $r+1=|G|$. Library:
`SeedOrbit.sharpRecurrentCardinality`. -/
theorem seed_cardinality_sharp (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (G : Set (Vec 2))
    (hG : G = {v | ∃ᶠ k in atTop, (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).g k = v}) :
    Tendsto (fun k => SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD
        ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).x k)) atTop (𝓝 0) ∧
      G.ncard = 3 ∧ Module.finrank ℝ (Submodule.span ℝ G) = 2 ∧
      Module.finrank ℝ (Submodule.span ℝ G) + 1 = G.ncard := by
  have h := SeedOrbit.sharpRecurrentCardinality c₁ c₂ hc₁ hc₁' hc hc₂
  dsimp only at h
  obtain ⟨-, -, hv, -, -, hcard, hrank, heq⟩ := h
  subst hG
  exact ⟨hv, hcard, hrank, heq⟩

/-! ### Section 7.7.1: exact invariant subspace and lifting (lines 503-545)

Standing assumptions (the setting of Section 7.7 is a finite max-linear objective, `_hF_def`,
which the lifting does not use): an admissible run `R`, a matrix `U` with orthonormal columns
(`Uᵀ * U = 1`) spanning a subspace `S` (`hS`), and an index `K` after which every gradient lies
in `S` (`hK`). The hatted variables $\widehat x_k=U^Tx_k$, $\widehat H_k=U^TH_kU$,
$\widehat g_k=U^Tg_k$ are `xh`, `Hh`, `gh` with their defining equations. -/

/-- After $K$ every gradient is $g_k=U\widehat g_k$. -/
theorem grad_lift {n r : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) (S : Submodule ℝ (Vec n))
    (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ) (hK : ∀ k, K ≤ k → R.g k ∈ S) (k : ℕ)
    (hk : K ≤ k) : U *ᵥ (Uᵀ *ᵥ R.g k) = R.g k :=
  Homogeneous.orthonormal_projection_on_range U hU _ ((hS _).mp (hK k hk))

/-- Item `C/07_H/disp/028` (`companion/chapters/07_H.tex:497-501`): the definitions
\[ \widehat x_k=U^\top x_k,\qquad\widehat H_k=U^\top H_kU,\qquad\widehat g_k=U^\top g_k. \]
They enter the theorems below as variables with these defining equations. This theorem unfolds
the library's objects for them: `AffineProjection.compress Uᵀ H` is $U^THU$ (so
$\widehat H_k$ is `compress Uᵀ (R.H k)`), `AffineProjection.lift Uᵀ H` is $HU(U^THU)^{-1}$
(the $L_K$ of (7.7.1)) and `AffineProjection.fiberPoint Uᵀ H x 0` is
$x-HU(U^THU)^{-1}U^Tx$ (the limit (7.7.2)). -/
theorem hat_definitions {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (H : Mat n) (x : Vec n) :
    AffineProjection.compress Uᵀ H = Uᵀ * H * U ∧
      AffineProjection.lift Uᵀ H = H * U * (Uᵀ * H * U)⁻¹ ∧
      AffineProjection.fiberPoint Uᵀ H x 0 = x - (H * U * (Uᵀ * H * U)⁻¹ * Uᵀ) *ᵥ x := by
  have hc : AffineProjection.compress Uᵀ H = Uᵀ * H * U := by
    simp only [AffineProjection.compress, Matrix.transpose_transpose]
  have hl : AffineProjection.lift Uᵀ H = H * U * (Uᵀ * H * U)⁻¹ := by
    simp only [AffineProjection.lift, hc, Matrix.transpose_transpose]
  refine ⟨hc, hl, ?_⟩
  simp only [AffineProjection.fiberPoint, hl, zero_sub, Matrix.mulVec_neg, ← sub_eq_add_neg,
    Matrix.mulVec_mulVec]

/-- Item `C/07_H/prose/049` (`companion/chapters/07_H.tex:503-505`): "Projection of the
inverse-BFGS formula gives exactly the same inverse-BFGS update for the hatted variables and
projected steps. The scalars $q_k,d_k,t_k$ and the line-search inequalities are unchanged."
For $k\ge K$: $\widehat H_k\succ0$; the projected step is
$U^Ts_k=-\alpha_k\widehat H_k\widehat g_k$ and $\widehat x_{k+1}=\widehat x_k+U^Ts_k$;
$\widehat H_{k+1}$ is the inverse-BFGS update of $\widehat H_k$ with $U^Ts_k$ and
$\widehat y_k=\widehat g_{k+1}-\widehat g_k$; $\widehat g_k^T\widehat H_k\widehat g_k=q_k$,
$-\widehat g_k^TU^Ts_k=d_k$, $\widehat y_k^TU^Ts_k=t_k$; and Armijo and weak Wolfe hold in the
hatted variables (with the same values $f(x_k)$). -/
theorem projected_run {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (hK : ∀ k, K ≤ k → R.g k ∈ S) (xh : ℕ → Vec r) (hxh : ∀ k, xh k = Uᵀ *ᵥ R.x k)
    (Hh : ℕ → Mat r) (hHh : ∀ k, Hh k = Uᵀ * R.H k * U) (gh : ℕ → Vec r)
    (hgh : ∀ k, gh k = Uᵀ *ᵥ R.g k) (k : ℕ) (hk : K ≤ k) :
    (Hh k).PosDef ∧ Uᵀ *ᵥ R.displacement k = -R.α k • (Hh k *ᵥ gh k) ∧
      xh (k + 1) = xh k + Uᵀ *ᵥ R.displacement k ∧
      Hh (k + 1) = inverseBFGS (Hh k) (Uᵀ *ᵥ R.displacement k) (gh (k + 1) - gh k) ∧
      dot (gh k) (Hh k *ᵥ gh k) = R.q k ∧ -dot (gh k) (Uᵀ *ᵥ R.displacement k) = R.d k ∧
      dot (gh (k + 1) - gh k) (Uᵀ *ᵥ R.displacement k) = R.curvature k ∧
      F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (gh k) (Uᵀ *ᵥ R.displacement k) ∧
      dot (gh (k + 1)) (Uᵀ *ᵥ R.displacement k) ≥ R.c₂ * dot (gh k) (Uᵀ *ᵥ R.displacement k) := by
  have hrank := Homogeneous.orthonormal_transpose_fullRowRank U hU
  have hgk : (Uᵀ)ᵀ *ᵥ gh k = R.g k := by
    rw [Matrix.transpose_transpose, hgh]
    exact grad_lift R U hU S hS K hK k hk
  have hgk1 : (Uᵀ)ᵀ *ᵥ gh (k + 1) = R.g (k + 1) := by
    rw [Matrix.transpose_transpose, hgh]
    exact grad_lift R U hU S hS K hK (k + 1) (by omega)
  have hcomp : ∀ j, Hh j = AffineProjection.compress Uᵀ (R.H j) := fun j => by
    rw [hHh, (hat_definitions U (R.H j) 0).1]
  have hstep : Uᵀ *ᵥ R.displacement k = bfgsStep (Hh k) (gh k) (R.α k) := by
    change Uᵀ *ᵥ bfgsStep (R.H k) (R.g k) (R.α k) = _
    rw [← hgk, AffineProjection.project_step, ← hcomp]
  have hdot : ∀ u : Vec r, dot u (Uᵀ *ᵥ R.displacement k) = dot ((Uᵀ)ᵀ *ᵥ u) (R.displacement k) :=
    fun u => (AffineProjection.dot_transpose_mulVec Uᵀ u _).symm
  have hy : R.g (k + 1) - R.g k = (Uᵀ)ᵀ *ᵥ (gh (k + 1) - gh k) := by
    rw [Matrix.mulVec_sub, hgk, hgk1]
  refine ⟨?_, by rw [hstep]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcomp]
    exact AffineProjection.compress_posDef Uᵀ hrank (R.positive_definite k)
  · rw [hxh, hxh, R.step k, Matrix.mulVec_add]
    rfl
  · rw [hcomp, hcomp, R.update k, hy]
    exact AffineProjection.inverseBFGS_compress Uᵀ (R.H k) _ _
  · rw [hcomp]
    change metricEnergy (AffineProjection.compress Uᵀ (R.H k)) (gh k) = metricEnergy (R.H k) (R.g k)
    rw [← AffineProjection.project_energy, hgk]
  · have h : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
    rw [hdot, hgk, h, neg_neg]
  · rw [hdot, ← hy]
    rfl
  · rw [hdot, hgk]
    exact R.armijo k
  · rw [hdot, hdot, hgk, hgk1]
    exact R.weak_wolfe k

/-- Item `C/07_H/prose/050` (`companion/chapters/07_H.tex:507-511`): "Moreover, all subsequent
steps belong to the fixed subspace $H_KS$. [...] Induction proves the claim." For $k\ge K$:
$H_kS\subseteq H_KS$ and $s_k\in H_KS$ (elements of $H_KS$ are $H_KUz$). Library:
`AffineProjection.matrix_lift_invariant` (on the tail run from $K$). -/
theorem steps_in_fixed_subspace {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (hK : ∀ k, K ≤ k → R.g k ∈ S) (k : ℕ) (hk : K ≤ k) :
    (∀ z : Vec r, ∃ z' : Vec r, R.H k *ᵥ (U *ᵥ z) = R.H K *ᵥ (U *ᵥ z')) ∧
      ∃ z : Vec r, R.displacement k = R.H K *ᵥ (U *ᵥ z) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hrank := Homogeneous.orthonormal_transpose_fullRowRank U hU
  let Q := (R.shift K).toFullBFGSRun
  have hgbar : ∀ i, (Uᵀ)ᵀ *ᵥ (Uᵀ *ᵥ R.g (K + i)) = Q.g i := fun i => by
    rw [Matrix.transpose_transpose]
    exact grad_lift R U hU S hS K hK (K + i) (Nat.le_add_right K i)
  have hM := AffineProjection.matrix_lift_invariant Uᵀ hrank Q (fun i => Uᵀ *ᵥ R.g (K + i)) hgbar j
  have hQj : Q.H j = R.H (K + j) := rfl
  have hQ0 : Q.H 0 = R.H K := by
    change R.H (K + 0) = R.H K
    rw [Nat.add_zero]
  rw [hQj, hQ0, (hat_definitions U (R.H K) 0).2.1, (hat_definitions U (R.H (K + j)) 0).1,
    Matrix.transpose_transpose] at hM
  have hz : ∀ z : Vec r, R.H (K + j) *ᵥ (U *ᵥ z) =
      R.H K *ᵥ (U *ᵥ (((Uᵀ * R.H K * U)⁻¹ * (Uᵀ * R.H (K + j) * U)) *ᵥ z)) := by
    intro z
    rw [Matrix.mulVec_mulVec, hM]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨fun z => ⟨_, hz z⟩,
    ⟨((Uᵀ * R.H K * U)⁻¹ * (Uᵀ * R.H (K + j) * U)) *ᵥ (-R.α (K + j) • (Uᵀ *ᵥ R.g (K + j))), ?_⟩⟩
  rw [← hz]
  change -R.α (K + j) • (R.H (K + j) *ᵥ R.g (K + j)) = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, grad_lift R U hU S hS K hK (K + j) hk]

/-- Item `C/07_H/prose/051` (`companion/chapters/07_H.tex:513-514`): "The restriction of $U^\top$
to $H_KS$ is invertible because $U^\top H_KU\succ0$." $U^TH_KU\succ0$, and for every
$z\in\R^r$ exactly one $w\in H_KS$ (an element $H_KUz'$) has $U^Tw=z$. -/
theorem restriction_invertible {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (_hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (_hK : ∀ k, K ≤ k → R.g k ∈ S) :
    (Uᵀ * R.H K * U).PosDef ∧
      ∀ z : Vec r, ∃! w : Vec n, (∃ z' : Vec r, w = R.H K *ᵥ (U *ᵥ z')) ∧ Uᵀ *ᵥ w = z := by
  have hrank := Homogeneous.orthonormal_transpose_fullRowRank U hU
  have hC : (Uᵀ * R.H K * U).PosDef := by
    rw [← (hat_definitions U (R.H K) 0).1]
    exact AffineProjection.compress_posDef Uᵀ hrank (R.positive_definite K)
  have hdet : IsUnit (Uᵀ * R.H K * U).det := hC.det_pos.ne'.isUnit
  have hcomp : ∀ v : Vec r, Uᵀ *ᵥ (R.H K *ᵥ (U *ᵥ v)) = (Uᵀ * R.H K * U) *ᵥ v := fun v => by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨hC, fun z => ⟨R.H K *ᵥ (U *ᵥ ((Uᵀ * R.H K * U)⁻¹ *ᵥ z)), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · rw [hcomp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · rintro w ⟨⟨z', rfl⟩, hw⟩
    rw [hcomp] at hw
    have hz' : z' = (Uᵀ * R.H K * U)⁻¹ *ᵥ z := by
      rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    rw [hz']

/-- Item `C/07_H/disp/029` (`companion/chapters/07_H.tex:516-522`), equation (7.7.1):
"Therefore
\[ x_k=x_K+L_K(\widehat x_k-\widehat x_K),\qquad L_K=H_KU(U^\top H_KU)^{-1}." \]
For every $k\ge K$; $L_K$ is the variable `L` with its defining equation. Library:
`AdmissibleBFGSRun.affine_iterate_lift_tail`. -/
theorem iterate_lift {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (hK : ∀ k, K ≤ k → R.g k ∈ S) (xh : ℕ → Vec r) (hxh : ∀ k, xh k = Uᵀ *ᵥ R.x k)
    (L : Matrix (Fin n) (Fin r) ℝ) (hL : L = R.H K * U * (Uᵀ * R.H K * U)⁻¹) :
    ∀ k, K ≤ k → R.x k = R.x K + L *ᵥ (xh k - xh K) := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hrank := Homogeneous.orthonormal_transpose_fullRowRank U hU
  have hgbar : ∀ i, (Uᵀ)ᵀ *ᵥ (Uᵀ *ᵥ R.g (K + i)) = R.g (K + i) := fun i => by
    rw [Matrix.transpose_transpose]
    exact grad_lift R U hU S hS K hK (K + i) (Nat.le_add_right K i)
  have h := R.affine_iterate_lift_tail Uᵀ hrank K (fun i => Uᵀ *ᵥ R.g (K + i)) hgbar j
  rw [(hat_definitions U (R.H K) 0).2.1, ← hL] at h
  rw [hxh, hxh]
  exact h

/-- Item `C/07_H/prose/052` (`companion/chapters/07_H.tex:524-525`): "In particular, convergence
of the projected iterates implies convergence of the original iterates." If
$\widehat x_k\to z_*$, then $x_k\to x_K+L_K(z_*-\widehat x_K)$. Library:
`AdmissibleBFGSRun.affine_limit_lift_tail`. -/
theorem limit_lift {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (hK : ∀ k, K ≤ k → R.g k ∈ S) (xh : ℕ → Vec r) (hxh : ∀ k, xh k = Uᵀ *ᵥ R.x k)
    (L : Matrix (Fin n) (Fin r) ℝ) (hL : L = R.H K * U * (Uᵀ * R.H K * U)⁻¹) :
    ∀ zstar : Vec r, Tendsto xh atTop (𝓝 zstar) →
      Tendsto R.x atTop (𝓝 (R.x K + L *ᵥ (zstar - xh K))) := by
  intro zstar hz
  have hrank := Homogeneous.orthonormal_transpose_fullRowRank U hU
  have hgbar : ∀ i, (Uᵀ)ᵀ *ᵥ (Uᵀ *ᵥ R.g (K + i)) = R.g (K + i) := fun i => by
    rw [Matrix.transpose_transpose]
    exact grad_lift R U hU S hS K hK (K + i) (Nat.le_add_right K i)
  have hz' : Tendsto (fun i => Uᵀ *ᵥ R.x (K + i)) atTop (𝓝 zstar) := by
    have h := (tendsto_add_atTop_iff_nat K).mpr hz
    refine h.congr (fun i => ?_)
    rw [hxh, Nat.add_comm]
  have h := R.affine_limit_lift_tail Uᵀ hrank K (fun i => Uᵀ *ᵥ R.g (K + i)) hgbar zstar hz'
  rw [(hat_definitions U (R.H K) 0).2.1, ← hL, ← hxh] at h
  exact h

/-- Item `C/07_H/disp/030` (`companion/chapters/07_H.tex:527-530`), equation (7.7.2): "If
$\widehat x_k\to0$, the limit is
\[ x_*=x_K-H_KU(U^\top H_KU)^{-1}U^\top x_K." \] -/
theorem zero_limit_formula {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (hK : ∀ k, K ≤ k → R.g k ∈ S) (xh : ℕ → Vec r) (hxh : ∀ k, xh k = Uᵀ *ᵥ R.x k)
    (hz : Tendsto xh atTop (𝓝 0)) :
    Tendsto R.x atTop (𝓝 (R.x K - (R.H K * U * (Uᵀ * R.H K * U)⁻¹ * Uᵀ) *ᵥ R.x K)) := by
  have h := limit_lift a F hF_def R U hU S hS K hK xh hxh _ rfl 0 hz
  rw [hxh, zero_sub, Matrix.mulVec_neg, ← sub_eq_add_neg, Matrix.mulVec_mulVec] at h
  exact h

/-- Item `C/07_H/prose/053` (`companion/chapters/07_H.tex:532-533`): "The projected Hessian is
$(U^\top H_kU)^{-1}$, not $U^\top B_kU$. This distinction is necessary for a valid reduction."
(i) For $k\ge K$ the inverses $\widehat B_k=(U^TH_kU)^{-1}$ satisfy the Hessian form (7.2.1) of
the projected run, $\widehat B_{k+1}=\widehat B_k-\widehat g_k\widehat g_k^T/q_k
+\widehat y_k\widehat y_k^T/t_k$. (ii) In general $(U^THU)^{-1}\ne U^TH^{-1}U$, and using
$U^TBU$ as projected Hessian gives the wrong projected step: for $H=\begin{pmatrix}2&1\\1&1
\end{pmatrix}$, $U=e_1$ and $g=e_1\in S$, $(U^TBU)^{-1}U^Tg=1\ne2=U^THg$. -/
theorem projected_hessian_distinction {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (S : Submodule ℝ (Vec n)) (hS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (K : ℕ)
    (hK : ∀ k, K ≤ k → R.g k ∈ S) (Hh : ℕ → Mat r) (hHh : ∀ k, Hh k = Uᵀ * R.H k * U)
    (gh : ℕ → Vec r) (hgh : ∀ k, gh k = Uᵀ *ᵥ R.g k) :
    (∀ k, K ≤ k → (Hh (k + 1))⁻¹ = (Hh k)⁻¹ - (R.q k)⁻¹ • outer (gh k) (gh k) +
        (R.curvature k)⁻¹ • outer (gh (k + 1) - gh k) (gh (k + 1) - gh k)) ∧
      ∃ (H : Mat 2) (V : Matrix (Fin 2) (Fin 1) ℝ) (g : Vec 2), H.PosDef ∧ Vᵀ * V = 1 ∧
        (∃ z, V *ᵥ z = g) ∧ (Vᵀ * H * V)⁻¹ ≠ Vᵀ * H⁻¹ * V ∧
        (Vᵀ * H⁻¹ * V)⁻¹ *ᵥ (Vᵀ *ᵥ g) ≠ Vᵀ *ᵥ (H *ᵥ g) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨hpd, hs, -, hupd, hq, -, ht, -, -⟩ := projected_run a F hF_def R U hU S hS K hK
      (fun j => Uᵀ *ᵥ R.x j) (fun _ => rfl) Hh hHh gh hgh k hk
    have hstep : Uᵀ *ᵥ R.displacement k = bfgsStep (Hh k) (gh k) (R.α k) := hs
    have hg0 : gh k ≠ 0 := by
      intro h0
      apply R.gradient_nonzero k
      rw [← grad_lift R U hU S hS K hK k hk, ← hgh, h0, Matrix.mulVec_zero]
    have htpos : 0 < dot (gh (k + 1) - gh k) (bfgsStep (Hh k) (gh k) (R.α k)) := by
      rw [← hstep, ht]
      exact R.curvature_pos k
    rw [hupd, hstep, hessianUpdate hpd hg0 _ (R.alpha_pos k) htpos, ← hstep, ht,
      show metricEnergy (Hh k) (gh k) = R.q k from hq]
  · let A : Mat 2 := !![1, 0; 1, 1]
    let H : Mat 2 := Aᵀ * A
    let B : Mat 2 := !![1, -1; -1, 2]
    let V : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    have hH : H = !![2, 1; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [H, A, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]
    have hA : Function.Injective A.mulVec := by
      intro u w huw
      have h0 := congrFun huw 0
      have h1 := congrFun huw 1
      simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      ext i
      fin_cases i <;> simp <;> linarith
    have hpd : H.PosDef := by
      have h := metricGram_posDef (Matrix.PosDef.one (n := Fin 2) (R := ℝ)) hA
      simpa [metricGram, H] using h
    have hHB : H * B = 1 := by
      rw [hH]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
    have hinv : H⁻¹ = B := Matrix.inv_eq_right_inv hHB
    have hVHV : Vᵀ * H * V = !![2] := by
      rw [hH]
      ext i j
      fin_cases i
      fin_cases j
      simp [V, Matrix.mul_apply, Fin.sum_univ_two]
    have hVBV : Vᵀ * B * V = !![1] := by
      ext i j
      fin_cases i
      fin_cases j
      simp [V, B, Matrix.mul_apply, Fin.sum_univ_two]
    have hinv2 : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1 / 2] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i
      fin_cases j
      simp
    have hinv1 : (!![1] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i
      fin_cases j
      simp
    refine ⟨H, V, ![1, 0], hpd, ?_, ⟨![1], ?_⟩, ?_, ?_⟩
    · ext i j
      fin_cases i
      fin_cases j
      simp [V, Matrix.mul_apply, Fin.sum_univ_two]
    · ext i
      fin_cases i <;> simp [V, Matrix.mulVec, dotProduct]
    · rw [hinv, hVHV, hVBV, hinv2]
      intro h
      have := congrFun (congrFun h 0) 0
      norm_num at this
    · rw [hinv, hVBV, hinv1, hH]
      intro h
      have := congrFun h 0
      simp [V, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

/-! ### Section 7.7.2: a two-gradient endpoint observation (lines 551-574)

Standing assumptions: a finite max-linear objective $F=\max_ia_i^Tx$, an admissible run, and
(line 554) $f_k\to0$. "Linearly independent" is `LinearIndependent ℝ ![u, v]`; in the plane it
is $\det[u\ v]\ne0$ (`linearIndependent_pair_iff`). -/

/-- In the plane, $u,v$ are linearly independent iff $\det[u\ v]=u_1v_2-u_2v_1\ne0$ (the
library's `HomogeneousPlanar.pairDet`). -/
theorem linearIndependent_pair_iff (u v : Vec 2) :
    LinearIndependent ℝ ![u, v] ↔ HomogeneousPlanar.pairDet u v ≠ 0 := by
  have h := Matrix.linearIndependent_rows_iff_isUnit (K := ℝ) (A := Matrix.of ![u, v])
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two] at h
  simpa [HomogeneousPlanar.pairDet, Matrix.row] using h

/-- Item `C/07_H/disp/031` (`companion/chapters/07_H.tex:544-549`), equation (7.7.3): "Assume
$f_k\to0$. Then $d_k\to0$, and every endpoint satisfies
\[ g_{k+1}^\top x_{k+1}=f_{k+1}\longrightarrow0,\qquad
   g_k^\top x_{k+1}=f_k-d_k\longrightarrow0." \]
Library: `AdmissibleBFGSRun.homogeneous_endpoint_pairings_tendsto_zero` (for every finite convex
positively homogeneous objective). -/
theorem endpoint_pairings {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0)) :
    Tendsto R.d atTop (𝓝 0) ∧
      (∀ k, dot (R.g (k + 1)) (R.x (k + 1)) = F (R.x (k + 1)) ∧
        dot (R.g k) (R.x (k + 1)) = F (R.x k) - R.d k) ∧
      Tendsto (fun k => dot (R.g (k + 1)) (R.x (k + 1))) atTop (𝓝 0) ∧
      Tendsto (fun k => dot (R.g k) (R.x (k + 1))) atTop (𝓝 0) := by
  have hhom := (BfgsCoverage.Article.Global.maxLinear_convex_homogeneous a F hF_def).2
  obtain ⟨h1, h2⟩ := R.homogeneous_endpoint_pairings_tendsto_zero hhom hv
  exact ⟨(R.summable_predicted_decreases_of_value_limit 0 hv).tendsto_atTop_zero,
    fun k => ⟨R.homogeneous_euler hhom (k + 1), R.homogeneous_old_endpoint_pairing hhom k⟩, h2, h1⟩

/-- Item `C/07_H/prose/054` (`companion/chapters/07_H.tex:551-555`): "In two dimensions, if
$g_k$ and $g_{k+1}$ are linearly independent, these two equations determine $x_{k+1}$. There
are only finitely many distinct pairs, so their inverse norms are uniformly bounded. Thus the
endpoints of all independent-gradient transitions converge to zero, even if the full sequence
was not known to be bounded." For a planar finite max-linear objective and an admissible run
with $f_k\to0$: an independent transition determines $x_{k+1}$ from its two pairings; one
constant $C$ gives $\|z\|\le C(|g_k^Tz|+|g_{k+1}^Tz|)$ for every independent transition and
every $z$; and the endpoints $x_{j+1}$ of independent transitions tend to zero (no boundedness
assumed). Norms are the sup norm of `Vec 2`. -/
theorem independent_endpoints {m : ℕ} (a : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0)) :
    (∀ k, LinearIndependent ℝ ![R.g k, R.g (k + 1)] → ∀ z : Vec 2,
        dot (R.g k) z = dot (R.g k) (R.x (k + 1)) →
        dot (R.g (k + 1)) z = dot (R.g (k + 1)) (R.x (k + 1)) → z = R.x (k + 1)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ k, LinearIndependent ℝ ![R.g k, R.g (k + 1)] → ∀ z : Vec 2,
        ‖z‖ ≤ C * (|dot (R.g k) z| + |dot (R.g (k + 1)) z|)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j, J ≤ j → LinearIndependent ℝ ![R.g j, R.g (j + 1)] →
        ‖R.x (j + 1)‖ < ε := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a _ hF_def
  refine ⟨fun k hk z h1 h2 => ?_, ?_, fun ε hε => ?_⟩
  · have hd := (linearIndependent_pair_iff _ _).mp hk
    have hb := HomogeneousPlanar.pair_inverse_bound (R.g k) (R.g (k + 1)) (z - R.x (k + 1)) hd
    have e1 : dot (R.g k) (z - R.x (k + 1)) = 0 := by
      change R.g k ⬝ᵥ (z - R.x (k + 1)) = 0
      rw [dotProduct_sub]
      change dot (R.g k) z - dot (R.g k) (R.x (k + 1)) = 0
      rw [h1, sub_self]
    have e2 : dot (R.g (k + 1)) (z - R.x (k + 1)) = 0 := by
      change R.g (k + 1) ⬝ᵥ (z - R.x (k + 1)) = 0
      rw [dotProduct_sub]
      change dot (R.g (k + 1)) z - dot (R.g (k + 1)) (R.x (k + 1)) = 0
      rw [h2, sub_self]
    rw [e1, e2, abs_zero, add_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  · obtain ⟨C, hC, hbound⟩ := HomogeneousPlanar.finite_pair_inverse_bound (Finset.univ.image a)
    exact ⟨C, hC, fun k hk z => hbound _ (R.maxLinear_gradient_mem _ hA k) _
      (R.maxLinear_gradient_mem _ hA (k + 1)) z ((linearIndependent_pair_iff _ _).mp hk)⟩
  · obtain ⟨J, hJ⟩ := R.maxLinear_planar_anchor_small _ hA hv ε hε
    exact ⟨J, fun j hj hind => hJ j hj ((linearIndependent_pair_iff _ _).mp hind)⟩

/-- Item `C/07_H/prose/055` (`companion/chapters/07_H.tex:557`): "An unchanged nonzero
gradient cannot satisfy weak Wolfe on a strict descent step." If $g^Ts<0$ and $c_2<1$, then
$g^Ts\ge c_2g^Ts$ fails; hence consecutive gradients of an admissible run always differ. -/
theorem unchanged_gradient_fails_wolfe {n : ℕ} :
    (∀ (g s : Vec n) (c₂ : ℝ), c₂ < 1 → dot g s < 0 → ¬ dot g s ≥ c₂ * dot g s) ∧
      ∀ {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ), R.g (k + 1) ≠ R.g k := by
  refine ⟨fun g s c₂ hc₂ hneg h => ?_, fun R k => (R.gradient_transition_ne k).symm⟩
  nlinarith

/-- Item `C/07_H/prose/056` (`companion/chapters/07_H.tex:558-561`): "Distinct gradients that
are positive multiples of one another also cannot both be active at positive-value iterates:
among positive multiples of a slope, only the largest multiple can attain a positive maximum."
For $F=\max_ia_i^Tx$: if $g_k=cg_j$ with $c>0$ at iterates of positive value, then $g_k=g_j$;
and if $a_{i'}=ca_i$ with $c>1$, then $a_i$ is not active ($F(x)\ne a_i^Tx$) at any point with
$F(x)>0$. -/
theorem positive_multiples_active {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) :
    (∀ (R : AdmissibleBFGSRun n F) (j k : ℕ) (c : ℝ), 0 < c → R.g k = c • R.g j →
        0 < F (R.x j) → 0 < F (R.x k) → R.g k = R.g j) ∧
      ∀ (i i' : Fin m) (c : ℝ), 1 < c → a i' = c • a i → ∀ x, 0 < F x → F x ≠ dot (a i) x := by
  have hhom := (BfgsCoverage.Article.Global.maxLinear_convex_homogeneous a F hF_def).2
  refine ⟨fun R j k c hc he hj hk => ?_, fun i i' c hc he x hx hact => ?_⟩
  · exact HomogeneousBlock.positive_parallel_supports_eq hhom (R.x j) (R.x k) (R.g j) (R.g k)
      (convex_supporting_inequality R.convex (R.hasGradient j))
      (convex_supporting_inequality R.convex (R.hasGradient k)) hj hk c hc he
  · have hle : dot (a i') x ≤ F x := (hF_def x).2 ⟨i', rfl⟩
    rw [he, HomogeneousBlock.dot_smul_first, ← hact] at hle
    nlinarith

/-- Item `C/07_H/prose/057` (`companion/chapters/07_H.tex:561-562`): "Consequently, any
dependent transition on the positive-value branch is between opposite slopes." For a finite
max-linear objective and an admissible run with $f(x_k)>0$ for all $k$: if $g_k,g_{k+1}$ are
linearly dependent, then $g_{k+1}=-\kappa g_k$ with $\kappa>0$. (Any dimension; the library's
planar form is `AdmissibleBFGSRun.homogeneous_dependent_transition_opposite`.) -/
theorem dependent_transition_opposite {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (hpos : ∀ k, 0 < F (R.x k)) (k : ℕ)
    (hdep : ¬ LinearIndependent ℝ ![R.g k, R.g (k + 1)]) :
    ∃ κ : ℝ, 0 < κ ∧ R.g (k + 1) = -κ • R.g k := by
  rw [LinearIndependent.pair_iff' (R.gradient_nonzero k)] at hdep
  push_neg at hdep
  obtain ⟨c, hc⟩ := hdep
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact R.gradient_nonzero (k + 1) hc.symm
  rcases lt_or_gt_of_ne hc0 with hneg | hposc
  · exact ⟨-c, neg_pos.mpr hneg, by rw [neg_neg, hc]⟩
  · exfalso
    have he := ((positive_multiples_active a F hF_def).1 R k (k + 1) c hposc hc.symm (hpos k)
      (hpos (k + 1)))
    exact R.gradient_transition_ne k he.symm

/-- Proof of Theorem 7.C, lines 583-586 (not a register item): "If the global objective is
unbounded below, its slope set cannot contain an opposite pair $a,-\kappa a$ with $\kappa>0$:
their maximum alone is nonnegative everywhere. Every accepted gradient transition is therefore
linearly independent in the plane." The last sentence holds on the branch $f_k\to0$ under
discussion (positive values; `homogeneous_finite_branch_positive`), as "In the other branch"
(line 589) confirms. -/
theorem unbounded_transitions_independent {m : ℕ} (a : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (hinf : ¬ BddBelow (Set.range F)) :
    (∀ i i' : Fin m, ∀ κ : ℝ, 0 < κ → a i' ≠ -κ • a i) ∧
      ∀ R : AdmissibleBFGSRun 2 F, Tendsto (fun k => F (R.x k)) atTop (𝓝 0) →
        ∀ k, LinearIndependent ℝ ![R.g k, R.g (k + 1)] := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a _ hF_def
  have hhom := Homogeneous.finiteMaxLinear_homogeneous _ hA
  obtain ⟨w, hw⟩ := (Homogeneous.unboundedBelow_iff_negative_value hhom).mp hinf
  refine ⟨fun i i' κ hκ => Homogeneous.unbounded_finiteMax_no_opposite_slopes _ hA hinf (a i)
      (a i') (Finset.mem_image_of_mem a (Finset.mem_univ i))
      (Finset.mem_image_of_mem a (Finset.mem_univ i')) κ hκ, fun R hv k => ?_⟩
  exact (linearIndependent_pair_iff _ _).mpr (R.maxLinear_planar_transition_independent _ hA w hw
    (R.homogeneous_finite_branch_positive hhom 0 hv) k)

/-- Proof of the remark of line 135 (item `C/07_H/prose/013`), lines 593-596: "For an
unbounded-below max-linear objective there is no stationary point: a stationary point of a convex
function would be a global minimizer, and no minimizer exists. Thus the zero limit is genuinely
nonstationary." For a finite max-linear objective (any dimension) unbounded below: a point $x$
with $0\in\partial f(x)$ would be a global minimizer, there is no global minimizer, hence
$0\notin\partial f(x)$ for every $x$ (in particular at the limit $0$). -/
theorem no_stationary_point {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (_hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (hinf : ¬ BddBelow (Set.range F)) :
    (∀ x, (0 : Vec n) ∈ ConvexSubdifferential.subdifferential F x → ∀ y, F x ≤ F y) ∧
      (¬ ∃ x, ∀ y, F x ≤ F y) ∧
      ∀ x, (0 : Vec n) ∉ ConvexSubdifferential.subdifferential F x := by
  have hmin : ∀ x, (0 : Vec n) ∈ ConvexSubdifferential.subdifferential F x → ∀ y, F x ≤ F y := by
    intro x hx y
    have h := ConvexSubdifferential.mem_subdifferential.mp hx y
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
    linarith
  have hnomin : ¬ ∃ x, ∀ y, F x ≤ F y := by
    rintro ⟨x, hx⟩
    exact hinf ⟨F x, by rintro _ ⟨y, rfl⟩; exact hx y⟩
  exact ⟨hmin, hnomin, fun x hx => hnomin ⟨x, hmin x hx⟩⟩

/-! ### Section 7.7.4: the general planar finite-value branch (lines 602-668)

Lines 609-665 prove the claim of lines 605-607 (`planar_finite_value_convergence`). Its
displays are stated under the standing assumptions at that point: a planar finite max-linear
objective (slopes `slopes`, since `a` and `b` are the anchor indices of the text), an
admissible run with $f_k\to0$, consecutive anchors $x_a,x_b$ (endpoints of independent
transitions $a-1$ and $b-1$, with only dependent transitions in between) with at least one
intermediate iterate ($a+2\le b$), the initial gradient $g=g_a$ of the block and $\kappa>0$ with
$g_{a+1}=-\kappa g$. The anchor hypotheses are not used; `block_general` proves all the
displays without them, from assumptions that `absVRun` satisfies (see the examples). -/

/-- Item `C/07_H/prose/059` (`companion/chapters/07_H.tex:593-595`): "For completeness,
opposing-gradient transitions can also be handled, giving convergence for all planar finite
max-linear objectives, including noncompact bounded-below ones." For every finite max-linear
objective on $\R^2$: every admissible run whose values have a finite limit has convergent
iterates; if the objective is bounded below (coercive or not), every admissible run has
convergent iterates. Library: `AdmissibleBFGSRun.maxLinear_planar_finite_value_has_limit`,
`AdmissibleBFGSRun.maxLinear_planar_lower_bound_has_limit`. -/
theorem planar_finite_value_convergence {m : ℕ} (a : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) :
    (∀ R : AdmissibleBFGSRun 2 F, (∃ L : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) →
        ∃ xstar, Tendsto R.x atTop (𝓝 xstar)) ∧
      ((∃ L : ℝ, ∀ x, L ≤ F x) →
        ∀ R : AdmissibleBFGSRun 2 F, ∃ xstar, Tendsto R.x atTop (𝓝 xstar)) := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a _ hF_def
  refine ⟨fun R ⟨L, hL⟩ => ?_, fun ⟨L, hL⟩ R => ?_⟩
  · obtain ⟨-, xstar, hx, -⟩ := R.maxLinear_planar_finite_value_has_limit _ hA L hL
    exact ⟨xstar, hx⟩
  · obtain ⟨xstar, hx, -⟩ := R.maxLinear_planar_lower_bound_has_limit _ hA L (fun k => hL _)
    exact ⟨xstar, hx⟩

/-- General form of the displays of lines 623-652 and of the step "monotonicity gives
$f_b\le(1-c_1)f_a$" (line 634), without the anchor hypotheses: for a planar finite max-linear
objective, an admissible run with $f_k\to0$, indices $a+2\le b$, $g=g_a$ and $\kappa>0$ with
$g_{a+1}=-\kappa g$:
$d_a=f_a+f_{a+1}/\kappa$; $f_{a+1}\le\frac{1-c_1}{1+c_1/\kappa}f_a\le(1-c_1)f_a$;
$f_b\le(1-c_1)f_a$; $-f_a/\kappa\le g^Tx_k\le f_a$ for $a\le k\le b$;
$g^T(x_b-x_a)\le-c_1f_a$; and $x_k=x_a+\theta(x_b-x_a)$ with $a\le k\le b$ gives
$0\le\theta\le(1+1/\kappa)/c_1$. -/
theorem block_general {m : ℕ} (slopes : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0))
    (a b : ℕ) (hab : a + 2 ≤ b) (g : Vec 2) (hg : g = R.g a) (κ : ℝ) (hκ : 0 < κ)
    (hopp : R.g (a + 1) = -κ • g) :
    R.d a = F (R.x a) + F (R.x (a + 1)) / κ ∧
      (F (R.x (a + 1)) ≤ (1 - R.c₁) / (1 + R.c₁ / κ) * F (R.x a) ∧
        (1 - R.c₁) / (1 + R.c₁ / κ) * F (R.x a) ≤ (1 - R.c₁) * F (R.x a)) ∧
      F (R.x b) ≤ (1 - R.c₁) * F (R.x a) ∧
      (∀ k, a ≤ k → k ≤ b → -F (R.x a) / κ ≤ dot g (R.x k) ∧ dot g (R.x k) ≤ F (R.x a)) ∧
      dot g (R.x b - R.x a) ≤ -R.c₁ * F (R.x a) ∧
      ∀ (k : ℕ) (θ : ℝ), a ≤ k → k ≤ b → R.x k = R.x a + θ • (R.x b - R.x a) →
        0 ≤ θ ∧ θ ≤ (1 + 1 / κ) / R.c₁ := by
  have hhom := (BfgsCoverage.Article.Global.maxLinear_convex_homogeneous slopes F hF_def).2
  have hpos : ∀ k, 0 < F (R.x k) := R.homogeneous_finite_branch_positive hhom 0 hv
  have hopp' : R.g (a + 1) = -κ • R.g a := by rw [hopp, hg]
  have hdec := R.homogeneous_opposite_decrease hhom a κ hκ hopp'
  obtain ⟨hc1, hc2⟩ := R.homogeneous_opposite_contraction hhom a κ hκ hopp' (hpos a).le
  have hc₁ := R.c₁_pos
  have hc₁1 : R.c₁ < 1 := R.c₁_lt_c₂.trans R.c₂_lt_one
  have hratio : (1 - R.c₁) / (1 + R.c₁ / κ) ≤ 1 - R.c₁ :=
    div_le_self (by linarith) (by have := div_pos hc₁ hκ; linarith)
  have hend : F (R.x b) ≤ (1 - R.c₁) * F (R.x a) :=
    (R.objective_antitone (by omega : a + 1 ≤ b)).trans hc2
  have hwin : ∀ k, a ≤ k → k ≤ b → -F (R.x a) / κ ≤ dot g (R.x k) ∧ dot g (R.x k) ≤ F (R.x a) := by
    intro k hak _
    have hFk : F (R.x k) ≤ F (R.x a) := R.objective_antitone hak
    have h1 : dot g (R.x k) ≤ F (R.x k) := by
      rw [hg]
      exact R.homogeneous_support hhom a (R.x k)
    have h2 : dot (R.g (a + 1)) (R.x k) ≤ F (R.x k) := R.homogeneous_support hhom (a + 1) (R.x k)
    rw [hopp, HomogeneousBlock.dot_smul_first] at h2
    refine ⟨?_, h1.trans hFk⟩
    rw [div_le_iff₀ hκ]
    linarith
  have heul : dot g (R.x a) = F (R.x a) := by
    rw [hg]
    exact R.homogeneous_euler hhom a
  have hgb : dot g (R.x b) ≤ (1 - R.c₁) * F (R.x a) := by
    rw [hg]
    exact (R.homogeneous_support hhom a (R.x b)).trans hend
  have hdiff : dot g (R.x b - R.x a) ≤ -R.c₁ * F (R.x a) := by
    have e : dot g (R.x b - R.x a) = dot g (R.x b) - dot g (R.x a) := by
      change g ⬝ᵥ (R.x b - R.x a) = g ⬝ᵥ R.x b - g ⬝ᵥ R.x a
      rw [dotProduct_sub]
    rw [e, heul]
    linarith
  refine ⟨hdec, ⟨hc1, mul_le_mul_of_nonneg_right hratio (hpos a).le⟩, hend, hwin, hdiff, ?_⟩
  intro k θ hak hkb hx
  exact HomogeneousBlock.interpolation_parameter_bound g (R.x a) (R.x b) (R.x k) (F (R.x a)) κ
    R.c₁ θ (hpos a) hκ hc₁ heul hgb (hwin k hak hkb).1 (hwin k hak hkb).2 hx

/-- Item `C/07_H/disp/032` (`companion/chapters/07_H.tex:611-613`), in the proof of the planar
finite-value branch: "Write its initial gradient as $g$, and the next opposite gradient as
$-\kappa g$, with $\kappa>0$. The first dependent transition has
\[ d_a=f_a+f_{a+1}/\kappa." \]
Under the standing assumptions of the block (see the section header); general form
`block_general`. -/
theorem block_decrease {m : ℕ} (slopes : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0))
    (a b : ℕ) (_ha : 1 ≤ a) (hab : a + 2 ≤ b)
    (_hanchor_a : LinearIndependent ℝ ![R.g (a - 1), R.g a])
    (_hanchor_b : LinearIndependent ℝ ![R.g (b - 1), R.g b])
    (_hblock : ∀ l, a ≤ l → l + 2 ≤ b → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)])
    (g : Vec 2) (hg : g = R.g a) (κ : ℝ) (hκ : 0 < κ) (hopp : R.g (a + 1) = -κ • g) :
    R.d a = F (R.x a) + F (R.x (a + 1)) / κ :=
  (block_general slopes F hF_def R hv a b hab g hg κ hκ hopp).1

/-- Item `C/07_H/disp/033` (`companion/chapters/07_H.tex:617-620`), in the proof of the planar
finite-value branch: "Armijo implies
\[ f_{a+1}\le\frac{1-c_1}{1+c_1/\kappa}f_a\le(1-c_1)f_a." \]
Under the standing assumptions of the block; general form `block_general`. -/
theorem block_contraction {m : ℕ} (slopes : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0))
    (a b : ℕ) (_ha : 1 ≤ a) (hab : a + 2 ≤ b)
    (_hanchor_a : LinearIndependent ℝ ![R.g (a - 1), R.g a])
    (_hanchor_b : LinearIndependent ℝ ![R.g (b - 1), R.g b])
    (_hblock : ∀ l, a ≤ l → l + 2 ≤ b → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)])
    (g : Vec 2) (hg : g = R.g a) (κ : ℝ) (hκ : 0 < κ) (hopp : R.g (a + 1) = -κ • g) :
    F (R.x (a + 1)) ≤ (1 - R.c₁) / (1 + R.c₁ / κ) * F (R.x a) ∧
      (1 - R.c₁) / (1 + R.c₁ / κ) * F (R.x a) ≤ (1 - R.c₁) * F (R.x a) :=
  (block_general slopes F hF_def R hv a b hab g hg κ hκ hopp).2.1

/-- Item `C/07_H/disp/034` (`companion/chapters/07_H.tex:625-627`), in the proof of the planar
finite-value branch: "Every accepted point in the block obeys
\[ -f_a/\kappa\le g^\top x\le f_a, \]
because $g$ and $-\kappa g$ are both slopes of the objective and $f(x)\le f_a$." For every
$x=x_k$, $a\le k\le b$. Under the standing assumptions of the block; general form
`block_general`. -/
theorem block_window {m : ℕ} (slopes : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0))
    (a b : ℕ) (_ha : 1 ≤ a) (hab : a + 2 ≤ b)
    (_hanchor_a : LinearIndependent ℝ ![R.g (a - 1), R.g a])
    (_hanchor_b : LinearIndependent ℝ ![R.g (b - 1), R.g b])
    (_hblock : ∀ l, a ≤ l → l + 2 ≤ b → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)])
    (g : Vec 2) (hg : g = R.g a) (κ : ℝ) (hκ : 0 < κ) (hopp : R.g (a + 1) = -κ • g) :
    ∀ k, a ≤ k → k ≤ b → -F (R.x a) / κ ≤ dot g (R.x k) ∧ dot g (R.x k) ≤ F (R.x a) :=
  (block_general slopes F hF_def R hv a b hab g hg κ hκ hopp).2.2.2.1

/-- Item `C/07_H/disp/035` (`companion/chapters/07_H.tex:632-634`), in the proof of the planar
finite-value branch: "The endpoint difference satisfies
\[ g^\top(x_b-x_a)\le-c_1f_a." \]
Under the standing assumptions of the block; general form `block_general`. -/
theorem block_endpoint_difference {m : ℕ} (slopes : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0))
    (a b : ℕ) (_ha : 1 ≤ a) (hab : a + 2 ≤ b)
    (_hanchor_a : LinearIndependent ℝ ![R.g (a - 1), R.g a])
    (_hanchor_b : LinearIndependent ℝ ![R.g (b - 1), R.g b])
    (_hblock : ∀ l, a ≤ l → l + 2 ≤ b → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)])
    (g : Vec 2) (hg : g = R.g a) (κ : ℝ) (hκ : 0 < κ) (hopp : R.g (a + 1) = -κ • g) :
    dot g (R.x b - R.x a) ≤ -R.c₁ * F (R.x a) :=
  (block_general slopes F hF_def R hv a b hab g hg κ hκ hopp).2.2.2.2.1

/-- Item `C/07_H/disp/036` (`companion/chapters/07_H.tex:638-640`), in the proof of the planar
finite-value branch: "Writing $x=x_a+\theta(x_b-x_a)$ consequently gives
\[ 0\le\theta\le\frac{1+1/\kappa}{c_1}." \]
For every point $x=x_k$ of the block ($a\le k\le b$) written in this form. Under the standing
assumptions of the block; general form `block_general`. -/
theorem block_parameter_bound {m : ℕ} (slopes : Fin m → Vec 2) (F : Vec 2 → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x))
    (R : AdmissibleBFGSRun 2 F) (hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 0))
    (a b : ℕ) (_ha : 1 ≤ a) (hab : a + 2 ≤ b)
    (_hanchor_a : LinearIndependent ℝ ![R.g (a - 1), R.g a])
    (_hanchor_b : LinearIndependent ℝ ![R.g (b - 1), R.g b])
    (_hblock : ∀ l, a ≤ l → l + 2 ≤ b → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)])
    (g : Vec 2) (hg : g = R.g a) (κ : ℝ) (hκ : 0 < κ) (hopp : R.g (a + 1) = -κ • g) :
    ∀ (k : ℕ) (θ : ℝ), a ≤ k → k ≤ b → R.x k = R.x a + θ • (R.x b - R.x a) →
      0 ≤ θ ∧ θ ≤ (1 + 1 / κ) / R.c₁ :=
  (block_general slopes F hF_def R hv a b hab g hg κ hκ hopp).2.2.2.2.2

/-- $|v|=\max(v,-v)$: the objective `Master.absV` ($F(u,v)=|v|$) is the finite max-linear
objective with the slopes $(0,1)$, $(0,-1)$. -/
theorem absV_isGreatest (x : Vec 2) :
    IsGreatest (Set.range fun i => dot ((![![0, 1], ![0, -1]] : Fin 2 → Vec 2) i) x)
      (BfgsCoverage.Article.Master.absV x) := by
  have h0 : dot (![0, 1] : Vec 2) x = x 1 := by simp [dot, Fin.sum_univ_two]
  have h1 : dot (![0, -1] : Vec 2) x = -x 1 := by simp [dot, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · rcases abs_choice (x 1) with h | h
    · exact ⟨0, by simp [h0, BfgsCoverage.Article.Master.absV, h]⟩
    · exact ⟨1, by simp [h1, BfgsCoverage.Article.Master.absV, h]⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa [h0, BfgsCoverage.Article.Master.absV] using le_abs_self (x 1)
    · simpa [h1, BfgsCoverage.Article.Master.absV] using neg_le_abs (x 1)

/-- The admissible run `Master.absVRun 1 1` of $F(u,v)=|v|$ converges to $(1,0)$. -/
theorem absVRun_tendsto :
    Tendsto (BfgsCoverage.Article.Master.absVRun 1 1 one_pos).x atTop (𝓝 ![1, 0]) := by
  have hlim : Tendsto (fun k => (BfgsCoverage.Article.Master.axisRun 1 one_pos).x k + ![1, 0])
      atTop (𝓝 (0 + ![1, 0])) :=
    (UnexcitedMetric.literal_point_limit (ρ := 1 / 2) (v₀ := 1) (by norm_num)
      (by norm_num)).add_const _
  rw [zero_add] at hlim
  exact hlim

/-- Item `C/07_H/prose/061` (`companion/chapters/07_H.tex:654-656`): "Reducing to the span of
the recurrent gradients and using (7.7.1) proves the same conclusion whenever that span has
dimension at most two in any ambient dimension. The limit may be nonzero in the original
coordinates." (i) For every finite max-linear objective in every dimension and every admissible
run whose recurrent gradients span a space of dimension at most two, a finite value limit gives
convergent iterates. (ii) The limit can be nonzero: $F(u,v)=|v|=\max(v,-v)$ on $\R^2$ and its
admissible run `BfgsCoverage.Article.Master.absVRun 1 1` (iterates $(1,\pm2^{-k})$) converge to
$(1,0)\ne0$. (The reference printed "(7.1)" before the correction M17 of 15 October 2026, item
`C/07_H/prose/028`.) -/
theorem recurrent_reduction_nonzero_limit :
    (∀ (n m : ℕ) (a : Fin m → Vec n) (F : Vec n → ℝ),
      (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) →
      ∀ (R : AdmissibleBFGSRun n F) (G : Set (Vec n)), G = {v | ∃ᶠ k in atTop, R.g k = v} →
        Module.finrank ℝ (Submodule.span ℝ G) ≤ 2 →
        (∃ L : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 L)) → ∃ xstar, Tendsto R.x atTop (𝓝 xstar)) ∧
      ∃ (a : Fin 2 → Vec 2) (F : Vec 2 → ℝ), (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) ∧
        ∃ R : AdmissibleBFGSRun 2 F,
          Module.finrank ℝ (Submodule.span ℝ {v | ∃ᶠ k in atTop, R.g k = v}) ≤ 2 ∧
          Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧
          ∃ xstar : Vec 2, xstar ≠ 0 ∧ Tendsto R.x atTop (𝓝 xstar) := by
  refine ⟨fun n m a F hF_def R G hG hrank hlim =>
    (recurrent_rank_le_two_convergence a F hF_def R G hG hrank).1 hlim, ?_⟩
  refine ⟨![![0, 1], ![0, -1]], BfgsCoverage.Article.Master.absV, absV_isGreatest,
    BfgsCoverage.Article.Master.absVRun 1 1 one_pos, ?_, ?_, ![1, 0], ?_, absVRun_tendsto⟩
  · exact (Submodule.finrank_le _).trans (by simp)
  · have h := ((continuous_abs.comp (continuous_apply 1)).tendsto _).comp absVRun_tendsto
    simpa [Function.comp_def, BfgsCoverage.Article.Master.absV] using h
  · intro h
    have := congrFun h 0
    simp at this

/-! ### Section 7.8: a noncompact convergence theorem in arbitrary dimension (lines 682-730)

Standing assumptions: a finite max-linear objective $F=\max_ia_i^Tx$ on $\R^n$, $S$ and $P$
of display `C/07_H/disp/037` as variables with their defining equations, the relative-interior
condition $0\in\operatorname{relint}P$ (relative to $S$, with the subspace topology), and $U$
with orthonormal columns spanning $S$. -/

/-- Item `C/07_H/prose/062` (`companion/chapters/07_H.tex:674-676`): "One source of
noncompactness is a subspace of directions on which the function is constant. When this is the
only source of noncompactness, the case is fully tractable in all dimensions." (i) If $F$ is
constant along a nonzero subspace $V$ ($F(x+v)=F(x)$ for $v\in V$), every nonempty sublevel of
$F$ is unbounded, hence not compact. (ii) A finite max-linear objective is constant along the
directions orthogonal to all its slopes. The second sentence announces the theorem of this
section (displays `C/07_H/disp/038`, `C/07_H/disp/039`). -/
theorem flat_directions_noncompact :
    (∀ (n : ℕ) (F : Vec n → ℝ) (V : Submodule ℝ (Vec n)), V ≠ ⊥ →
      (∀ x, ∀ v ∈ V, F (x + v) = F x) → ∀ c : ℝ, {x | F x ≤ c}.Nonempty →
        ¬ Bornology.IsBounded {x | F x ≤ c}) ∧
      ∀ (n m : ℕ) (a : Fin m → Vec n) (F : Vec n → ℝ),
        (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) →
        ∀ x w : Vec n, (∀ i, dot (a i) w = 0) → F (x + w) = F x := by
  refine ⟨fun n F V hV hflat c hne hb => ?_, fun n m a F hF_def x w hw => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x₀ hx₀)
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have ht : 0 ≤ (C + ‖x₀‖ + 1) / ‖v‖ := div_nonneg (by positivity) hnv.le
    have hmem : x₀ + ((C + ‖x₀‖ + 1) / ‖v‖) • v ∈ {x | F x ≤ c} := by
      show F (x₀ + ((C + ‖x₀‖ + 1) / ‖v‖) • v) ≤ c
      rw [hflat x₀ _ (V.smul_mem _ hvV)]
      exact hx₀
    have h1 := hC _ hmem
    have h2 : ‖((C + ‖x₀‖ + 1) / ‖v‖) • v‖ ≤ ‖x₀ + ((C + ‖x₀‖ + 1) / ‖v‖) • v‖ + ‖x₀‖ := by
      calc ‖((C + ‖x₀‖ + 1) / ‖v‖) • v‖ = ‖(x₀ + ((C + ‖x₀‖ + 1) / ‖v‖) • v) - x₀‖ := by
            rw [add_sub_cancel_left]
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, div_mul_cancel₀ _ hnv.ne'] at h2
    linarith
  · obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
    have hall : ∀ b ∈ Finset.univ.image a, dot b (x + w) = dot b x := by
      intro b hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      change a i ⬝ᵥ (x + w) = a i ⬝ᵥ x
      rw [dotProduct_add]
      change dot (a i) x + dot (a i) w = dot (a i) x
      rw [hw i, add_zero]
    unfold Homogeneous.finiteMaxLinear
    exact Finset.sup'_congr hA rfl hall

/-- Item `C/07_H/disp/037` (`companion/chapters/07_H.tex:680-683`): the definitions
\[ S=\operatorname{span}\{a_1,\ldots,a_m\},\qquad P=\operatorname{conv}\{a_1,\ldots,a_m\}, \]
together with the condition "$0\in\operatorname{relint}P$, with relative interior taken in
$S$" of lines 697-698. $S$ and $P$ are `Submodule.span ℝ (Set.range a)` and
`convexHull ℝ (Set.range a)`; the relative interior is the interior in the subtype `S`. The
statement: the library's `Homogeneous.RelativeInteriorZero` of the slope set is exactly
this condition. -/
theorem relint_def {n m : ℕ} (a : Fin m → Vec n) (S : Submodule ℝ (Vec n))
    (hS : S = Submodule.span ℝ (Set.range a)) (P : Set (Vec n))
    (hP : P = convexHull ℝ (Set.range a)) :
    Homogeneous.RelativeInteriorZero (Finset.univ.image a) ↔
      (0 : S) ∈ interior {v : S | (v : Vec n) ∈ P} := by
  subst hS hP
  unfold Homogeneous.RelativeInteriorZero
  rw [coe_image_univ]

/-- $x\perp S$ (orthogonal to every vector of $S$) iff $U^Tx=0$, when the columns of $U$ span
$S$. -/
theorem perp_iff {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (S : Submodule ℝ (Vec n))
    (hUS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) (x : Vec n) :
    (∀ v ∈ S, dot v x = 0) ↔ Uᵀ *ᵥ x = 0 := by
  have hT : ∀ z : Vec r, dot (U *ᵥ z) x = dot z (Uᵀ *ᵥ x) := fun z => by
    simpa only [Matrix.transpose_transpose] using AffineProjection.dot_transpose_mulVec Uᵀ z x
  constructor
  · intro h
    ext i
    have hi := h (U *ᵥ Pi.single i 1) ((hUS _).mpr ⟨_, rfl⟩)
    rw [hT] at hi
    change Pi.single i 1 ⬝ᵥ (Uᵀ *ᵥ x) = 0 at hi
    rw [dotProduct_comm, dotProduct_single_one] at hi
    simpa using hi
  · intro h v hv
    obtain ⟨z, rfl⟩ := (hUS v).mp hv
    rw [hT, h]
    simp [dot]

/-- Item `C/07_H/disp/038` (`companion/chapters/07_H.tex:689-691`), with the claims of lines
697-699: "suppose $0\in\operatorname{relint}P$, with relative interior taken in $S$. Then $f$
depends only on the projection to $S$ and is coercive there:
\[ f(x)\ge\mu\|U^\top x\|\quad\text{for some }\mu>0." \]
$F(x)=F(UU^Tx)$ ($UU^Tx$ is the orthogonal projection of $x$ on $S$), and
$F(x)\ge\mu\|U^Tx\|$ (Euclidean norm) for some $\mu>0$. -/
theorem relint_coercive {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (S : Submodule ℝ (Vec n)) (hS : S = Submodule.span ℝ (Set.range a)) (P : Set (Vec n))
    (hP : P = convexHull ℝ (Set.range a)) (hri : (0 : S) ∈ interior {v : S | (v : Vec n) ∈ P})
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hUS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) :
    (∀ x, F x = F (U *ᵥ (Uᵀ *ᵥ x))) ∧
      ∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖euclideanVector (Uᵀ *ᵥ x)‖ ≤ F x := by
  have hri' := (relint_def a S hS P hP).mpr hri
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  subst hS
  have hspan : ∀ x, x ∈ Submodule.span ℝ ((Finset.univ.image a : Finset (Vec n)) : Set (Vec n)) ↔
      ∃ z, U *ᵥ z = x := by
    rw [coe_image_univ]
    exact hUS
  have hAsub : ∀ b ∈ Finset.univ.image a, ∃ z, U *ᵥ z = b :=
    fun b hb => (hspan b).mp (Submodule.subset_span hb)
  exact ⟨fun x => (Homogeneous.finiteMaxLinear_projection_eq _ hA U hU hAsub x).symm,
    Homogeneous.relativeInterior_euclidean_projection_bound _ hA hri' U hU hspan⟩

/-- Item `C/07_H/disp/039` (`companion/chapters/07_H.tex:696-702`), equation (7.8.1), with the
claim of line 705: "Theorem 7.A implies $U^\top x_k\to0$. The invariant subspace formula with
$K=0$ gives
\[ x_k\longrightarrow x_0-H_0U(U^\top H_0U)^{-1}U^\top x_0." \]
For every admissible run. Library: `AdmissibleBFGSRun.maxLinear_relativeInterior_convergence`
(`relativeInteriorConvergence`). -/
theorem relint_limit {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (S : Submodule ℝ (Vec n)) (hS : S = Submodule.span ℝ (Set.range a)) (P : Set (Vec n))
    (hP : P = convexHull ℝ (Set.range a)) (hri : (0 : S) ∈ interior {v : S | (v : Vec n) ∈ P})
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hUS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x)
    (R : AdmissibleBFGSRun n F) :
    Tendsto (fun k => Uᵀ *ᵥ R.x k) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 (R.x 0 - (R.H 0 * U * (Uᵀ * R.H 0 * U)⁻¹ * Uᵀ) *ᵥ R.x 0)) := by
  have hri' := (relint_def a S hS P hP).mpr hri
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  subst hS
  have hspan : ∀ x, x ∈ Submodule.span ℝ ((Finset.univ.image a : Finset (Vec n)) : Set (Vec n)) ↔
      ∃ z, U *ᵥ z = x := by
    rw [coe_image_univ]
    exact hUS
  have h := R.maxLinear_relativeInterior_convergence _ hA hri' U hU hspan
  rw [(hat_definitions U (R.H 0) (R.x 0)).2.2] at h
  exact h

/-- Item `C/07_H/prose/065` (`companion/chapters/07_H.tex:704-706`): "The limit is a minimizer,
and in fact the projection of $x_0$ onto $S^\perp$ in the $H_0^{-1}$ metric. It is independent
of the choices of admissible accepted lengths." With $x_*$ the limit (7.8.1) (a variable with its
defining equation): $x_*$ minimizes $F$; $x_*\in S^\perp$ and $x_*$ is the unique minimizer of
$(x-x_0)^TH_0^{-1}(x-x_0)$ over $x\in S^\perp$; and every admissible run on $F$ with the same
$x_0$ and $H_0$ (whatever its accepted lengths and line-search constants) converges to $x_*$. -/
theorem relint_limit_projection {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (S : Submodule ℝ (Vec n)) (hS : S = Submodule.span ℝ (Set.range a)) (P : Set (Vec n))
    (hP : P = convexHull ℝ (Set.range a)) (hri : (0 : S) ∈ interior {v : S | (v : Vec n) ∈ P})
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hUS : ∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x)
    (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (hxstar : xstar = R.x 0 - (R.H 0 * U * (Uᵀ * R.H 0 * U)⁻¹ * Uᵀ) *ᵥ R.x 0) :
    (∀ z, F xstar ≤ F z) ∧ (∀ v ∈ S, dot v xstar = 0) ∧
      (∀ x, (∀ v ∈ S, dot v x = 0) →
        dot (xstar - R.x 0) ((R.H 0)⁻¹ *ᵥ (xstar - R.x 0)) ≤
            dot (x - R.x 0) ((R.H 0)⁻¹ *ᵥ (x - R.x 0)) ∧
          (dot (x - R.x 0) ((R.H 0)⁻¹ *ᵥ (x - R.x 0)) =
              dot (xstar - R.x 0) ((R.H 0)⁻¹ *ᵥ (xstar - R.x 0)) ↔ x = xstar)) ∧
      ∀ R' : AdmissibleBFGSRun n F, R'.x 0 = R.x 0 → R'.H 0 = R.H 0 →
        Tendsto R'.x atTop (𝓝 xstar) := by
  have hri' := (relint_def a S hS P hP).mpr hri
  have hperp := perp_iff U S hUS
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  subst hS
  have hspan : ∀ x, x ∈ Submodule.span ℝ ((Finset.univ.image a : Finset (Vec n)) : Set (Vec n)) ↔
      ∃ z, U *ᵥ z = x := by
    rw [coe_image_univ]
    exact hUS
  obtain ⟨-, -, hzero, hiff, hmin⟩ := R.maxLinear_relativeInterior_complete _ hA hri' U hU hspan
  rw [(hat_definitions U (R.H 0) (R.x 0)).2.2, ← hxstar] at hzero hmin
  have hnn := Homogeneous.relativeInteriorZero_nonneg _ hA hri'
  refine ⟨fun z => hzero ▸ hnn z, (hperp xstar).mpr ((hiff xstar).mp hzero), fun x hx => ?_,
    fun R' hx0 hH0 => ?_⟩
  · exact hmin x ((hiff x).mpr ((hperp x).mp hx))
  · have h := (R'.maxLinear_relativeInterior_complete _ hA hri' U hU hspan).2.1
    rw [(hat_definitions U (R'.H 0) (R'.x 0)).2.2, hx0, hH0, ← hxstar] at h
    exact h

/-- Item `C/07_H/prose/066` (`companion/chapters/07_H.tex:706-708`): "This includes all finite
polyhedral seminorms and noncoercive gauges whose minimizer set is a linear subspace." For a
finite max-linear objective: if it is a seminorm, or if it is nonnegative (a gauge) and its set
of minimizers is a linear subspace, then $0\in\operatorname{relint}P$, so the theorem of
displays `C/07_H/disp/038`-`C/07_H/disp/039` applies. Library:
`Homogeneous.relativeInteriorZero_of_seminorm`,
`Homogeneous.relativeInteriorZero_iff_nonneg_linear_zero_fiber`. -/
theorem relint_includes_seminorms {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (S : Submodule ℝ (Vec n)) (hS : S = Submodule.span ℝ (Set.range a)) (P : Set (Vec n))
    (hP : P = convexHull ℝ (Set.range a)) :
    ((∃ p : Seminorm ℝ (Vec n), ∀ x, F x = p x) →
        (0 : S) ∈ interior {v : S | (v : Vec n) ∈ P}) ∧
      ((∀ x, 0 ≤ F x) → (∃ V : Submodule ℝ (Vec n), ∀ x, (∀ z, F x ≤ F z) ↔ x ∈ V) →
        (0 : S) ∈ interior {v : S | (v : Vec n) ∈ P}) := by
  have hrel := relint_def a S hS P hP
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  have h0 : Homogeneous.finiteMaxLinear _ hA 0 = 0 :=
    Homogeneous.value_zero (Homogeneous.finiteMaxLinear_homogeneous _ hA)
  refine ⟨fun ⟨p, hp⟩ => hrel.mp (Homogeneous.relativeInteriorZero_of_seminorm _ hA p hp),
    fun hn ⟨V, hV⟩ => hrel.mp ((Homogeneous.relativeInteriorZero_iff_nonneg_linear_zero_fiber _
      hA).mpr ⟨hn, V, fun x => ?_⟩)⟩
  rw [← hV]
  constructor
  · intro hx z
    rw [hx]
    exact hn z
  · intro hx
    exact le_antisymm (h0 ▸ hx 0) (hn x)

/-- Item `C/07_H/prose/067` (`companion/chapters/07_H.tex:710-714`): "The same argument applies
after a finite prefix if $0\in\operatorname{relint}\operatorname{conv}G$ for the recurrent
gradients. The projected tail objective is then coercive even if some original, nonrecurrent
slopes have disappeared. Formula (7.7.2) supplies the limit." With $G$ the recurrent gradients,
$0$ in the interior of $\operatorname{conv}G$ relative to $\operatorname{span}G$, and $U$ with
orthonormal columns spanning $\operatorname{span}G$: the tail objective
$z\mapsto\max_{g\in G}g^TUz$ satisfies $\max_{g\in G}g^TUz\ge\mu\|z\|$ for some $\mu>0$; and for
some $K$, $x_k\to x_K-H_KU(U^TH_KU)^{-1}U^Tx_K$ (formula (7.7.2), printed "(7.2)" before the
correction M17 of 15 October 2026, item `C/07_H/prose/028`). Library:
`AdmissibleBFGSRun.maxLinear_recurrent_relativeInterior_convergence`. -/
theorem recurrent_relint_convergence {n m r : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (R : AdmissibleBFGSRun n F) (G : Set (Vec n)) (hG : G = {v | ∃ᶠ k in atTop, R.g k = v})
    (hri : (0 : Submodule.span ℝ G) ∈
      interior {v : Submodule.span ℝ G | (v : Vec n) ∈ convexHull ℝ G})
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hUS : ∀ x, x ∈ Submodule.span ℝ G ↔ ∃ z, U *ᵥ z = x) :
    (∃ μ : ℝ, 0 < μ ∧ ∀ (z : Vec r) (M : ℝ), IsGreatest ((fun v => dot v (U *ᵥ z)) '' G) M →
        μ * ‖euclideanVector z‖ ≤ M) ∧
      ∃ K : ℕ, Tendsto R.x atTop (𝓝 (R.x K - (R.H K * U * (Uᵀ * R.H K * U)⁻¹ * Uᵀ) *ᵥ R.x K)) := by
  obtain ⟨hA, rfl⟩ := maxLinear_eq a F hF_def
  have hrange := R.maxLinear_gradient_range_finite _ hA
  have hfin : G.Finite := by
    rw [hG]
    exact Homogeneous.recurrentValues_finite R.g hrange
  have hGne : G.Nonempty := by
    rw [hG]
    exact Homogeneous.recurrentValues_nonempty R.g hrange
  have hBG : ((hfin.toFinset : Finset (Vec n)) : Set (Vec n)) = G := hfin.coe_toFinset
  have hB : hfin.toFinset.Nonempty := by
    rw [← Finset.coe_nonempty, hBG]
    exact hGne
  have hri' : Homogeneous.RelativeInteriorZero hfin.toFinset := by
    unfold Homogeneous.RelativeInteriorZero
    rw [hBG]
    exact hri
  have hspan : ∀ x, x ∈ Submodule.span ℝ ((hfin.toFinset : Finset (Vec n)) : Set (Vec n)) ↔
      ∃ z, U *ᵥ z = x := by
    rw [hBG]
    exact hUS
  have hBrec : ((hfin.toFinset : Finset (Vec n)) : Set (Vec n)) =
      Homogeneous.recurrentValues R.g := hBG.trans hG
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hμ, hbound⟩ :=
      Homogeneous.relativeInterior_euclidean_projection_bound _ hB hri' U hU hspan
    refine ⟨μ, hμ, fun z M hM => ?_⟩
    have hUz : Uᵀ *ᵥ (U *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    have hmax : IsGreatest ((fun v => dot v (U *ᵥ z)) '' G)
        (Homogeneous.finiteMaxLinear hfin.toFinset hB (U *ᵥ z)) := by
      refine ⟨?_, ?_⟩
      · obtain ⟨v, hv, he⟩ := Homogeneous.finiteMaxLinear_active hfin.toFinset hB (U *ᵥ z)
        exact ⟨v, (Set.Finite.mem_toFinset hfin).mp hv, he.symm⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact Homogeneous.slope_le_finiteMaxLinear _ hB ((Set.Finite.mem_toFinset hfin).mpr hv) _
    have h := hbound (U *ᵥ z)
    rw [hUz, hmax.unique hM] at h
    exact h
  · obtain ⟨K, hK, -, -⟩ := R.maxLinear_recurrent_relativeInterior_convergence _ _ hA hB hBrec hri'
      U hU hspan
    rw [(hat_definitions U (R.H K) (R.x K)).2.2] at hK
    exact ⟨K, hK⟩

/-- Item `C/07_H/prose/068` (`companion/chapters/07_H.tex:716-718`): "For $f\equiv0$, the
algorithm is already stationary; there is no nonzero-gradient infinite run. The projection
formula above concerns a nontrivial slope span." If $F\equiv0$, its gradient is zero at every
point (every point is stationary) and no admissible run exists. (The last sentence is a remark
on the scope of formula (7.8.1).) -/
theorem zero_objective_no_run {n : ℕ} (F : Vec n → ℝ) (hF : ∀ x, F x = 0) :
    (∀ x, HasFDerivAt F (gradientFunctional 0) x) ∧ IsEmpty (AdmissibleBFGSRun n F) := by
  refine ⟨fun x => ?_, ⟨fun R => R.identically_zero_no_infinite_run hF⟩⟩
  have hF' : F = fun _ => 0 := funext hF
  have h0 : gradientFunctional (0 : Vec n) = 0 := by
    ext v
    simp [gradientFunctional_apply, dot]
  rw [hF', h0]
  exact hasFDerivAt_const 0 x

/-! ### Non-vacuity

The examples below show that the standing assumptions of the theorems above can hold together
with an admissible run, including the anchor hypotheses of the block displays (`block_decrease`
etc.; witness `block_witness` below). One family of statements is about every admissible run on
objectives for which no admissible run is exhibited: the second part of Theorem 7.B
($0\notin\operatorname{aff}\{a_i\}$, `theorem_7B`) and the run statement on the common-tilt
family (`tilt_family_escape`; `tilt_model_gradients` is about gradients only). On many of these
objectives no admissible run exists, so the statements are vacuous there: slopes on one affine
line missing $0$ in any dimension (`maxLinear_line_no_run`), hence every objective of
Theorem 7.B (ii) in dimension at most two (`maxLinear_affine_free_no_run`), and the family with
$b_i$ on one line (`tilt_collinear_no_run`: at most two distinct pieces in any dimension, every
member in $\R^2$). For slopes not on one line (at least three pieces, dimension at least three)
existence is not known (`TiltNoInfiniteRunQuestion`). -/

/-! #### A witness for the anchor hypotheses of the block displays

An admissible run of $|u|+|v|$ whose first three steps form an opposite-gradient block between
two anchors: three explicit exact steps, prepended (`prependStep`) to an infinite admissible
run given by `AdmissibleRunExistence.exists_admissible_run` (whose hypotheses hold for $|u|+|v|$:
convex, bounded below, not differentiable only on the axes, which meet every line through a point
of differentiability in at most two points, and no point of differentiability has gradient
zero). -/

/-- Prepend one accepted step to an admissible run: from a point $x$ with gradient $g\ne0$ and
$H\succ0$, a length $\alpha>0$ whose step reaches the initial point of `R`, with the inverse-BFGS
update giving the initial matrix of `R` and Armijo and weak Wolfe for the constants of `R`, the
sequences $x,R.x_0,R.x_1,\dots$ (and likewise $g$, $H$, $\alpha$) form an admissible run. -/
def prependStep {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (x g : Vec n) (H : Mat n)
    (α : ℝ) (hH : H.PosDef) (hα : 0 < α) (hg0 : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    (hx : R.x 0 = x + bfgsStep H g α)
    (hH1 : R.H 0 = inverseBFGS H (bfgsStep H g α) (R.g 0 - g))
    (harm : F (R.x 0) ≤ F x + R.c₁ * dot g (bfgsStep H g α))
    (hwolfe : R.c₂ * dot g (bfgsStep H g α) ≤ dot (R.g 0) (bfgsStep H g α)) :
    AdmissibleBFGSRun n F where
  convex := R.convex
  x k := match k with
    | 0 => x
    | j + 1 => R.x j
  H k := match k with
    | 0 => H
    | j + 1 => R.H j
  g k := match k with
    | 0 => g
    | j + 1 => R.g j
  α k := match k with
    | 0 => α
    | j + 1 => R.α j
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := hH
  alpha_pos k := by
    cases k with
    | zero => exact hα
    | succ j => exact R.alpha_pos j
  gradient_nonzero k := by
    cases k with
    | zero => exact hg0
    | succ j => exact R.gradient_nonzero j
  hasGradient k := by
    cases k with
    | zero => exact hg
    | succ j => exact R.hasGradient j
  step k := by
    cases k with
    | zero => exact hx
    | succ j => exact R.step j
  update k := by
    cases k with
    | zero => exact hH1
    | succ j => exact R.update j
  armijo k := by
    cases k with
    | zero => exact harm
    | succ j => exact R.armijo j
  weak_wolfe k := by
    cases k with
    | zero => exact hwolfe
    | succ j => exact R.weak_wolfe j

/-- $F(u,v)=|u|+|v|$ on $\R^2$. -/
def absSum (x : Vec 2) : ℝ := |x 0| + |x 1|

/-- $|u|+|v|$ is convex. -/
theorem absSum_convex : ConvexOn ℝ univ absSum := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  simp only [absSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h0 : |a * x 0 + b * y 0| ≤ a * |x 0| + b * |y 0| := by
    calc |a * x 0 + b * y 0| ≤ |a * x 0| + |b * y 0| := abs_add_le _ _
      _ = a * |x 0| + b * |y 0| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h1 : |a * x 1 + b * y 1| ≤ a * |x 1| + b * |y 1| := by
    calc |a * x 1 + b * y 1| ≤ |a * x 1| + |b * y 1| := abs_add_le _ _
      _ = a * |x 1| + b * |y 1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  linarith

/-- A vector $\sigma$ with $\sigma_ix_i=|x_i|$ and $|\sigma_i|\le1$ is a subgradient of $|u|+|v|$
at $x$. -/
theorem absSum_support (x σ : Vec 2) (h0 : σ 0 * x 0 = |x 0|) (h1 : σ 1 * x 1 = |x 1|)
    (hs0 : |σ 0| ≤ 1) (hs1 : |σ 1| ≤ 1) : ∀ z, dot σ (z - x) ≤ absSum z - absSum x := by
  intro z
  have e : dot σ (z - x) = σ 0 * z 0 + σ 1 * z 1 - (σ 0 * x 0 + σ 1 * x 1) := by
    simp only [dot, Fin.sum_univ_two, Pi.sub_apply]
    ring
  rw [e, h0, h1]
  have k0 : σ 0 * z 0 ≤ |z 0| := by
    calc σ 0 * z 0 ≤ |σ 0 * z 0| := le_abs_self _
      _ = |σ 0| * |z 0| := abs_mul _ _
      _ ≤ 1 * |z 0| := mul_le_mul_of_nonneg_right hs0 (abs_nonneg _)
      _ = |z 0| := one_mul _
  have k1 : σ 1 * z 1 ≤ |z 1| := by
    calc σ 1 * z 1 ≤ |σ 1 * z 1| := le_abs_self _
      _ = |σ 1| * |z 1| := abs_mul _ _
      _ ≤ 1 * |z 1| := mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      _ = |z 1| := one_mul _
  simp only [absSum]
  linarith

/-- $|u|+|v|$ is differentiable off the coordinate axes. -/
theorem absSum_differentiableAt {x : Vec 2} (h0 : x 0 ≠ 0) (h1 : x 1 ≠ 0) :
    DifferentiableAt ℝ absSum x := by
  have hab : ∀ i : Fin 2, x i ≠ 0 → DifferentiableAt ℝ (fun y : Vec 2 => |y i|) x := by
    intro i hi
    have hp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).hasFDerivAt (x := x)
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact (hp.abs_of_neg hneg).differentiableAt
    · exact (hp.abs_of_pos hpos).differentiableAt
  exact (hab 0 h0).add (hab 1 h1)

/-- Off the axes the gradient of $|u|+|v|$ is the sign vector. -/
theorem absSum_hasGradient {x σ : Vec 2} (hx0 : x 0 ≠ 0) (hx1 : x 1 ≠ 0)
    (h0 : σ 0 * x 0 = |x 0|) (h1 : σ 1 * x 1 = |x 1|) (hs0 : |σ 0| ≤ 1) (hs1 : |σ 1| ≤ 1) :
    HasFDerivAt absSum (gradientFunctional σ) x := by
  have hd := hasFDerivAt_coordinateGradient (absSum_differentiableAt hx0 hx1)
  have he := supporting_vector_eq_gradient (absSum_support x σ h0 h1 hs0 hs1) hd
  rw [← he] at hd
  exact hd

/-- $|u|+|v|$ is not differentiable on the coordinate axes. -/
theorem absSum_not_differentiableAt {x : Vec 2} (hx : x 0 = 0 ∨ x 1 = 0) :
    ¬ DifferentiableAt ℝ absSum x := by
  intro hdiff
  have hd := hasFDerivAt_coordinateGradient hdiff
  have hsgn : ∀ r : ℝ, ∃ s : ℝ, s * r = |r| ∧ |s| ≤ 1 := by
    intro r
    rcases le_total 0 r with h | h
    · exact ⟨1, by rw [one_mul, abs_of_nonneg h], by norm_num⟩
    · exact ⟨-1, by rw [abs_of_nonpos h]; ring, by norm_num⟩
  rcases hx with h | h
  · obtain ⟨s, hs, hs1⟩ := hsgn (x 1)
    have e1 := supporting_vector_eq_gradient
      (absSum_support x ![1, s] (by simp [h]) (by simpa using hs) (by simp) (by simpa using hs1)) hd
    have e2 := supporting_vector_eq_gradient
      (absSum_support x ![-1, s] (by simp [h]) (by simpa using hs) (by simp)
        (by simpa using hs1)) hd
    have := congrFun (e1.trans e2.symm) 0
    norm_num at this
  · obtain ⟨s, hs, hs1⟩ := hsgn (x 0)
    have e1 := supporting_vector_eq_gradient
      (absSum_support x ![s, 1] (by simpa using hs) (by simp [h]) (by simpa using hs1) (by simp)) hd
    have e2 := supporting_vector_eq_gradient
      (absSum_support x ![s, -1] (by simpa using hs) (by simp [h]) (by simpa using hs1)
        (by simp)) hd
    have := congrFun (e1.trans e2.symm) 1
    norm_num at this


/-- Every line through a point of differentiability of $|u|+|v|$ meets its non-differentiability
set (the axes) in at most two points. -/
theorem absSum_line (x p : Vec 2) (hx : DifferentiableAt ℝ absSum x) (_hp : p ≠ 0) :
    {t : ℝ | ¬ DifferentiableAt ℝ absSum (x + t • p)}.Countable := by
  have hx0 : x 0 ≠ 0 := fun h => absSum_not_differentiableAt (Or.inl h) hx
  have hx1 : x 1 ≠ 0 := fun h => absSum_not_differentiableAt (Or.inr h) hx
  have hsub : {t : ℝ | ¬ DifferentiableAt ℝ absSum (x + t • p)} ⊆
      {t : ℝ | x 0 + t * p 0 = 0} ∪ {t : ℝ | x 1 + t * p 1 = 0} := by
    intro t ht
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    exact ht (absSum_differentiableAt (by simpa using hc.1) (by simpa using hc.2))
  have hsing : ∀ i : Fin 2, x i ≠ 0 → {t : ℝ | x i + t * p i = 0}.Subsingleton := by
    intro i hxi t ht t' ht'
    simp only [Set.mem_setOf_eq] at ht ht'
    by_cases hpi : p i = 0
    · rw [hpi, mul_zero, add_zero] at ht
      exact absurd ht hxi
    · have h : (t - t') * p i = 0 := by linear_combination ht - ht'
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hpi)
  exact ((hsing 0 hx0).countable.union (hsing 1 hx1).countable).mono hsub

/-- No point of differentiability of $|u|+|v|$ has gradient zero. -/
theorem absSum_no_stationary (y g : Vec 2) (hg : HasFDerivAt absSum (gradientFunctional g) y) :
    g ≠ 0 := by
  rintro rfl
  have h := convex_supporting_inequality absSum_convex hg 0
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  have hy : y 0 = 0 := by
    simp only [absSum, Pi.zero_apply, abs_zero, add_zero] at h
    have := abs_nonneg (y 1)
    exact abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))
  exact absSum_not_differentiableAt (Or.inl hy) hg.differentiableAt

/-- The matrices $H_0,H_1,H_2$ of the witness run of the block displays (see `block_witness`). -/
def bwH0 : Mat 2 := !![1, -1; -1, 2]
/-- $H_1$ of the witness run. -/
def bwH1 : Mat 2 := !![1, 0; 0, 2]
/-- $H_2$ of the witness run. -/
def bwH2 : Mat 2 := !![101 / 120, 19 / 60; 19 / 60, 41 / 30]

/-- The first step of the witness run: $s_0=-4H_0(1,1)=(0,-4)$. -/
theorem bw_step0 : bfgsStep bwH0 ![1, 1] 4 = ![0, -4] := by
  ext i
  fin_cases i <;> norm_num [bfgsStep, bwH0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- $H_1$ is the inverse-BFGS update of $H_0$. -/
theorem bw_update0 : inverseBFGS bwH0 ![0, -4] (![1, -1] - ![1, 1]) = bwH1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseBFGS, bwH0, bwH1, outer, dot, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

/-- The second step: $s_1=-\frac{21}{20}H_1(1,-1)=(-\frac{21}{20},\frac{21}{10})$. -/
theorem bw_step1 : bfgsStep bwH1 ![1, -1] (21 / 20) = ![-21 / 20, 21 / 10] := by
  ext i
  fin_cases i <;> norm_num [bfgsStep, bwH1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- $H_2$ is the inverse-BFGS update of $H_1$. -/
theorem bw_update1 : inverseBFGS bwH1 ![-21 / 20, 21 / 10] (![-1, 1] - ![1, -1]) = bwH2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseBFGS, bwH1, bwH2, outer, dot, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

/-- The third step: $s_2=-\frac1{10}H_2(-1,1)=(\frac{21}{400},-\frac{21}{200})$. -/
theorem bw_step2 : bfgsStep bwH2 ![-1, 1] (1 / 10) = ![21 / 400, -21 / 200] := by
  ext i
  fin_cases i <;> norm_num [bfgsStep, bwH2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]


/-- $H_0=A^TA$, $A=\begin{pmatrix}1&-1\\0&1\end{pmatrix}$, is positive definite. -/
theorem bwH0_posDef : bwH0.PosDef := by
  have hA : Function.Injective (!![1, -1; 0, 1] : Mat 2).mulVec := by
    apply Function.LeftInverse.injective (g := (!![1, 1; 0, 1] : Mat 2).mulVec)
    intro v
    rw [Matrix.mulVec_mulVec]
    have e : (!![1, 1; 0, 1] : Mat 2) * !![1, -1; 0, 1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    rw [e, Matrix.one_mulVec]
  have h := metricGram_posDef (Matrix.PosDef.one (n := Fin 2) (R := ℝ)) hA
  have e : metricGram 1 (!![1, -1; 0, 1] : Mat 2) = bwH0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [metricGram, bwH0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  rwa [e] at h

/-- $|u|+|v|=\max(u+v,u-v,-u+v,-u-v)$: the finite max-linear objective with four slopes. -/
theorem absSum_isGreatest (x : Vec 2) :
    IsGreatest (Set.range fun i =>
      dot ((![![1, 1], ![1, -1], ![-1, 1], ![-1, -1]] : Fin 4 → Vec 2) i) x) (absSum x) := by
  have e : ∀ a b : ℝ, dot (![a, b] : Vec 2) x = a * x 0 + b * x 1 := fun a b => by
    simp [dot, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · rcases abs_choice (x 0) with h0 | h0 <;> rcases abs_choice (x 1) with h1 | h1
    · exact ⟨0, by change dot ![1, 1] x = _; rw [e, absSum, h0, h1]; ring⟩
    · exact ⟨1, by change dot ![1, -1] x = _; rw [e, absSum, h0, h1]; ring⟩
    · exact ⟨2, by change dot ![-1, 1] x = _; rw [e, absSum, h0, h1]; ring⟩
    · exact ⟨3, by change dot ![-1, -1] x = _; rw [e, absSum, h0, h1]; ring⟩
  · rintro _ ⟨i, rfl⟩
    have a0 := le_abs_self (x 0)
    have a1 := le_abs_self (x 1)
    have b0 := neg_le_abs (x 0)
    have b1 := neg_le_abs (x 1)
    fin_cases i
    · change dot ![1, 1] x ≤ absSum x
      rw [e, absSum]
      linarith
    · change dot ![1, -1] x ≤ absSum x
      rw [e, absSum]
      linarith
    · change dot ![-1, 1] x ≤ absSum x
      rw [e, absSum]
      linarith
    · change dot ![-1, -1] x ≤ absSum x
      rw [e, absSum]
      linarith

/-- $|u|+|v|$ is positively homogeneous of degree one. -/
theorem absSum_homogeneous : Homogeneous.PositiveDegreeOne absSum := by
  intro t ht x
  simp only [absSum, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  ring

/-- An admissible run of $F(u,v)=|u|+|v|$ with $c_1=1/4$, $c_2=1/2$ whose first iterates are
$x_0=(1,3)$, $x_1=(1,-1)$, $x_2=(-\frac1{20},\frac{11}{10})$,
$x_3=(\frac1{400},\frac{199}{200})$ with gradients $(1,1)$, $(1,-1)$, $(-1,1)$, $(1,1)$ (exact
rational steps with $\alpha_0=4$, $\alpha_1=\frac{21}{20}$, $\alpha_2=\frac1{10}$), continued by
the existence theorem `AdmissibleRunExistence.exists_admissible_run` from $(x_3,H_3)$. -/
theorem bw_run_exists :
    ∃ R : AdmissibleBFGSRun 2 absSum,
      R.x 0 = ![1, 3] ∧ R.x 1 = ![1, -1] ∧ R.x 2 = ![-1 / 20, 11 / 10] ∧
      R.x 3 = ![1 / 400, 199 / 200] ∧
      R.g 0 = ![1, 1] ∧ R.g 1 = ![1, -1] ∧ R.g 2 = ![-1, 1] ∧ R.g 3 = ![1, 1] ∧
      R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 := by
  have hgrad : ∀ (x σ : Vec 2), x 0 ≠ 0 → x 1 ≠ 0 → σ 0 * x 0 = |x 0| → σ 1 * x 1 = |x 1| →
      |σ 0| ≤ 1 → |σ 1| ≤ 1 → HasFDerivAt absSum (gradientFunctional σ) x :=
    fun x σ h0 h1 e0 e1 s0 s1 => absSum_hasGradient h0 h1 e0 e1 s0 s1
  have hg0 : HasFDerivAt absSum (gradientFunctional ![1, 1]) ![1, 3] :=
    hgrad _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hg1 : HasFDerivAt absSum (gradientFunctional ![1, -1]) ![1, -1] :=
    hgrad _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hg2 : HasFDerivAt absSum (gradientFunctional ![-1, 1]) ![-1 / 20, 11 / 10] :=
    hgrad _ _ (by norm_num) (by norm_num) (by norm_num [abs_of_neg]) (by norm_num [abs_of_pos])
      (by norm_num) (by norm_num)
  have hg3 : HasFDerivAt absSum (gradientFunctional ![1, 1]) ![1 / 400, 199 / 200] :=
    hgrad _ _ (by norm_num) (by norm_num) (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
      (by norm_num) (by norm_num)
  have hne : ∀ a b : ℝ, a ≠ 0 → (![a, b] : Vec 2) ≠ 0 := fun a b ha h => ha (by
    simpa using congrFun h 0)
  have hH1 : bwH1.PosDef := by
    rw [← bw_update0, ← bw_step0]
    exact inverseBFGS_posDef bwH0_posDef _ _ (by
      rw [bw_step0]; norm_num [dot, Fin.sum_univ_two])
  have hH2 : bwH2.PosDef := by
    rw [← bw_update1, ← bw_step1]
    exact inverseBFGS_posDef hH1 _ _ (by
      rw [bw_step1]; norm_num [dot, Fin.sum_univ_two])
  have hH3 : (inverseBFGS bwH2 (bfgsStep bwH2 ![-1, 1] (1 / 10)) (![1, 1] - ![-1, 1])).PosDef :=
    inverseBFGS_posDef hH2 _ _ (by rw [bw_step2]; norm_num [dot, Fin.sum_univ_two])
  have hbdd : BddBelow (range absSum) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
  obtain ⟨R3, hx3, hgr3, hHR3, hc1, hc2⟩ := AdmissibleRunExistence.exists_admissible_run
    absSum_convex hbdd absSum_line absSum_no_stationary hg3 hH3
    (c₁ := 1 / 4) (c₂ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hx3' : R3.x 0 = ![-1 / 20, 11 / 10] + bfgsStep bwH2 ![-1, 1] (1 / 10) := by
    rw [hx3, bw_step2]
    ext i
    fin_cases i <;> norm_num
  have hH3' : R3.H 0 = inverseBFGS bwH2 (bfgsStep bwH2 ![-1, 1] (1 / 10)) (R3.g 0 - ![-1, 1]) := by
    rw [hHR3, hgr3]
  have harm3 : absSum (R3.x 0) ≤ absSum ![-1 / 20, 11 / 10] +
      R3.c₁ * dot ![-1, 1] (bfgsStep bwH2 ![-1, 1] (1 / 10)) := by
    rw [hx3, hc1, bw_step2]
    norm_num [absSum, dot, Fin.sum_univ_two, abs_of_pos, abs_of_neg]
  have hwol3 : R3.c₂ * dot ![-1, 1] (bfgsStep bwH2 ![-1, 1] (1 / 10)) ≤
      dot (R3.g 0) (bfgsStep bwH2 ![-1, 1] (1 / 10)) := by
    rw [hgr3, hc2, bw_step2]
    norm_num [dot, Fin.sum_univ_two]
  let R2 := prependStep R3 ![-1 / 20, 11 / 10] ![-1, 1] bwH2 (1 / 10) hH2 (by norm_num)
    (hne _ _ (by norm_num)) hg2 hx3' hH3' harm3 hwol3
  have hx2' : R2.x 0 = ![1, -1] + bfgsStep bwH1 ![1, -1] (21 / 20) := by
    change ![-1 / 20, 11 / 10] = _
    rw [bw_step1]
    ext i
    fin_cases i <;> norm_num
  have hH2' : R2.H 0 = inverseBFGS bwH1 (bfgsStep bwH1 ![1, -1] (21 / 20)) (R2.g 0 - ![1, -1]) := by
    change bwH2 = inverseBFGS bwH1 (bfgsStep bwH1 ![1, -1] (21 / 20)) (![-1, 1] - ![1, -1])
    rw [bw_step1, bw_update1]
  have harm2 : absSum (R2.x 0) ≤ absSum ![1, -1] +
      R2.c₁ * dot ![1, -1] (bfgsStep bwH1 ![1, -1] (21 / 20)) := by
    change absSum ![-1 / 20, 11 / 10] ≤ absSum ![1, -1] +
      R3.c₁ * dot ![1, -1] (bfgsStep bwH1 ![1, -1] (21 / 20))
    rw [hc1, bw_step1]
    norm_num [absSum, dot, Fin.sum_univ_two, abs_of_pos, abs_of_neg]
  have hwol2 : R2.c₂ * dot ![1, -1] (bfgsStep bwH1 ![1, -1] (21 / 20)) ≤
      dot (R2.g 0) (bfgsStep bwH1 ![1, -1] (21 / 20)) := by
    change R3.c₂ * dot ![1, -1] (bfgsStep bwH1 ![1, -1] (21 / 20)) ≤
      dot ![-1, 1] (bfgsStep bwH1 ![1, -1] (21 / 20))
    rw [hc2, bw_step1]
    norm_num [dot, Fin.sum_univ_two]
  let R1 := prependStep R2 ![1, -1] ![1, -1] bwH1 (21 / 20) hH1 (by norm_num)
    (hne _ _ (by norm_num)) hg1 hx2' hH2' harm2 hwol2
  have hx1' : R1.x 0 = ![1, 3] + bfgsStep bwH0 ![1, 1] 4 := by
    change ![1, -1] = _
    rw [bw_step0]
    ext i
    fin_cases i <;> norm_num
  have hH1' : R1.H 0 = inverseBFGS bwH0 (bfgsStep bwH0 ![1, 1] 4) (R1.g 0 - ![1, 1]) := by
    change bwH1 = inverseBFGS bwH0 (bfgsStep bwH0 ![1, 1] 4) (![1, -1] - ![1, 1])
    rw [bw_step0, bw_update0]
  have harm1 : absSum (R1.x 0) ≤
      absSum ![1, 3] + R1.c₁ * dot ![1, 1] (bfgsStep bwH0 ![1, 1] 4) := by
    change absSum ![1, -1] ≤ absSum ![1, 3] + R3.c₁ * dot ![1, 1] (bfgsStep bwH0 ![1, 1] 4)
    rw [hc1, bw_step0]
    norm_num [absSum, dot, Fin.sum_univ_two]
  have hwol1 : R1.c₂ * dot ![1, 1] (bfgsStep bwH0 ![1, 1] 4) ≤
      dot (R1.g 0) (bfgsStep bwH0 ![1, 1] 4) := by
    change R3.c₂ * dot ![1, 1] (bfgsStep bwH0 ![1, 1] 4) ≤ dot ![1, -1] (bfgsStep bwH0 ![1, 1] 4)
    rw [hc2, bw_step0]
    norm_num [dot, Fin.sum_univ_two]
  let R0 := prependStep R1 ![1, 3] ![1, 1] bwH0 4 bwH0_posDef (by norm_num)
    (hne _ _ (by norm_num)) hg0 hx1' hH1' harm1 hwol1
  exact ⟨R0, rfl, rfl, rfl, hx3, rfl, rfl, rfl, hgr3, hc1, hc2⟩


/-- The standing assumptions of the block displays `C/07_H/disp/032`-`036` hold with the anchor
hypotheses: for $F(u,v)=|u|+|v|$ and the run of `bw_run_exists`, $f_k\to0$, the transitions
$0$ and $2$ are independent ($x_1$, $x_3$ are consecutive anchors, $a=1$, $b=3$), the transition
$1$ is dependent, and $g_2=-g_1$ ($g=g_1$, $\kappa=1$). -/
theorem block_witness :
    ∃ (slopes : Fin 4 → Vec 2) (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F),
      (∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x)) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ 1 ≤ 1 ∧ 1 + 2 ≤ 3 ∧
      LinearIndependent ℝ ![R.g (1 - 1), R.g 1] ∧ LinearIndependent ℝ ![R.g (3 - 1), R.g 3] ∧
      (∀ l, 1 ≤ l → l + 2 ≤ 3 → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)]) ∧
      R.g (1 + 1) = -(1 : ℝ) • R.g 1 := by
  obtain ⟨R, -, -, -, -, h0, h1, h2, h3, -, -⟩ := bw_run_exists
  have hv : Tendsto (fun k => absSum (R.x k)) atTop (𝓝 0) :=
    (R.homogeneous_bounded_below_convergence absSum_homogeneous 0
      (fun x => add_nonneg (abs_nonneg _) (abs_nonneg _))).2.2
  refine ⟨_, absSum, R, absSum_isGreatest, hv, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [show (1 : ℕ) - 1 = 0 from rfl, h0, h1, linearIndependent_pair_iff]
    norm_num [HomogeneousPlanar.pairDet]
  · rw [show (3 : ℕ) - 1 = 2 from rfl, h2, h3, linearIndependent_pair_iff]
    norm_num [HomogeneousPlanar.pairDet]
  · intro l hl1 hl2
    have hl : l = 1 := by omega
    subst hl
    rw [h1, linearIndependent_pair_iff]
    norm_num [HomogeneousPlanar.pairDet, h2]
  · rw [h2, h1]
    ext i
    fin_cases i <;> norm_num

/-- $|x|=\max(x,-x)$ on $\R$: the finite max-linear objective with the slopes $1,-1$. -/
theorem abs_isGreatest (x : Vec 1) :
    IsGreatest (Set.range fun i =>
      dot ((![OneDimensional.embed 1, OneDimensional.embed (-1)] : Fin 2 → Vec 1) i) x) (|x 0|) := by
  have h0 : dot (OneDimensional.embed 1) x = x 0 := by simp [dot]
  have h1 : dot (OneDimensional.embed (-1)) x = -x 0 := by simp [dot]
  refine ⟨?_, ?_⟩
  · rcases abs_choice (x 0) with h | h
    · exact ⟨0, show dot (OneDimensional.embed 1) x = |x 0| by rw [h0, h]⟩
    · exact ⟨1, show dot (OneDimensional.embed (-1)) x = |x 0| by rw [h1, h]⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · show dot (OneDimensional.embed 1) x ≤ |x 0|
      rw [h0]
      exact le_abs_self _
    · show dot (OneDimensional.embed (-1)) x ≤ |x 0|
      rw [h1]
      exact neg_le_abs _

/-- The recurrent gradients of `Master.absVRun 1 1` are the two slopes $(0,1)$, $(0,-1)$ of
$|v|$. -/
theorem absVRun_recurrent :
    {v | ∃ᶠ k in atTop, (BfgsCoverage.Article.Master.absVRun 1 1 one_pos).g k = v} =
      Set.range (![![0, 1], ![0, -1]] : Fin 2 → Vec 2) := by
  have hg : ∀ k, (BfgsCoverage.Article.Master.absVRun 1 1 one_pos).g k =
      ![0, (-1 : ℝ) ^ k] := fun k => BfgsCoverage.Article.Master.axisRun_g 1 one_pos k
  ext v
  constructor
  · intro hv
    obtain ⟨k, hk⟩ := hv.exists
    rw [hg] at hk
    rcases BfgsCoverage.Article.Global.neg_one_pow_cases k with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨0, by rw [← hk, h]; rfl⟩
    · exact ⟨1, by rw [← hk, h]; rfl⟩
  · rintro ⟨i, rfl⟩
    rw [Set.mem_setOf_eq, frequently_atTop]
    intro N
    fin_cases i
    · refine ⟨2 * N, by omega, ?_⟩
      rw [hg, pow_mul]
      norm_num
    · refine ⟨2 * N + 1, by omega, ?_⟩
      rw [hg, pow_succ, pow_mul]
      norm_num

/-- The hypotheses of Theorem 7.A and of its consequences (items `prose/007`-`prose/009`,
`prose/026`, `prose/034`, `prose/035`), of the displays of Sections 7.5.2-7.5.3 (with a finite
value limit), of the first part of Theorem 7.B and of item `prose/016` hold together:
$F(x)=|x|=\max(x,-x)$ on $\R$ is finite, convex, positively homogeneous, bounded below,
coercive, with bounded sublevels, and its admissible run `Global.absRun` ($x_k=(-1/2)^k$) has
$F(x_k)\to0$. -/
example : ∃ (F : Vec 1 → ℝ) (a : Fin 2 → Vec 1),
    ConvexOn ℝ univ F ∧ Homogeneous.PositiveDegreeOne F ∧
      (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) ∧
      (∃ L : ℝ, ∀ x, L ≤ F x) ∧ Tendsto F (cocompact (Vec 1)) atTop ∧
      (∀ c : ℝ, Bornology.IsBounded {x | F x ≤ c}) ∧
      ∃ R : AdmissibleBFGSRun 1 F, Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧
        Module.finrank ℝ (Submodule.span ℝ {v | ∃ᶠ k in atTop, R.g k = v}) ≤ 2 := by
  have hgr := abs_isGreatest
  obtain ⟨hconv, hhom⟩ :=
    BfgsCoverage.Article.Global.maxLinear_convex_homogeneous _ (fun x : Vec 1 => |x 0|) hgr
  have hzero : ∀ x : Vec 1, x 0 = 0 → x = 0 := by
    intro x h0
    ext i
    rw [Subsingleton.elim i 0]
    exact h0
  have hpos : ∀ x : Vec 1, x ≠ 0 → 0 < |x 0| :=
    fun x hx => abs_pos.mpr (fun h0 => hx (hzero x h0))
  have hcoer := BfgsCoverage.Article.Global.coercive_of_positive le_rfl hconv hhom hpos
  have hbdd : ∃ L : ℝ, ∀ x : Vec 1, L ≤ |x 0| := ⟨0, fun x => abs_nonneg _⟩
  let R := BfgsCoverage.Article.Global.absRun (fun x : Vec 1 => |x 0|) (fun _ => rfl)
  refine ⟨_, _, hconv, hhom, hgr, hbdd, hcoer, fun c => ?_, R,
    (bounded_below_consequence hconv hhom hbdd).2 R, ?_⟩
  · exact (BfgsCoverage.Article.Global.sublevels_compact_of_coercive (convex_continuous hconv)
      hcoer c).isBounded
  · exact (Submodule.finrank_le _).trans (by simp)

/-- The hypotheses of Theorem 7.C and of its first alternative hold with an admissible run: the
three-piece seed objective (unbounded below) and its run `SeedOrbit.run` with $c_1=1/4$,
$c_2=1/2$ (also item `prose/014`). The same run has three recurrent gradients spanning
$\R^2$ (`seed_cardinality_sharp`). -/
example : ∃ (a : Fin 3 → Vec 2) (F : Vec 2 → ℝ),
    (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) ∧ ¬ BddBelow (Set.range F) ∧
      ∃ R : AdmissibleBFGSRun 2 F, Tendsto R.x atTop (𝓝 0) ∧
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) :=
  ⟨_, _, seed_isGreatest, seed_unbounded,
    SeedOrbit.run (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (seed_attains_first_alternative.2.2.2 _ _ _ _ _ _).1,
    (seed_attains_first_alternative.2.2.2 _ _ _ _ _ _).2.1⟩

/-- The hypotheses of Lemma 7.3, of `lemma_7_3_value_limit` and of `recurrent_cardinality` (and
those of the in-proof forms of displays `disp/025`, `disp/026` up to the assumption
$0\notin\operatorname{aff}G$ of the proof by contradiction) hold: the data of the admissible
run `Global.absRun` of $|x|$. -/
example : ∃ (F : Vec 1 → ℝ) (x : ℕ → Vec 1) (H : ℕ → Mat 1) (g : ℕ → Vec 1) (α : ℕ → ℝ)
    (c₁ c₂ : ℝ), 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧ (H 0).PosDef ∧ (∀ k, 0 < α k) ∧ (∀ k, g k ≠ 0) ∧
      (∀ k, HasFDerivAt F (gradientFunctional (g k)) (x k)) ∧
      (∀ k, x (k + 1) = x k + bfgsStep (H k) (g k) (α k)) ∧
      (∀ k, H (k + 1) = inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k)) ∧
      (∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (bfgsStep (H k) (g k) (α k))) ∧
      (∀ k, dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)) ≥
        c₂ * dot (g k) (bfgsStep (H k) (g k) (α k))) ∧
      (Set.range g).Finite ∧ (∃ L : ℝ, ∀ k, L ≤ F (x k)) ∧
      ∃ L : ℝ, Tendsto (fun k => F (x k)) atTop (𝓝 L) := by
  let R := BfgsCoverage.Article.Global.absRun (fun x : Vec 1 => |x 0|) (fun _ => rfl)
  obtain ⟨hA, hFeq⟩ := maxLinear_eq _ (fun x : Vec 1 => |x 0|) abs_isGreatest
  obtain ⟨hconv, hhom⟩ := BfgsCoverage.Article.Global.maxLinear_convex_homogeneous _
    (fun x : Vec 1 => |x 0|) abs_isGreatest
  exact ⟨_, R.x, R.H, R.g, R.α, R.c₁, R.c₂, R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one, R.initial_posDef,
    R.alpha_pos, R.gradient_nonzero, R.hasGradient, R.step, R.update, R.armijo, R.weak_wolfe,
    (R.congrObjective hFeq).maxLinear_gradient_range_finite _ hA, ⟨0, fun k => abs_nonneg _⟩,
    ⟨0, (bounded_below_consequence hconv hhom ⟨0, fun x => abs_nonneg _⟩).2 R⟩⟩

/-- The general forms of displays `disp/025` and `disp/026` are satisfiable: $G=\{(1)\}$ in
$\R^1$; and one BFGS update with $H=I$, $g=(1,1)$, $g'=(-1,1)$, $\alpha=1$, $v=(0,1)$
(the gradients of $|u|+t$). -/
example : (∃ G : Set (Vec 1), G.Nonempty ∧ (0 : Vec 1) ∉ affineSpan ℝ G) ∧
    ∃ (H : Mat 2) (g g' v : Vec 2) (α : ℝ), H.PosDef ∧ g ≠ 0 ∧ 0 < α ∧
      0 < dot (g' - g) (bfgsStep H g α) ∧ dot v g = 1 ∧ dot v g' = 1 := by
  refine ⟨⟨{![1]}, Set.singleton_nonempty _, fun h => ?_⟩,
    ⟨1, ![1, 1], ![-1, 1], ![0, 1], 1, Matrix.PosDef.one, fun h => ?_, one_pos, ?_, ?_, ?_⟩⟩
  · rw [AffineSubspace.mem_affineSpan_singleton] at h
    have := congrFun h 0
    simp at this
  · have := congrFun h 0
    simp at this
  · simp [dot, bfgsStep, Fin.sum_univ_two]
  · simp [dot, Fin.sum_univ_two]
  · simp [dot, Fin.sum_univ_two]

/-- The hypothesis of the common-tilt family is satisfiable: $F(u,t)=t$ is $t+\max_ib_i^Tu$ for
the single slope $b_1=0$ (a linear objective, with no admissible run: `tilt_two_values_no_run`;
see the section "Non-vacuity"). -/
example : ∃ (b : Fin 1 → Vec 1) (F : Vec 2 → ℝ), ∀ (u : Vec 1) (t : ℝ),
    IsGreatest (Set.range fun i => t + dot (b i) u) (F (Fin.snoc u t)) := by
  refine ⟨fun _ => 0, fun x => x (Fin.last 1), fun u t => ⟨⟨0, ?_⟩, ?_⟩⟩
  · show t + dot (0 : Vec 1) u = (Fin.snoc u t : Vec 2) (Fin.last 1)
    rw [Fin.snoc_last]
    simp [dot]
  · rintro _ ⟨i, rfl⟩
    show t + dot (0 : Vec 1) u ≤ (Fin.snoc u t : Vec 2) (Fin.last 1)
    rw [Fin.snoc_last]
    simp [dot]

/-- The standing assumptions of Sections 7.7.1-7.7.2, of `block_general` and of Section 7.8
(also with recurrent gradients, item `prose/067`) hold together: $F(u,v)=|v|=\max(v,-v)$ on
$\R^2$, its admissible run `Master.absVRun 1 1` (gradients $(0,\pm1)$, values $\to0$), the
column $U=e_2$ spanning $S=\operatorname{span}\{(0,1),(0,-1)\}$ with $K=0$, the block $a=0$,
$b=2$ with $g=g_0=(0,1)$, $g_1=-g_0$ ($\kappa=1$), $0\in\operatorname{relint}P$, and the
recurrent gradients $G=\{(0,1),(0,-1)\}$ with $U$ spanning $\operatorname{span}G$ and
$0\in\operatorname{relint}\operatorname{conv}G$. -/
example : ∃ (a : Fin 2 → Vec 2) (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F)
    (U : Matrix (Fin 2) (Fin 1) ℝ) (S : Submodule ℝ (Vec 2)),
    (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Uᵀ * U = 1 ∧ (∀ x, x ∈ S ↔ ∃ z, U *ᵥ z = x) ∧
      (∀ k, 0 ≤ k → R.g k ∈ S) ∧ S = Submodule.span ℝ (Set.range a) ∧
      (0 : S) ∈ interior {v : S | (v : Vec 2) ∈ convexHull ℝ (Set.range a)} ∧
      0 + 2 ≤ 2 ∧ R.g (0 + 1) = -(1 : ℝ) • R.g 0 ∧
      {v | ∃ᶠ k in atTop, R.g k = v} = Set.range a ∧
      (∀ x, x ∈ Submodule.span ℝ {v | ∃ᶠ k in atTop, R.g k = v} ↔ ∃ z, U *ᵥ z = x) ∧
      (0 : Submodule.span ℝ {v | ∃ᶠ k in atTop, R.g k = v}) ∈
        interior {v : Submodule.span ℝ {v | ∃ᶠ k in atTop, R.g k = v} |
          (v : Vec 2) ∈ convexHull ℝ {v | ∃ᶠ k in atTop, R.g k = v}} := by
  let a : Fin 2 → Vec 2 := ![![0, 1], ![0, -1]]
  let U : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
  let R := BfgsCoverage.Article.Master.absVRun 1 1 one_pos
  have hg : ∀ k, R.g k = ![0, (-1 : ℝ) ^ k] := fun k =>
    BfgsCoverage.Article.Master.axisRun_g 1 one_pos k
  have hgr : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (BfgsCoverage.Article.Master.absV x) :=
    absV_isGreatest
  have hUa : ∀ z : Vec 1, U *ᵥ z = z 0 • a 0 := by
    intro z
    ext i
    fin_cases i <;> simp [U, a, Matrix.mulVec, dotProduct]
  have hS : ∀ x, x ∈ Submodule.span ℝ (Set.range a) ↔ ∃ z, U *ᵥ z = x := by
    intro x
    constructor
    · intro hx
      have hle : Submodule.span ℝ (Set.range a) ≤ LinearMap.range U.mulVecLin := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨![1], by rw [Matrix.mulVecLin_apply, hUa]; simp⟩
        · exact ⟨![-1], by rw [Matrix.mulVecLin_apply, hUa]; ext j; fin_cases j <;> simp [a]⟩
      obtain ⟨z, hz⟩ := hle hx
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      rw [hUa]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  have hFeq : ∀ x, BfgsCoverage.Article.Master.absV x = (normSeminorm ℝ ℝ).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x := by
    intro x
    simp [BfgsCoverage.Article.Master.absV, Real.norm_eq_abs]
  have hrec : {v | ∃ᶠ k in atTop, R.g k = v} = Set.range a := absVRun_recurrent
  have hri := (relint_includes_seminorms a _ hgr _ rfl _ rfl).1 ⟨_, hFeq⟩
  refine ⟨a, _, R, U, Submodule.span ℝ (Set.range a), hgr, ?_, ?_, hS, fun k _ => ?_, rfl,
    hri, le_rfl, ?_, hrec, by rw [hrec]; exact hS, by rw [hrec]; exact hri⟩
  · have h := ((continuous_abs.comp (continuous_apply 1)).tendsto _).comp absVRun_tendsto
    simpa [Function.comp_def, BfgsCoverage.Article.Master.absV] using h
  · ext i j
    fin_cases i
    fin_cases j
    simp [U, Matrix.mul_apply]
  · rw [hg]
    rcases BfgsCoverage.Article.Global.neg_one_pow_cases k with ⟨h, -⟩ | ⟨h, -⟩
    · exact Submodule.subset_span ⟨0, by rw [h]; rfl⟩
    · exact Submodule.subset_span ⟨1, by rw [h]; rfl⟩
  · rw [hg, hg]
    ext i
    fin_cases i <;> simp

/-- The standing assumptions of the in-proof block displays (`block_decrease`, `block_contraction`,
`block_window`, `block_endpoint_difference`, `block_parameter_bound`), including the anchor
hypotheses, hold together: `block_witness` ($F(u,v)=|u|+|v|$, $a=1$, $b=3$, $g=g_1$,
$\kappa=1$). -/
example : ∃ (slopes : Fin 4 → Vec 2) (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F),
    (∀ x, IsGreatest (Set.range fun i => dot (slopes i) x) (F x)) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧
      ∃ (a b : ℕ) (g : Vec 2) (κ : ℝ), 1 ≤ a ∧ a + 2 ≤ b ∧
        LinearIndependent ℝ ![R.g (a - 1), R.g a] ∧ LinearIndependent ℝ ![R.g (b - 1), R.g b] ∧
        (∀ l, a ≤ l → l + 2 ≤ b → ¬ LinearIndependent ℝ ![R.g l, R.g (l + 1)]) ∧
        g = R.g a ∧ 0 < κ ∧ R.g (a + 1) = -κ • g := by
  obtain ⟨slopes, F, R, hF, hv, -, -, ha, hb, hdep, hopp⟩ := block_witness
  exact ⟨slopes, F, R, hF, hv, 1, 3, R.g 1, 1, le_rfl, le_rfl, ha, hb, hdep, rfl, one_pos, hopp⟩

end BfgsCoverage.Companion.Ch07H
