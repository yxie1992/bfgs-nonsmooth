import BfgsArticle.Coverage.Article.Failure
import BfgsVerification.AlgebraicSeedJacobian
import BfgsVerification.EReconstructionFacts
import BfgsVerification.HessianUpdate
import BfgsVerification.PositiveUpdate
import BfgsVerification.DScalarSmallBounds

/-!
# Lean coverage: `companion/chapters/12_D.tex`

Chapter `comp:D` of the companion ("The exact deterministic seed and local smooth embedding").
Register: `editorial/lean_coverage/register/C_12_D.json`. The finite rational certificate that
the chapter cites (Appendix `comp:seed_certificate`) is covered in
`BfgsCoverage.Companion.SeedCertificate`; this module does not import it (and it does not import
this one). Results that the article states word for word are `SAME_AS` the article items in the
register; this module imports `BfgsCoverage.Article.Failure` and reuses its definitions.

## The specified implementation (lines 25-45)

The chapter's line search is strict: Armijo $F(x+\alpha p)<F(x)+c_1\alpha g^Tp$ and weak Wolfe
$\nabla F(x+\alpha p)^Tp>c_2g^Tp$ (`D:tests`). In Lean it is
`DeterministicLineSearch.fromMetric F x H c₁ c₂ N` (`specified_search`, `strict_tests`): at a
differentiable point it uses $g=\nabla F(x)$ and $p=-Hg$, starts with $\ell=0$, $h=+\infty$
(`none`), $\alpha=1$, tests Armijo first and weak Wolfe second, bisects after an Armijo rejection
and doubles (or bisects once $h<\infty$) after a Wolfe rejection, and returns the accepted length
with the list of all trial lengths; an exhausted budget `N` is failure. The budget only bounds the
number of trials (`fromMetric_fuel_mono`), and a run produced by the implementation is determined
by its initial point and matrix (`implemented_run_unique`). (The article's search is the
non-strict `NonStrictLineSearch`; its helpers are duplicated here for the strict search.) A run
is an `AdmissibleBFGSRun` (full step and full update `D:bfgs` at every step, `no_reset`).

## Constants (M11)

The article's discrepancy M11 (Lemma `art:seed_cycle` without a range of $(c_1,c_2)$; corrected in
the article on 15 October 2026) does not recur: the chapter fixes $c_1=10^{-4}$, $c_2=1/2$ for
Theorem `D:main` (line 52) and for the table
(line 204), and states the extension to every $0<c_1\le1/3$, $c_1<c_2<1$ (lines 57-60, 233), which
holds (`main`, `trial_table`, `trial_tree_all`). Strict Armijo holds at the accepted trial of phase
$j$ exactly when $c_1<r_j$, $r_j>1/3$ (`ratio_signs`), and weak Wolfe for every $c_2>0$.

## Corrected discrepancy (line 380, 15 October 2026)

"This does not make them analytic or uniformly strongly convex" spoke of the four branches of
`D:fullobjective`, but the fourth, $f_3(u,v)=v$, is analytic (`branch3_analytic`); the same kind
of wording issue as the article's M8. Corrected on 15 October 2026 (M14): "This does not make the
first three branches analytic, nor any branch uniformly strongly convex." `not_analytic` proves
it: $f_0,f_1,f_2$ are not analytic, and no branch is uniformly strongly convex. Wording points W7
(line 68) and W8 (line 105, "in this chapter") were applied on the same day, and W46: the
equation counter set at lines 389 and 447 now continues after the three numbered lines of the
`gather` display of Lemma `D:scalarlemma` (before, (12.9)-(12.11) were printed twice;
`D:fullobjective`, `D:localcone`, `D:finalorbit` are now (12.12)-(12.14)).

## Notation

* $(c,d)$ = (`seedC`, `seedD`) = (`AlgebraicSeed.root 0`, `AlgebraicSeed.root 1`); $U,\dots,Y$ =
  `AlgebraicSeed.U` … `AlgebraicSeed.Y`; $\rho$ = `seedRatio` = `AlgebraicSeed.ratio seedC seedD`.
* $g_0,g_1,g_2$ = `g0`, `g1`, `g2 seedC seedD` = `SeedOrbit.gradient seedC seedD i`; $G$ =
  `objective seedC seedD` (`SeedOrbit.objective`); $M_j$ = `metric seedC seedD j`; $M_1$ = `M1`.
* $\mathcal B(H,g,g^+,\alpha)$ = `Failure.fullUpdate H g g⁺ α` (`bfgs_update`).
* $s_j$, $z_j$ ($j\le3$), $p_j=-M_jg_j$, $g_j$ with $g_3=g_0$: `Failure.seedStep`,
  `Failure.seedPoint`, `Failure.seedDir`, `Failure.seedSlope`; the trial point of row `q` of the
  table is `query q`. The table's columns are `trialPhase`, `trialLength`, `trialActive`,
  `trialAccept`; `trialHistory j` is the trial list of phase $j$; `phase k = k % 3`.
* The run on $G$ from $z_0$, $H_0=I$ has iterates `orbitPoint`, matrices `orbitMetric`, gradients
  `orbitGradient` (`cone_orbit`); $\overline G$ is a variable `Gbar` with its defining equation
  (`gbar_eq`: it is `SeedOrbit.coerciveObjective`).
* $\vartheta$ = `theta`, $a_n$ = `scale n`, $\epsilon_0$ = `DScalarRamp.epsilon`, $b_*$ =
  `DEmbedding.bStar`, $c_b$ = `DScalarRamp.center b`, $P_b$ = `DScalarRamp.ramp b`, $J_b$ =
  `DScalarRamp.primitive b`, $\xi$ = `coordinate b (scale n) x`, $\ell_b,u_b$ =
  `DScalarRamp.lowerLength b`, `DScalarRamp.upperLength b`, $\varphi_b$ = `DScalar.phi b`,
  $\varphi_b'$, $\varphi_b''$ = `deriv`, `deriv ∘ deriv`.
* $f_i$ = `DEmbedding.branch i`, $F$ = `DEmbedding.objective`, $p_n$ = `DEmbedding.center n`; the
  $n$th run ($n\ge1$) is `DEmbedding.run hn c₁ c₂ …`. Hessians are `RadialHessian.matrix`
  (classical for the $C^2$ branches), operator norms `FrameNorms.euclideanOpNorm`; `Vec 2` carries
  the sup norm, Euclidean norms are `‖euclideanVector z‖`; $\partial F(x)$ is
  `ConvexSubdifferential.subdifferential F x`; one-sided directional derivatives are limits along
  `𝓝[>] 0`.
* Printed decimals ("$\simeq$", "approximately", the tables) are read as nearest roundings,
  $|x-\text{printed}|<\text{unit}/2$ (`display_round`, from `DDisplayPrecision.corrected_error`);
  the printed values are the library's corrected display values.

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/001` (`D:bfgs`), `prose/002` | 27-32 | `bfgs_update`, `no_reset` |
| `prose/003`, `disp/002` (`D:tests`) | 34-44 | `specified_search`, `strict_tests` |
| `prose/004`, `prose/005` | 45 | `nonstrict_identical`, `all_trials_differentiable` |
| `theorem/D:main` (`disp/003`-`005`) | 47-62 | `main` |
| `disp/006`, `prose/008` | 64-68 | `accepted_lengths`, `starts_null` |
| `disp/008`, `prose/009`, `disp/010`, `lemma/D:root` | 89-106 | `polys_def`, `root_def`, `rho_value`, `root_lemma` |
| `disp/011`, `disp/012` (proof of `D:root`) | 109-116 | `jacobian_residual`, `contraction` |
| `disp/015`, `disp/016`, `disp/018`, `disp/019`, `prose/011` | 131-160 | `closure`, `steps`, `z3_eq`, `approximate_points`, `active_gradients` |
| `disp/021`-`023`, `prose/013`-`016`, `prose/018` | 167-189 | `generic_closure`, `middle_affine`, `parallel_condition`, `rho_tilde_rayleigh`, `last_update_projector`, `polys_iff`, `rho_difference`, `formal_checks` |
| `prose/020`, `prose/021` (table), `disp/024`, `disp/025`, `prose/024`, `prose/026` | 204-233 | `rejected_above`, `trial_table`, `starting_values`, `accepted_ratios`, `ratio_signs`, `trial_tree_all` |
| `disp/026`, `prose/028`, `prose/029` (`D:trialbounds`) | 235-241 | `trial_bounds` |
| `disp/027`, `prose/030`-`033`, `disp/028` | 243-253 | `cone_orbit`, `cone_scaling`, `cone_limit`, `limit_nonstationary`, `downhill`, `ray_hull` |
| `disp/029`, `prose/034`-`038` | 260-264 | `coercive_failure`, `coercive_trials`, `coercive_same_search`, `coercive_combination`, `coercive_minimizer`, `coercive_sublevels` |
| `disp/032`-`036`, `prose/041`, `prose/042` | 288-324 | `ramp_def`, `ramp_bounds`, `primitive_def`, `phi_def`, `intervals_cover` |
| `lemma/D:scalarlemma` (`disp/037`), `disp/039`, `disp/040`, `disp/042` | 326-368 | `scalar_lemma`, `matching_identity`, `asymptotic_orders`, `scalar_table` |
| `disp/043`, `prose/043`-`046` | 372-380 | `third_derivative_bound`, `second_derivative_regularity`, `branches_C21` |
| `prose/047` (corrected) | 380 | `not_analytic`, `branch3_analytic` (counterexample, former wording) |
| `prose/048`-`053`, `disp/045`-`048`, `disp/050`, `prose/056` | 404-438 | `branch_hessians`, `hessian_bounds_01`, `bstar_curvature`, `hessian_bounds_23`, `common_bounds`, `objective_minimizer`, `center_def`, `center_branch_slopes`, `center_facts` |
| `disp/051`-`053`, `prose/057`-`061`, `disp/056`, `disp/057` | 453-489 | `initial_def`, `final_orbit`, `trial_form`, `local_model_at_trials`, `embedded_decisions`, `scaled_update`, `spd_differentiable`, `final_limits`, `initial_limits`, `trajectory_bound` |

The other items (definitions reused from the article, displays that the article states word for
word, summaries, section titles, remarks on the formalization and the literature) are
`DEFINITION`, `SAME_AS`, `PART_OF`, `PROOF` or `NON_CLAIM` in the register. An `example` at the
end shows that the standing assumptions can hold at once.
-/

noncomputable section
open Set Filter Matrix BfgsVerification
open scoped Topology

namespace BfgsCoverage.Companion.Ch12D

open SeedOrbit SeedCycle DScalarGeometric
open BfgsCoverage.Article

/-! ### The specified strict search: trial budget and determinism -/

/-- A successful strict search keeps its output when one more trial is allowed. -/
theorem search_fuel_succ {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ : ℝ} :
    ∀ (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a b : ℝ) (L : List ℝ),
      DeterministicLineSearch.search F x p g c₁ c₂ fuel l h a = (some b, L) →
      DeterministicLineSearch.search F x p g c₁ c₂ (fuel + 1) l h a = (some b, L) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l h a b L hs
    simp [DeterministicLineSearch.search] at hs
  | succ fuel ih =>
    intro l h a b L hs
    by_cases hA : DeterministicLineSearch.Armijo F x p g c₁ a
    · by_cases hW : DeterministicLineSearch.Wolfe F x p g c₂ a
      · rw [DeterministicLineSearch.search_accept fuel hA hW] at hs
        rw [DeterministicLineSearch.search_accept (fuel + 1) hA hW, hs]
      · rw [DeterministicLineSearch.search, if_pos hA, if_neg hW] at hs ⊢
        generalize hr : DeterministicLineSearch.search F x p g c₁ c₂ fuel a h
          (DeterministicLineSearch.nextTrial a h) = r at hs
        obtain ⟨r1, r2⟩ := r
        simp only [Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [ih a h (DeterministicLineSearch.nextTrial a h) b r2 hr]
    · rw [DeterministicLineSearch.search, if_neg hA] at hs ⊢
      generalize hr : DeterministicLineSearch.search F x p g c₁ c₂ fuel l (some a)
        (DeterministicLineSearch.nextTrial l (some a)) = r at hs
      obtain ⟨r1, r2⟩ := r
      simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [ih l (some a) (DeterministicLineSearch.nextTrial l (some a)) b r2 hr]

/-- The trial budget only bounds the number of trials: a successful output of the specified
strict search is its output for every larger budget. -/
theorem fromMetric_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x : Vec n} {H : Mat n} {c₁ c₂ : ℝ}
    {fuel N : ℕ} {b : ℝ} {L : List ℝ}
    (hs : DeterministicLineSearch.fromMetric F x H c₁ c₂ fuel = (some b, L)) (hN : fuel ≤ N) :
    DeterministicLineSearch.fromMetric F x H c₁ c₂ N = (some b, L) := by
  unfold DeterministicLineSearch.fromMetric at hs ⊢
  induction N, hN using Nat.le_induction with
  | base => exact hs
  | succ N _ ih => exact search_fuel_succ N 0 none 1 b L ih

/-- The strict implementation is deterministic: two full-BFGS runs on the same objective with
the same initial point and matrix, whose lengths are outputs of the specified strict search (with
some trial budgets), coincide. -/
theorem implemented_run_unique {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ}
    (R R' : AdmissibleBFGSRun n F) (hx : R.x 0 = R'.x 0) (hH : R.H 0 = R'.H 0)
    (hs : ∀ k, ∃ N L, DeterministicLineSearch.fromMetric F (R.x k) (R.H k) c₁ c₂ N = (some (R.α k), L))
    (hs' : ∀ k, ∃ N L, DeterministicLineSearch.fromMetric F (R'.x k) (R'.H k) c₁ c₂ N =
      (some (R'.α k), L)) :
    R.x = R'.x ∧ R.H = R'.H ∧ R.g = R'.g ∧ R.α = R'.α := by
  have hg : ∀ k, R.x k = R'.x k → R.g k = R'.g k := by
    intro k hk
    rw [← DeterministicLineSearch.actual_coordinateGradient (R.hasGradient k),
      ← DeterministicLineSearch.actual_coordinateGradient (R'.hasGradient k), hk]
  have hα : ∀ k, R.x k = R'.x k → R.H k = R'.H k → R.α k = R'.α k := by
    intro k hk hHk
    obtain ⟨N, L, hN⟩ := hs k
    obtain ⟨N', L', hN'⟩ := hs' k
    have h1 := fromMetric_fuel_mono hN (le_max_left N N')
    have h2 := fromMetric_fuel_mono hN' (le_max_right N N')
    rw [hk, hHk, h2] at h1
    exact (Option.some.inj (congrArg Prod.fst h1)).symm
  have hxH : ∀ k, R.x k = R'.x k ∧ R.H k = R'.H k := by
    intro k
    induction k with
    | zero => exact ⟨hx, hH⟩
    | succ k ih =>
      have hgk := hg k ih.1
      have hαk := hα k ih.1 ih.2
      have hxk : R.x (k + 1) = R'.x (k + 1) := by
        rw [R.step, R'.step, ih.1, ih.2, hgk, hαk]
      refine ⟨hxk, ?_⟩
      rw [R.update, R'.update, ih.2, hgk, hαk, hg (k + 1) hxk]
  exact ⟨funext fun k => (hxH k).1, funext fun k => (hxH k).2,
    funext fun k => hg k (hxH k).1, funext fun k => hα k (hxH k).1 (hxH k).2⟩

/-! ### Section 12.1: main result and exact implementation -/

/-- Item `C/12_D/disp/001` (`companion/chapters/12_D.tex:28-31`), equation `D:bfgs`, with line 27
("For a differentiable current point $x$, put $g=\nabla F(x)$ and $p=-Hg$"):
\[ s=\alpha p,\quad y=\nabla F(x+s)-g,\quad t=y^Ts,\qquad
   H_+=\Bigl(I-\frac{sy^T}{t}\Bigr)H\Bigl(I-\frac{ys^T}{t}\Bigr)+\frac{ss^T}{t}. \]
$\nabla F(x+s)$ is `gplus`. The full inverse update $\mathcal B(H,g,g^+,\alpha)$ of the chapter
(line 130: "$\mathcal B$ denotes \eqref{D:bfgs} with the stated current and next gradients") is
the article's `Failure.fullUpdate H g gplus α`, and $s=\alpha p$ is the library's `bfgsStep H g α`. -/
theorem bfgs_update {n : ℕ} (H : Mat n) (g gplus : Vec n) (α : ℝ) (p s y : Vec n) (t : ℝ)
    (hp : p = -(H *ᵥ g)) (hs : s = α • p) (hy : y = gplus - g) (ht : t = dot y s) :
    s = bfgsStep H g α ∧
    Failure.fullUpdate H g gplus α =
      (1 - t⁻¹ • outer s y) * H * (1 - t⁻¹ • outer y s) + t⁻¹ • outer s s := by
  have hs' : s = bfgsStep H g α := by
    rw [hs, hp, bfgsStep, smul_neg, neg_smul]
  refine ⟨hs', ?_⟩
  rw [Failure.fullUpdate, ← hs', ← hy, ht]
  rfl

/-- Item `C/12_D/prose/002` (`companion/chapters/12_D.tex:32`): "There is no resetting, damping,
rescaling of the stored matrix, memory truncation, or skipped update." In every run
(`AdmissibleBFGSRun`) each step is the full step $x_{k+1}=x_k-\alpha_kH_kg_k$ and each matrix is
the full update of the previous one, $H_{k+1}=\mathcal B(H_k,g_k,g_{k+1},\alpha_k)$. -/
theorem no_reset {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.x (k + 1) = R.x k + bfgsStep (R.H k) (R.g k) (R.α k) ∧
    R.H (k + 1) = Failure.fullUpdate (R.H k) (R.g k) (R.g (k + 1)) (R.α k) :=
  ⟨R.step k, R.update k⟩

open Classical in
/-- Item `C/12_D/prose/003` (`companion/chapters/12_D.tex:34-40`): the specified line search,
"Algorithm 4.6 of Lewis--Overton: initialize a lower bracket $\ell=0$, an upper bracket
$h=+\infty$, and $\alpha=1$. At each trial: if Armijo fails, set $h=\alpha$; otherwise, if weak
Wolfe fails, set $\ell=\alpha$; otherwise, accept $\alpha$ and stop. After a rejection, try
$(\ell+h)/2$ if $h<+\infty$, and $2\ell$ otherwise."

At a differentiable point $x$ with $g=\nabla F(x)$ and $p=-Hg$, the search
`DeterministicLineSearch.fromMetric F x H c₁ c₂ N` is the bracketing search started with
$\ell=0$, $h=+\infty$ (`none`) and $\alpha=1$; a trial with brackets `lo`, `hi` tests the strict
Armijo test first and the strict weak Wolfe test second (display `D:tests`, item `disp/002`),
accepts if both hold, sets $h=\alpha$ and tries $(\ell+\alpha)/2$ after an Armijo rejection, and
sets $\ell=\alpha$ and tries $(\alpha+h)/2$, or $2\alpha$ while $h=+\infty$, after a Wolfe
rejection. The output is the accepted length and the list of all trial lengths; the budget `N`
only bounds the number of trials (`fromMetric_fuel_mono`), and an exhausted budget is failure
(`(none, [])`). -/
theorem specified_search {n : ℕ} (F : Vec n → ℝ) (x : Vec n) (H : Mat n) (c₁ c₂ : ℝ)
    (g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x) (p : Vec n) (hp : p = -(H *ᵥ g)) :
    (∀ N, DeterministicLineSearch.fromMetric F x H c₁ c₂ N =
      DeterministicLineSearch.search F x p g c₁ c₂ N 0 none 1) ∧
    (∀ (lo : ℝ) (hi : Option ℝ) (α : ℝ),
      DeterministicLineSearch.search F x p g c₁ c₂ 0 lo hi α = (none, [])) ∧
    ∀ (N : ℕ) (lo : ℝ) (hi : Option ℝ) (α : ℝ),
      DeterministicLineSearch.search F x p g c₁ c₂ (N + 1) lo hi α =
        if DeterministicLineSearch.Armijo F x p g c₁ α then
          if DeterministicLineSearch.Wolfe F x p g c₂ α then (some α, [α])
          else ((DeterministicLineSearch.search F x p g c₁ c₂ N α hi
              (match hi with | none => 2 * α | some u => (α + u) / 2)).1,
            α :: (DeterministicLineSearch.search F x p g c₁ c₂ N α hi
              (match hi with | none => 2 * α | some u => (α + u) / 2)).2)
        else ((DeterministicLineSearch.search F x p g c₁ c₂ N lo (some α) ((lo + α) / 2)).1,
          α :: (DeterministicLineSearch.search F x p g c₁ c₂ N lo (some α) ((lo + α) / 2)).2) := by
  have hstep : bfgsStep H g 1 = p := by simp [hp, bfgsStep]
  refine ⟨fun N => ?_, fun lo hi α => ?_, fun N lo hi α => ?_⟩
  · unfold DeterministicLineSearch.fromMetric
    rw [DeterministicLineSearch.actual_coordinateGradient hg, hstep]
  · simp [DeterministicLineSearch.search]
  · rw [DeterministicLineSearch.search]
    rfl

/-- Item `C/12_D/disp/002` (`companion/chapters/12_D.tex:41-44`): the two tests of the search,
\[ F(x+\alpha p)<F(x)+c_1\alpha g^Tp,\qquad \nabla F(x+\alpha p)^Tp>c_2g^Tp. \]
`DeterministicLineSearch.Armijo` is literally the first inequality.
`DeterministicLineSearch.Wolfe` uses `coordinateGradient F (x + α • p)`, which is
$\nabla F(x+\alpha p)$ at a differentiable trial point (here `hg'`). -/
theorem strict_tests {n : ℕ} (F : Vec n → ℝ) (x p g : Vec n) (c₁ c₂ α : ℝ) (g' : Vec n)
    (hg' : HasFDerivAt F (gradientFunctional g') (x + α • p)) :
    (DeterministicLineSearch.Armijo F x p g c₁ α ↔ F (x + α • p) < F x + c₁ * α * dot g p) ∧
    (DeterministicLineSearch.Wolfe F x p g c₂ α ↔ dot g' p > c₂ * dot g p) := by
  refine ⟨Iff.rfl, ?_⟩
  unfold DeterministicLineSearch.Wolfe
  rw [DeterministicLineSearch.actual_coordinateGradient hg']

/-- $\overline G$ of display `disp/029` is the library's `SeedOrbit.coerciveObjective`. -/
theorem gbar_eq (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    Gbar = coerciveObjective := by
  funext x
  rw [hGbar]
  apply le_antisymm
  · obtain ⟨h0, h1, h3⟩ := coercive_coordinate_bounds x
    have h2 := coerciveFamily.branch_le 2 x
    have he2 : coerciveFamily.branch 2 x = seedC * x 0 + seedD * x 1 := by
      simp [coerciveFamily, MaxAffine.Family.branch, dot, Fin.sum_univ_two, g2]
    rw [he2] at h2
    exact max_le (max_le h0 (by linarith)) (max_le h2 h3)
  · unfold coerciveObjective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro i _
    have e0 : coerciveFamily.branch 0 x = x 0 := by
      simp [coerciveFamily, MaxAffine.Family.branch, dot, Fin.sum_univ_two, g0]
    have e1 : coerciveFamily.branch 1 x = -x 0 - x 1 / 8 := by
      simp [coerciveFamily, MaxAffine.Family.branch, dot, Fin.sum_univ_two, g1]
      ring
    have e2 : coerciveFamily.branch 2 x = seedC * x 0 + seedD * x 1 := by
      simp [coerciveFamily, MaxAffine.Family.branch, dot, Fin.sum_univ_two, g2]
    fin_cases i
    · show coerciveFamily.branch 0 x ≤ _
      rw [e0]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · show coerciveFamily.branch 1 x ≤ _
      rw [e1]
      exact (le_max_right _ _).trans (le_max_left _ _)
    · show coerciveFamily.branch 2 x ≤ _
      rw [e2]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · show coerciveFamily.branch 3 x ≤ _
      rw [coercive_branch_last]
      exact (le_max_right _ _).trans (le_max_right _ _)

/-- Item `C/12_D/prose/004` (`companion/chapters/12_D.tex:45`): "All decisions below are strict;
using non-strict acceptance inequalities produces the identical orbit."

For every $0<c_1\le1/3$, $c_1<c_2<1$ and the three runs of the chapter (the run on $G$ from
$z_0$, the run on $\overline G$ from $z_0$, and for $n\ge1$ the run on $F$ from $x_0^{(n)}$, all
with $H_0=I$, produced by the strict search), at every iterate the search with the non-strict
tests $F(x+\alpha p)\le F(x)+c_1\alpha g^Tp$, $\nabla F(x+\alpha p)^Tp\ge c_2g^Tp$
(`NonStrictLineSearch`) returns the same accepted length and trial list as the strict search, and
every run produced by the non-strict implementation from the same initial point and matrix has the
same iterates and matrices (the identical orbit). -/
theorem nonstrict_identical (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    (∀ k, NonStrictLineSearch.fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k) c₁ c₂ 5) ∧
    (∀ k, NonStrictLineSearch.fromMetric Gbar (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric Gbar (orbitPoint k) (orbitMetric k) c₁ c₂ 5) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (k : ℕ),
      NonStrictLineSearch.fromMetric DEmbedding.objective ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)
          ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric DEmbedding.objective
          ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)
          ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5) ∧
    (∀ R' : AdmissibleBFGSRun 2 (objective seedC seedD), R'.x 0 = Failure.seedPoint 0 → R'.H 0 = 1 →
      (∀ k, ∃ N L, NonStrictLineSearch.fromMetric (objective seedC seedD) (R'.x k) (R'.H k) c₁ c₂ N =
        (some (R'.α k), L)) → R'.x = orbitPoint ∧ R'.H = orbitMetric) ∧
    (∀ R' : AdmissibleBFGSRun 2 Gbar, R'.x 0 = Failure.seedPoint 0 → R'.H 0 = 1 →
      (∀ k, ∃ N L, NonStrictLineSearch.fromMetric Gbar (R'.x k) (R'.H k) c₁ c₂ N =
        (some (R'.α k), L)) → R'.x = orbitPoint ∧ R'.H = orbitMetric) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (R' : AdmissibleBFGSRun 2 DEmbedding.objective),
      R'.x 0 = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x 0 → R'.H 0 = 1 →
      (∀ k, ∃ N L, NonStrictLineSearch.fromMetric DEmbedding.objective (R'.x k) (R'.H k) c₁ c₂ N =
        (some (R'.α k), L)) →
      R'.x = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x ∧
        R'.H = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H) := by
  have hG := gbar_eq Gbar hGbar
  subst hG
  obtain ⟨h1, h2, h3⟩ := DLiteralTargets.nonStrictRun c₁ c₂ hc₁ hc₁' hc hc₂
  refine ⟨fun k => (h1 k).2, fun k => (h2 k).2, fun n hn k => (h3 n hn k).2, ?_, ?_, ?_⟩
  · intro R' hx' hH' hs'
    have hH0 : (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 := (actual_run_failure hc₁ hc₁' hc hc₂).1
    obtain ⟨e1, e2, -, -⟩ := Failure.implemented_run_unique R' (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂)
      (hx'.trans Failure.seedPoint_zero_eq) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, (h1 k).1⟩)
    exact ⟨e1, e2⟩
  · intro R' hx' hH' hs'
    have hH0 : (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 :=
      (actual_coercive_deterministic_failure hc₁ hc₁' hc hc₂).2.2.2.2.1
    obtain ⟨e1, e2, -, -⟩ := Failure.implemented_run_unique R' (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂)
      (hx'.trans Failure.seedPoint_zero_eq) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, (h2 k).1⟩)
    exact ⟨e1, e2⟩
  · intro n hn R' hx' hH' hs'
    have hH0 := DEmbedding.run_initial_matrix hn hc₁ hc₁' hc hc₂
    exact (Failure.implemented_run_unique R' (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂)
      hx' (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, (h3 n hn k).1⟩)).imp id (fun h => h.1)

/-- Item `C/12_D/prose/005` (`companion/chapters/12_D.tex:45`): "Every trial point, not just every
accepted point, is differentiable." For the three runs of the chapter (on $G$ and on
$\overline G$ the iterates `orbitPoint k`, matrices `orbitMetric k` and gradients `orbitGradient k`
of `cone_orbit` and `coercive_failure`; on $F$ the runs `DEmbedding.run` of Theorem `D:main`), the
objective is differentiable at every accepted point and at every trial point
$x_k+\alpha p_k$, $p_k=-H_kg_k$, $\alpha$ in the trial list of the $k$th search. -/
theorem all_trials_differentiable (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    (∀ k, DifferentiableAt ℝ (objective seedC seedD) (orbitPoint k) ∧
      ∀ a ∈ trialHistory (phase k), DifferentiableAt ℝ (objective seedC seedD)
        (orbitPoint k + a • bfgsStep (orbitMetric k) (orbitGradient k) 1)) ∧
    (∀ k, DifferentiableAt ℝ Gbar (orbitPoint k) ∧
      ∀ a ∈ trialHistory (phase k), DifferentiableAt ℝ Gbar
        (orbitPoint k + a • bfgsStep (orbitMetric k) (orbitGradient k) 1)) ∧
    ∀ (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) (n : ℕ)
      (hn : 1 ≤ n) (k : ℕ),
      DifferentiableAt ℝ DEmbedding.objective ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k) ∧
      ∀ a ∈ trialHistory (phase k), DifferentiableAt ℝ DEmbedding.objective
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k + a •
          bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1) := by
  have hG := gbar_eq Gbar hGbar
  subst hG
  refine ⟨fun k => ⟨(orbit_hasGradient k).differentiableAt, fun a ha => ?_⟩,
    fun k => ⟨(coercive_orbit_hasGradient k).differentiableAt, fun a ha => ?_⟩,
    fun c₁ c₂ hc₁ hc₁' hc hc₂ n hn k =>
      ⟨((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).hasGradient k).differentiableAt, fun a ha => ?_⟩⟩
  · obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
    exact orbit_all_trials_differentiable k q hq
  · obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
    exact (coercive_all_trials_hasGradient k q hq).differentiableAt
  · obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
    exact (DEmbedding.run_all_trials_differentiable hn hc₁ hc₁' hc hc₂ k q hq).differentiableAt

/-- Item `C/12_D/theorem/D:main` (`companion/chapters/12_D.tex:47-62`), Theorem `D:main`, including
its displays Item `C/12_D/disp/003` (`companion/chapters/12_D.tex:49-51`),
Item `C/12_D/disp/004` (`companion/chapters/12_D.tex:53-56`) and
Item `C/12_D/disp/005` (`companion/chapters/12_D.tex:58-60`).

"There exist four convex functions $f_i\in C^2(\mathbb R^2)$, with
\[ 0\preceq\nabla^2 f_i(x)\preceq64I \quad(i=0,1,2,3;\ x\in\mathbb R^2), \]
such that $F=\max_i f_i$ has compact sublevel sets and the unique global minimizer $x_*=0$, where
$F$ is nonsmooth. For the deterministic line search specified above, with $c_1=10^{-4}$ and
$c_2=1/2$, there are starting points $x_0^{(n)}\to0$, all initialized with $H_0=I$, whose
full-BFGS iterates satisfy
\[ x_k^{(n)}\longrightarrow p_n\ne0,\qquad F(x_k^{(n)})\downarrow F(p_n)>0,\qquad
   0\notin\partial F(p_n). \]
Every line search terminates after at most five trials. In fact, the same function, initial
points, matrices, and trial decisions work for every fixed
\[ 0<c_1\le\tfrac13,\qquad c_1<c_2<1. \]
The entire accepted and trial trajectories can be contained in an arbitrarily small neighborhood
of $0$ by choosing $n$ sufficiently large."

Lean form. $C^2$ is `ContDiff ℝ 2`; $\nabla^2f_i(x)$ is `RadialHessian.matrix (f i) x`, the
classical Hessian for these $C^2$ functions; $A\succeq0$ is `A.PosSemidef`; $F$ is introduced
with its defining equation `hF`; "nonsmooth" is non-differentiability at $0$;
$\partial F(p)$ is `ConvexSubdifferential.subdifferential F p`. The runs are indexed by $n\ge1$
(Section 12.5). The iterates `x n k`, matrices `H n k`, gradients `g n k`, accepted lengths
`α n k`, trial lists `hist n k` (all trial lengths of the $k$th search in order; the last one is
accepted, the others rejected: the trial decisions) and the limits `p n` are chosen before the
pair $(c_1,c_2)$. For $(c_1,c_2)=(10^{-4},1/2)$, and in fact for every pair of the range, the run
`R : AdmissibleBFGSRun 2 F` (full update at every step) with these data is produced by the
specified strict search (`DeterministicLineSearch.fromMetric`, display `D:tests`) with any trial
budget $N\ge5$. "$F(x_k)\downarrow$" is read as strictly decreasing values. The trial points of
search $k$ are `x n k + a • bfgsStep (H n k) (g n k) 1` $=x_k-aH_kg_k$, `a ∈ hist n k`. -/
theorem main :
    ∃ f : Fin 4 → Vec 2 → ℝ,
      (∀ i, ConvexOn ℝ univ (f i) ∧ ContDiff ℝ 2 (f i)) ∧
      (∀ i x, (RadialHessian.matrix (f i) x).PosSemidef ∧
        ((64 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (f i) x).PosSemidef) ∧
      ∀ F : Vec 2 → ℝ, (∀ x, F x = Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)) →
        (∀ a : ℝ, IsCompact {x | F x ≤ a}) ∧
        (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F (0 : Vec 2) ∧
        ∃ (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (g : ℕ → ℕ → Vec 2) (α : ℕ → ℕ → ℝ)
          (hist : ℕ → ℕ → List ℝ) (p : ℕ → Vec 2),
          Tendsto (fun n => x n 0) atTop (𝓝 0) ∧ (∀ n, H n 0 = 1) ∧
          (∀ n, 1 ≤ n → ∃ R : AdmissibleBFGSRun 2 F, R.c₁ = 1 / 10 ^ 4 ∧ R.c₂ = 1 / 2 ∧
            R.x = x n ∧ R.H = H n ∧ R.g = g n ∧ R.α = α n ∧
            ∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric F (x n k) (H n k) (1 / 10 ^ 4) (1 / 2) N =
              (some (α n k), hist n k)) ∧
          (∀ n, 1 ≤ n →
            Tendsto (x n) atTop (𝓝 (p n)) ∧ p n ≠ 0 ∧
            (∀ k, F (x n (k + 1)) < F (x n k)) ∧
            Tendsto (fun k => F (x n k)) atTop (𝓝 (F (p n))) ∧ 0 < F (p n) ∧
            (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (p n) ∧
            ∀ k, (hist n k).length ≤ 5) ∧
          (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 → ∀ n, 1 ≤ n →
            ∃ R : AdmissibleBFGSRun 2 F, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
              R.x = x n ∧ R.H = H n ∧ R.g = g n ∧ R.α = α n ∧
              ∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric F (x n k) (H n k) c₁ c₂ N =
                (some (α n k), hist n k)) ∧
          ∀ V ∈ 𝓝 (0 : Vec 2), ∀ᶠ n in atTop, ∀ k, x n k ∈ V ∧
            ∀ a ∈ hist n k, x n k + a • bfgsStep (H n k) (g n k) 1 ∈ V := by
  refine ⟨DEmbedding.branch, fun i => ⟨DEmbedding.branch_convex i, DEmbedding.branch_contDiff i⟩,
    DEmbedding.branch_hessian_bounds, ?_⟩
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
    exact fromMetric_fuel_mono (DEmbedding.run_search hn hc₁ hc₁' hc hc₂ k) hN
  refine ⟨DEmbedding.objective_sublevels_compact, fun x => ?_, fun x hx => ?_,
    DEmbedding.objective_not_differentiable_zero, ?_⟩
  · rw [DEmbedding.objective_zero]
    exact DEmbedding.objective_nonnegative x
  · rw [DEmbedding.objective_zero] at hx
    exact DEmbedding.objective_unique_zero hx
  have hc : (0 : ℝ) < 1 / 10 ^ 4 ∧ (1 / 10 ^ 4 : ℝ) ≤ 1/3 ∧ (1 / 10 ^ 4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
    norm_num
  refine ⟨fun n k => SeedEmbedding.point (DEmbedding.center n) ((scale n) ^ 2) k,
    fun _ k => orbitMetric k, fun n k => SeedEmbedding.gradient ((scale n) ^ 2) k,
    fun _ k => orbitLength k, fun _ k => trialHistory (phase k), DEmbedding.center,
    DEmbedding.initial_points_tendsto, fun _ => ?_,
    fun n hn => hruns _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 n hn, fun n hn => ?_, hruns, ?_⟩
  · change (1 : ℝ) • (1 : Mat 2) = 1
    simp
  · refine ⟨SeedEmbedding.point_tendsto _ _, DEmbedding.center_ne_zero n,
      DEmbedding.run_value_strict_decrease hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2,
      DEmbedding.run_value_tendsto hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2, DEmbedding.center_positive n,
      DEmbedding.center_nonstationary n, fun k => trialHistory_length_le (phase k)⟩
  · intro V hV
    filter_upwards [DEmbedding.trajectories_uniformly_small hV] with n hn k
    refine ⟨hn.1 k, fun a ha => ?_⟩
    obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
    rw [SeedEmbedding.translated_trial]
    exact hn.2 k q hq

/-- Item `C/12_D/disp/006` (`companion/chapters/12_D.tex:65-67`), with line 64: "The accepted
lengths are not assigned externally. They are generated by the deterministic search:
\[ \alpha_{3m}=1,\qquad\alpha_{3m+1}=\tfrac14,\qquad\alpha_{3m+2}=\tfrac1{16}. \]"
For the runs of Theorem `D:main` (every $n\ge1$ and every $0<c_1\le1/3$, $c_1<c_2<1$), the
specified strict search at the iterates $3m$, $3m+1$, $3m+2$ returns the accepted lengths
$1$, $1/4$, $1/16$ (with the trial lists of the table, `trial_table`), and these are the run's
lengths. -/
theorem accepted_lengths (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    DeterministicLineSearch.fromMetric DEmbedding.objective
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m))
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m)) c₁ c₂ 5 = (some 1, [1]) ∧
    DeterministicLineSearch.fromMetric DEmbedding.objective
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m + 1))
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m + 1)) c₁ c₂ 5 =
      (some (1/4), [1, 1/2, 1/4]) ∧
    DeterministicLineSearch.fromMetric DEmbedding.objective
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m + 2))
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m + 2)) c₁ c₂ 5 =
      (some (1/16), [1, 1/2, 1/4, 1/8, 1/16]) ∧
    (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).α (3 * m) = 1 ∧
    (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).α (3 * m + 1) = 1/4 ∧
    (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).α (3 * m + 2) = 1/16 := by
  have hs := DEmbedding.run_search hn hc₁ hc₁' hc hc₂
  obtain ⟨-, -, -, h0⟩ := DEmbedding.run_phase_parameters hn hc₁ hc₁' hc hc₂ m 0
  obtain ⟨-, -, -, h1⟩ := DEmbedding.run_phase_parameters hn hc₁ hc₁' hc hc₂ m 1
  obtain ⟨-, -, -, h2⟩ := DEmbedding.run_phase_parameters hn hc₁ hc₁' hc hc₂ m 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at h0 h1 h2
  have p0 : phase (3 * m) = 0 := Fin.ext (by simp [phase])
  have p1 : phase (3 * m + 1) = 1 := Fin.ext (by simp [phase, Nat.add_mod])
  have p2 : phase (3 * m + 2) = 2 := Fin.ext (by simp [phase, Nat.add_mod])
  have e0 := hs (3 * m)
  have e1 := hs (3 * m + 1)
  have e2 := hs (3 * m + 2)
  dsimp only at e0 e1 e2
  rw [p0, h0] at e0
  rw [p1, h1] at e1
  rw [p2, h2] at e2
  exact ⟨e0, e1, e2, h0, h1, h2⟩

open DScalarGeometric in
/-- Item `C/12_D/prose/008` (`companion/chapters/12_D.tex:68`): "It does not address strong-Wolfe
interpolation searches or a positive-measure basin of failing initial points." The failing
starts $x_0^{(n)}=p_n+a_n^2z_0$, $n\ge1$, of Theorem `D:main` form a countable set of Lebesgue
measure zero; they are not a positive-measure basin. (Strong-Wolfe interpolation searches are
outside the theorem, which concerns the specified search.) -/
theorem starts_null :
    {x : Vec 2 | ∃ n : ℕ, 1 ≤ n ∧ x = DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0}.Countable ∧
    MeasureTheory.volume
      {x : Vec 2 | ∃ n : ℕ, 1 ≤ n ∧ x = DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0} = 0 := by
  have hc : {x : Vec 2 | ∃ n : ℕ, 1 ≤ n ∧
      x = DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0}.Countable :=
    (Set.countable_range fun n : ℕ => DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0).mono
      (by
        rintro x ⟨n, -, hx⟩
        exact ⟨n, hx.symm⟩)
  exact ⟨hc, hc.measure_zero _⟩

/-! ### Section 12.2: an exactly specified algebraic seed -/

/-- A printed decimal of Chapter D is the nearest rounding of the actual value: if the actual
quantity is the library's certified display value `DDisplayActual.values i`, the printed decimal
is `DDisplayPrecision.corrected i` and the unit of the last printed digit is
`DDisplayPrecision.unit i`, then $|x-\text{printed}|<\text{unit}/2$. -/
theorem display_round (i : Fin 33) {x printed u : ℝ} (hx : DDisplayActual.values i = x)
    (hp : DDisplayPrecision.corrected i = printed) (hu : DDisplayPrecision.unit i = u) :
    |x - printed| < u / 2 := by
  rw [← hx, ← hp, ← hu]
  exact DDisplayPrecision.corrected_error i

/-- Item `C/12_D/disp/008` (`companion/chapters/12_D.tex:90-92`), equation `D:polys`:
\[ 264192RK-UV(U+129)=0,\qquad16VTK-RUY=0. \]
The left sides are the components of the library's `AlgebraicSeed.P` at $(c,d)$ (first
conjunct), and the chapter's pair $(c,d)=$ (`seedC`, `seedD`) satisfies both equations. -/
theorem polys_def (c d : ℝ) :
    AlgebraicSeed.P ![c, d] = ![264192 * AlgebraicSeed.R c d * AlgebraicSeed.K c d -
        AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129),
      16 * AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d -
        AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d] ∧
    (264192 * AlgebraicSeed.R seedC seedD * AlgebraicSeed.K seedC seedD -
        AlgebraicSeed.U seedC seedD * AlgebraicSeed.V seedC seedD * (AlgebraicSeed.U seedC seedD + 129) = 0 ∧
      16 * AlgebraicSeed.V seedC seedD * AlgebraicSeed.T seedC seedD * AlgebraicSeed.K seedC seedD -
        AlgebraicSeed.R seedC seedD * AlgebraicSeed.U seedC seedD * AlgebraicSeed.Y seedC seedD = 0) := by
  refine ⟨?_, source_root_polynomials⟩
  ext i
  fin_cases i <;> rfl

/-- Item `C/12_D/prose/009` (`companion/chapters/12_D.tex:93`): "Choose the unique root in the
closed $\ell_\infty$ box of radius $10^{-30}$ centered at the rational pair $(c_0,d_0)$." The
chapter's pair $(c,d)$ is the library's `AlgebraicSeed.root` (`seedC`, `seedD`): it lies in the
box (`Vec 2` carries the sup norm), solves `D:polys` ($P=0$), and is the only solution there. The
center $(c_0,d_0)$ is `AlgebraicSeed.center`, the two displayed decimals
(`BfgsCoverage.Article.SeedCertificate.center_def`). -/
theorem root_def :
    ‖AlgebraicSeed.root - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 ∧ AlgebraicSeed.P AlgebraicSeed.root = 0 ∧
    (∀ x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 → AlgebraicSeed.P x = 0 →
      x = AlgebraicSeed.root) ∧
    seedC = AlgebraicSeed.root 0 ∧ seedD = AlgebraicSeed.root 1 :=
  ⟨AlgebraicSeed.root_spec.1, AlgebraicSeed.root_spec.2,
    fun x hb hx => AlgebraicSeed.root_unique x ⟨hb, hx⟩, rfl, rfl⟩

/-- Item `C/12_D/disp/010` (`companion/chapters/12_D.tex:99-102`), equation `D:rho`:
\[ \rho=\frac{129R}{V(U+129)}\simeq0.060199206107543764815373666287. \]
The library's `seedRatio` is $\rho$ (first conjunct: its defining formula at the root; this part
of the display is a definition), and "$\simeq$" is nearest rounding to the thirty printed digits.
(On the whole root box: `BfgsCoverage.Companion.SeedCertificate.root_certificate`.) -/
theorem rho_value :
    seedRatio = 129 * AlgebraicSeed.R seedC seedD /
      (AlgebraicSeed.V seedC seedD * (AlgebraicSeed.U seedC seedD + 129)) ∧
    |seedRatio - 0.060199206107543764815373666287| < 1 / 10 ^ 30 / 2 :=
  ⟨rfl, display_round 0 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
    (by simp [DDisplayPrecision.unit])⟩

/-- $g^T(-\alpha Hg)=-\alpha\,g^THg$. -/
theorem dot_bfgsStep {n : ℕ} (H : Mat n) (g : Vec n) (α : ℝ) :
    dot g (bfgsStep H g α) = -α * metricEnergy H g := by
  rw [bfgsStep, dot_smul_right]
  rfl

/-- Item `C/12_D/lemma/D:root` (`companion/chapters/12_D.tex:104-106`), Lemma `D:root`.

"The designated box contains exactly one solution of~\eqref{D:polys}. All denominators in this
chapter are nonzero there, and $0.060<\rho<0.061$." ("in this chapter" since 15 October 2026,
wording point W8; before "in this note".)

The box is $\{x:\|x-(c_0,d_0)\|_\infty\le10^{-30}\}$ and a solution of `D:polys` is a zero of $P$.
"All denominators in this chapter" that depend on the point $(c,d)$ of the box are: $V(U+129)$ (of
$\rho$, `D:rho`, and of $\widetilde\rho-\rho$), $UV(U+129)$ (of $\beta$), $RUY$ (of $\gamma$),
$U(U+129)Y$ (of $\widetilde\rho$), $1-\rho$ (of $z_0$, `D:x0`), $b_*=2c-32d$ (of $c_{b_*}$,
$\xi$ and $\varphi_{b_*}$), $g_j^Ts_j$ (of the ratios at the accepted steps) and $t=y^Ts$ of the
three updates `D:bfgs` with the matrices $M_j$ and lengths $1,1/4,1/16$; they are nonzero at every
point of the box. The bounds on $\rho$ are those of the chapter's $\rho$ at the root (they hold
at every point of the box as well, `AlgebraicSeed.box_denominators_and_ratio`). -/
theorem root_lemma :
    (∃! x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 ∧ AlgebraicSeed.P x = 0) ∧
    (∀ x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 → ∀ c d : ℝ, c = x 0 → d = x 1 →
      AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0 ∧
      AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0 ∧
      AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0 ∧
      AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0 ∧
      1 - 129 * AlgebraicSeed.R c d / (AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)) ≠ 0 ∧
      2 * c - 32 * d ≠ 0 ∧
      (∀ j : Fin 3, dot (SeedOrbit.gradient c d j)
        (bfgsStep (metric c d j) (SeedOrbit.gradient c d j) (length j)) ≠ 0) ∧
      ∀ j : Fin 3, dot (SeedOrbit.gradient c d (nextPhase j) - SeedOrbit.gradient c d j)
        (bfgsStep (metric c d j) (SeedOrbit.gradient c d j) (length j)) ≠ 0) ∧
    (0.060 : ℝ) < seedRatio ∧ seedRatio < 0.061 := by
  refine ⟨AlgebraicSeed.exists_unique_root, fun x hx c d hc hd => ?_, ?_⟩
  · subst hc hd
    obtain ⟨hU, hV, hR, -, -, hY, hA, -, hhi⟩ := AlgebraicSeed.box_denominators_and_ratio hx
    obtain ⟨h1, -, -, h4⟩ := AlgebraicSeed.box_coarse hx
    obtain ⟨hmet, hcurv0, hcurv1, hlast, -, -, -⟩ := DBoxDenominators.sourceBoxDenominators x hx
    refine ⟨(mul_pos hV hA).ne', (mul_pos (mul_pos hU hV) hA).ne', (mul_pos (mul_pos hR hU) hY).ne',
      (mul_pos (mul_pos hU hA) hY).ne', ?_, by linarith, fun j => ?_, fun j => ?_⟩
    · have h : AlgebraicSeed.ratio (x 0) (x 1) < 1 := by linarith
      unfold AlgebraicSeed.ratio at h
      intro h0
      linarith
    · rw [dot_bfgsStep]
      exact mul_ne_zero (neg_ne_zero.mpr (source_length_pos j).ne') (hmet j).2.ne'
    · fin_cases j
      · exact hcurv0.ne'
      · exact hcurv1.ne'
      · exact (lt_trans (by norm_num) hlast).ne'
  · obtain ⟨-, -, -, -, -, -, -, h1, h2⟩ := AlgebraicSeed.box_denominators_and_ratio
      AlgebraicSeed.root_spec.1
    norm_num
    exact ⟨by linarith, by linarith⟩

/-- Item `C/12_D/disp/011` (`companion/chapters/12_D.tex:109-112`), in the proof of Lemma `D:root`:
with $M=DP(\bar r)^{-1}$, $\bar r=(c_0,d_0)$, and the box $X$,
\[ \sup_{z\in X}\|I-MDP(z)\|_\infty<10^{-26},\qquad\|MP(\bar r)\|_\infty<10^{-50}. \]
$DP(\bar r)$ is the library's rational matrix `AlgebraicSeed.J` (`fderiv ℝ P r̄` is the linear map
of `J`) and $M$ is `AlgebraicSeed.M` $=J^{-1}$; $\|\cdot\|_\infty$ is the operator norm for the sup
norm of `Vec 2` (maximal row sum) and the sup norm of a vector. The bound holds at every point
of $X$ and for the supremum. -/
theorem jacobian_residual :
    AlgebraicSeed.M = (AlgebraicSeed.J)⁻¹ ∧
    fderiv ℝ AlgebraicSeed.P AlgebraicSeed.center = AffineProjection.matrixCLM AlgebraicSeed.J ∧
    (∀ z : Vec 2, ‖z - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 →
      ‖ContinuousLinearMap.id ℝ (Vec 2) -
        (AffineProjection.matrixCLM AlgebraicSeed.M).comp (fderiv ℝ AlgebraicSeed.P z)‖ < 1 / 10 ^ 26) ∧
    sSup ((fun z => ‖ContinuousLinearMap.id ℝ (Vec 2) -
        (AffineProjection.matrixCLM AlgebraicSeed.M).comp (fderiv ℝ AlgebraicSeed.P z)‖) ''
      {z | ‖z - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30}) < 1 / 10 ^ 26 ∧
    ‖AlgebraicSeed.M *ᵥ AlgebraicSeed.P AlgebraicSeed.center‖ < 1 / 10 ^ 50 :=
  ⟨AlgebraicSeed.M_eq_J_inverse, AlgebraicSeed.actual_Jacobian,
    fun _ hz => AlgebraicSeed.source_Jacobian_bound hz, AlgebraicSeed.source_Jacobian_sup_bound,
    AlgebraicSeed.source_residual⟩

/-- The map $z\mapsto z-MP(z)$ is the library's centered Newton map `AlgebraicSeed.newton`
conjugated by the translation to $\bar r$. -/
theorem newton_shift (z : Vec 2) :
    z - AlgebraicSeed.M *ᵥ AlgebraicSeed.P z =
      AlgebraicSeed.center + AlgebraicSeed.newton (z - AlgebraicSeed.center) := by
  simp only [AlgebraicSeed.newton, add_sub_cancel]
  abel

/-- Item `C/12_D/disp/012` (`companion/chapters/12_D.tex:114-116`), in the proof of Lemma `D:root`,
with the preceding sentence: "Hence $z\mapsto z-MP(z)$ is a strict contraction mapping $X$ into
itself, because \[ 10^{-50}+10^{-26}\,10^{-30}<10^{-30}. \]" The numerical inequality, the map
sends the box $X$ into itself, and it is Lipschitz on $X$ (sup norm) with a constant
$\kappa<1$ ($\kappa=7000\cdot10^{-30}$). -/
theorem contraction :
    (1 / 10 ^ 50 : ℝ) + 1 / 10 ^ 26 * (1 / 10 ^ 30) < 1 / 10 ^ 30 ∧
    Set.MapsTo (fun z : Vec 2 => z - AlgebraicSeed.M *ᵥ AlgebraicSeed.P z)
      {z | ‖z - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30} {z | ‖z - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30} ∧
    ∃ κ : ℝ, κ < 1 ∧ ∀ z w : Vec 2, ‖z - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 →
      ‖w - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 →
      ‖(z - AlgebraicSeed.M *ᵥ AlgebraicSeed.P z) - (w - AlgebraicSeed.M *ᵥ AlgebraicSeed.P w)‖ ≤
        κ * ‖z - w‖ := by
  refine ⟨by norm_num, fun z hz => ?_, ⟨7000 * AlgebraicSeed.radius, ?_, fun z w hz hw => ?_⟩⟩
  · have hm := AlgebraicSeed.newton_maps_ball (x := z - AlgebraicSeed.center)
      (show z - AlgebraicSeed.center ∈ Metric.closedBall 0 AlgebraicSeed.radius by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
    simp only [Metric.mem_closedBall, dist_zero_right] at hm
    simp only [Set.mem_setOf_eq]
    rw [newton_shift, add_sub_cancel_left]
    exact hm
  · linarith [AlgebraicSeed.contraction_half]
  · rw [newton_shift, newton_shift, add_sub_add_left_eq_sub]
    have h := AlgebraicSeed.newton_lipschitz (x := z - AlgebraicSeed.center)
      (y := w - AlgebraicSeed.center) hz hw
    rwa [sub_sub_sub_cancel_right] at h

/-- Item `C/12_D/disp/015` (`companion/chapters/12_D.tex:131-134`), equation `D:closure`:
\[ \mathcal B(I,g_0,g_1,1)=M_1,\qquad \mathcal B(M_2,g_2,g_0,1/16)=\rho I, \]
with $M_1=\begin{pmatrix}129/256&-1/16\\-1/16&1\end{pmatrix}$, $M_2=\mathcal B(M_1,g_1,g_2,1/4)$
(`metric seedC seedD 2`), $\mathcal B$ = `Failure.fullUpdate` (`D:bfgs`). -/
theorem closure :
    Failure.fullUpdate 1 g0 g1 1 = !![129/256, -1/16; -1/16, 1] ∧
    Failure.fullUpdate (metric seedC seedD 2) (g2 seedC seedD) g0 (1/16) = seedRatio • (1 : Mat 2) :=
  ⟨Failure.seed_closures.1, Failure.seed_closures.2.1⟩

/-- Item `C/12_D/disp/016` (`companion/chapters/12_D.tex:136-139`), equation `D:steps`: "The three
displacements are
\[ s_0=(-1,0)^T,\quad s_1=(127/1024,1/64)^T,\quad s_2=\rho(1-c,-d)^T." \]
The displacements of the cycle are $s_j=-\alpha_jM_jg_j$ with $\alpha=(1,1/4,1/16)$. -/
theorem steps :
    bfgsStep (metric seedC seedD 0) g0 1 = ![-1, 0] ∧
    bfgsStep (metric seedC seedD 1) g1 (1/4) = ![127/1024, 1/64] ∧
    bfgsStep (metric seedC seedD 2) (g2 seedC seedD) (1/16) = seedRatio • ![1 - seedC, -seedD] :=
  ⟨(Failure.seedStep_eq 0).symm, (Failure.seedStep_eq 1).symm, (Failure.seedStep_eq 2).symm⟩

/-- Item `C/12_D/disp/018` (`companion/chapters/12_D.tex:147-149`): $z_3=\rho z_0$, where
$z_0,\dots,z_3$ are the points of `D:x0` (`Failure.seedPoint`). -/
theorem z3_eq : Failure.seedPoint 3 = seedRatio • Failure.seedPoint 0 :=
  Failure.seed_closures.2.2

/-- Item `C/12_D/disp/019` (`companion/chapters/12_D.tex:151-159`): "For clarity, approximate points
are" the table of $(z_j)_1,(z_j)_2$, $j=0,\dots,3$. Each printed twelve-digit decimal is the
nearest rounding of the coordinate: the error is less than $10^{-12}/2$. -/
theorem approximate_points :
    |Failure.seedPoint 0 0 - 0.888432624149| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 0 1 - (-0.082297397686)| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 1 0 - (-0.111567375851)| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 1 1 - (-0.082297397686)| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 2 0 - 0.012456061649| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 2 1 - (-0.066672397686)| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 3 0 - 0.053482938654| < 1 / 10 ^ 12 / 2 ∧
    |Failure.seedPoint 3 1 - (-0.004954238005)| < 1 / 10 ^ 12 / 2 := by
  have e0 : Failure.seedPoint 0 = point seedC seedD seedRatio 0 := Failure.seedStart_eq
  have e1 : Failure.seedPoint 1 = point seedC seedD seedRatio 1 := Failure.seedPoint_castSucc 1
  have e2 : Failure.seedPoint 2 = point seedC seedD seedRatio 2 := Failure.seedPoint_castSucc 2
  have e3 : Failure.seedPoint 3 = trial seedC seedD seedRatio 2 (length 2) := Failure.seedPoint_succ 2
  rw [e0, e1, e2, e3]
  have hu : ∀ i : Fin 33, i ≠ 0 → DDisplayPrecision.unit i = 1 / 10 ^ 12 := fun i hi => by
    simp [DDisplayPrecision.unit, hi]
  refine ⟨display_round 1 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 1 (by decide)),
    display_round 2 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 2 (by decide)),
    display_round 3 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 3 (by decide)),
    display_round 4 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 4 (by decide)),
    display_round 5 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 5 (by decide)),
    display_round 6 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 6 (by decide)),
    display_round 7 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 7 (by decide)),
    display_round 8 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (hu 8 (by decide))⟩

/-- Item `C/12_D/prose/011` (`companion/chapters/12_D.tex:160`): "The uniquely active gradient at
$z_j$ is $g_j$ for $j=0,1,2$, and $g_0$ at $z_3$." -/
theorem active_gradients :
    (∀ j : Fin 3, ∀ i : Fin 3, i ≠ j →
      dot (SeedOrbit.gradient seedC seedD i) (Failure.seedPoint j.castSucc) <
        dot (SeedOrbit.gradient seedC seedD j) (Failure.seedPoint j.castSucc)) ∧
    ∀ i : Fin 3, i ≠ 0 →
      dot (SeedOrbit.gradient seedC seedD i) (Failure.seedPoint 3) <
        dot (SeedOrbit.gradient seedC seedD 0) (Failure.seedPoint 3) := by
  refine ⟨fun j => ?_, fun i hi => ?_⟩
  · rw [Failure.seedPoint_castSucc]
    exact (source_base_certificate j).active
  · have e3 : Failure.seedPoint 3 = trial seedC seedD seedRatio 2 (length 2) := Failure.seedPoint_succ 2
    rw [e3]
    exact (source_trial_certificate 8).active i hi

/-! ### Section 12.2, derivation and independent checks of the matrix closure

The paragraph of lines 167-189 works "for arbitrary symbolic $(c,d)$ with the denominators
nonzero". Its standing assumptions, in every theorem below: $\beta,\gamma,\widetilde\rho$ with
their defining equations (display `disp/020`, `hβ`, `hγ`, `hρt`); the displayed denominators
$UV(U+129)$, $RUY$, $U(U+129)Y$ nonzero (`hden1`-`hden3`); and the denominators $t=y^Ts$ of the
two updates `D:bfgs` that the identity uses nonzero (`ht1`: the middle update
$\mathcal B(M_1,g_1,g_2,\beta)$, `ht2`: the last update with length $\gamma$). Hypotheses that a
proof does not use start with `_`. -/

/-- Under the standing assumptions of the paragraph, all of $U,V,U+129,R,Y,T,K$ are nonzero (the
update denominators force $\beta\ne0$ and $\widetilde\rho\ne0$). -/
theorem standing_nonzero (c d β γ : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0) :
    AlgebraicSeed.U c d ≠ 0 ∧ AlgebraicSeed.V c d ≠ 0 ∧ AlgebraicSeed.U c d + 129 ≠ 0 ∧
    AlgebraicSeed.R c d ≠ 0 ∧ AlgebraicSeed.Y c d ≠ 0 ∧ AlgebraicSeed.T c d ≠ 0 ∧
    AlgebraicSeed.K c d ≠ 0 := by
  have hUV := left_ne_zero_of_mul hden1
  have hA := right_ne_zero_of_mul hden1
  have hU := left_ne_zero_of_mul hUV
  have hV := right_ne_zero_of_mul hUV
  have hRU := left_ne_zero_of_mul hden2
  have hY := right_ne_zero_of_mul hden2
  have hR := left_ne_zero_of_mul hRU
  have hβ0 : β ≠ 0 := by
    intro h0
    apply ht1
    rw [middle_curvature, h0]
    ring
  have hK : AlgebraicSeed.K c d ≠ 0 := by
    intro h0
    apply hβ0
    rw [hβ, h0]
    ring
  have hβb : β = beta c d := hβ
  have hγb : γ = gamma c d := hγ
  have hT : AlgebraicSeed.T c d ≠ 0 := by
    intro h0
    apply ht2
    rw [Failure.fullUpdate_eq_update, middle_update hβ0 hA, hβb, hγb,
      last_step_generic hU hV hA hR hY, dot_smul_right]
    have hr : rhoTilde c d = 0 := by
      unfold rhoTilde
      rw [h0]
      ring
    rw [hr, zero_mul]
  exact ⟨hU, hV, hA, hR, hY, hT, hK⟩

/-- Item `C/12_D/disp/021` (`companion/chapters/12_D.tex:174-177`): "Direct rational identities
give \[ \mathcal B\bigl(\mathcal B(M_1,g_1,g_2,\beta),g_2,g_0,\gamma\bigr)=\widetilde\rho I." \]
For arbitrary $(c,d)$ under the standing assumptions of the paragraph ($g_2=(c,d)^T$,
$M_1$ = `SeedCycle.M1`). -/
theorem generic_closure (c d β γ ρt : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (_hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0) :
    Failure.fullUpdate (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) g0 γ = ρt • (1 : Mat 2) := by
  obtain ⟨hU, hV, hA, hR, hY, hT, hK⟩ := standing_nonzero c d β γ hβ hγ hden1 hden2 ht1 ht2
  subst hβ hγ hρt
  exact SeedCycle.generic_closure hU hV hA hR hY hT hK

/-- Item `C/12_D/prose/013` (`companion/chapters/12_D.tex:178`): "One way to derive the formulas is
to write the middle update as $C+\beta D$." Under the standing assumptions of the paragraph, the
middle update $\mathcal B(M_1,g_1,g_2,b)$ is affine in the length: for every $b\ne0$ it is $C+bD$
with
$C=\frac{16512}{(U+129)^2}vv^T$, $v=(-(d+1/8),c+1)^T$, and $D=\frac1{256(U+129)}ww^T$,
$w=(127,16)^T$. -/
theorem middle_affine (c d β γ ρt : ℝ)
    (_hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (_hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (_hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (_hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (_hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (_ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (_ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0) :
    ∃ C D : Mat 2, (∀ b : ℝ, b ≠ 0 → Failure.fullUpdate M1 g1 (g2 c d) b = C + b • D) ∧
      C = (16512 / (AlgebraicSeed.U c d + 129) ^ 2) • outer ![-(d + 1/8), c + 1] ![-(d + 1/8), c + 1] ∧
      D = (1 / (256 * (AlgebraicSeed.U c d + 129))) • outer ![127, 16] ![127, 16] := by
  have hA := right_ne_zero_of_mul hden1
  refine ⟨_, _, fun b hb => ?_, rfl, rfl⟩
  rw [Failure.fullUpdate_eq_update, middle_update hb hA, middleMatrix, smul_smul]
  congr 2
  ring

/-- Two vectors of the plane are parallel ($u$ a multiple of $w\ne0$) exactly when their
$2\times2$ determinant vanishes. -/
theorem parallel_iff_det (u w : Vec 2) (hw : w ≠ 0) :
    (∃ t : ℝ, u = t • w) ↔ u 0 * w 1 - u 1 * w 0 = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    by_cases h0 : w 0 = 0
    · have h1 : w 1 ≠ 0 := by
        intro h1
        apply hw
        ext i
        fin_cases i
        · exact h0
        · exact h1
      refine ⟨u 1 / w 1, ?_⟩
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
        rw [h0, mul_zero, sub_zero] at h
        rcases mul_eq_zero.mp h with h2 | h2
        · exact h2
        · exact absurd h2 h1
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
    · refine ⟨u 0 / w 0, ?_⟩
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith

/-- Item `C/12_D/prose/014` (`companion/chapters/12_D.tex:178`): "Requiring $(C+\beta D)g_2$ to be
parallel to $g_0-g_2$ is linear in $\beta$. Its solution is the formula above." With $C$, $D$ of
`middle_affine` and under the standing assumptions of the paragraph: the $2\times2$ determinant
of $(C+bD)g_2$ and $g_0-g_2$ is the affine function $-258RK/(U+129)^2+b\,UV/(256(U+129))$ of the
length $b$, with nonzero slope; and $(C+bD)g_2$ is parallel to $g_0-g_2$ exactly when
$b=\frac{66048RK}{UV(U+129)}$, the formula of $\beta$ (display `disp/020`). -/
theorem parallel_condition (c d β γ ρt : ℝ)
    (_hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (_hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (_hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (_hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (_ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (_ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0)
    (C D : Mat 2)
    (hC : C = (16512 / (AlgebraicSeed.U c d + 129) ^ 2) • outer ![-(d + 1/8), c + 1] ![-(d + 1/8), c + 1])
    (hD : D = (1 / (256 * (AlgebraicSeed.U c d + 129))) • outer ![127, 16] ![127, 16]) :
    (∀ b : ℝ, ((C + b • D) *ᵥ g2 c d) 0 * (g0 - g2 c d) 1 - ((C + b • D) *ᵥ g2 c d) 1 * (g0 - g2 c d) 0 =
      -(258 * AlgebraicSeed.R c d * AlgebraicSeed.K c d) / (AlgebraicSeed.U c d + 129) ^ 2 +
        b * (AlgebraicSeed.U c d * AlgebraicSeed.V c d / (256 * (AlgebraicSeed.U c d + 129)))) ∧
    AlgebraicSeed.U c d * AlgebraicSeed.V c d / (256 * (AlgebraicSeed.U c d + 129)) ≠ 0 ∧
    ∀ b : ℝ, (∃ t : ℝ, (C + b • D) *ᵥ g2 c d = t • (g0 - g2 c d)) ↔
      b = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
        (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)) := by
  have hUV := left_ne_zero_of_mul hden1
  have hA := right_ne_zero_of_mul hden1
  have hY := right_ne_zero_of_mul hden2
  have hdet : ∀ b : ℝ, ((C + b • D) *ᵥ g2 c d) 0 * (g0 - g2 c d) 1 -
      ((C + b • D) *ᵥ g2 c d) 1 * (g0 - g2 c d) 0 =
      -(258 * AlgebraicSeed.R c d * AlgebraicSeed.K c d) / (AlgebraicSeed.U c d + 129) ^ 2 +
        b * (AlgebraicSeed.U c d * AlgebraicSeed.V c d / (256 * (AlgebraicSeed.U c d + 129))) := by
    intro b
    subst hC hD
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, g0, g2, dot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    field_simp
    unfold AlgebraicSeed.R AlgebraicSeed.K AlgebraicSeed.U AlgebraicSeed.V
    ring
  have hslope : AlgebraicSeed.U c d * AlgebraicSeed.V c d / (256 * (AlgebraicSeed.U c d + 129)) ≠ 0 :=
    div_ne_zero hUV (mul_ne_zero (by norm_num) hA)
  have hw : g0 - g2 c d ≠ 0 := by
    intro h0
    apply hY
    have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    simp only [Pi.sub_apply, g0, g2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.zero_apply] at e0 e1
    unfold AlgebraicSeed.Y
    have hc : c = 1 := by linarith
    have hd : d = 0 := by linarith
    rw [hc, hd]
    norm_num
  refine ⟨hdet, hslope, fun b => ?_⟩
  rw [parallel_iff_det _ _ hw, hdet b]
  constructor
  · intro h
    rw [neg_div] at h
    have hb : b = (258 * AlgebraicSeed.R c d * AlgebraicSeed.K c d / (AlgebraicSeed.U c d + 129) ^ 2) /
        (AlgebraicSeed.U c d * AlgebraicSeed.V c d / (256 * (AlgebraicSeed.U c d + 129))) := by
      rw [eq_div_iff hslope]
      linarith
    rw [hb]
    have hU := left_ne_zero_of_mul hUV
    have hV := right_ne_zero_of_mul hUV
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- The matrix $C+\beta D$ of `middle_affine` at the length $\beta$ of display `disp/020` is the
library's `SeedCycle.middleMatrix (beta c d) c d`. -/
theorem middle_sum_eq (c d β : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (C D : Mat 2)
    (hC : C = (16512 / (AlgebraicSeed.U c d + 129) ^ 2) • outer ![-(d + 1/8), c + 1] ![-(d + 1/8), c + 1])
    (hD : D = (1 / (256 * (AlgebraicSeed.U c d + 129))) • outer ![127, 16] ![127, 16]) :
    C + β • D = middleMatrix (beta c d) c d := by
  rw [hC, hD, middleMatrix, ← show β = beta c d from hβ, smul_smul]
  congr 2
  ring

/-- Item `C/12_D/disp/022` (`companion/chapters/12_D.tex:179-181`): "If $w\perp(g_0-g_2)$, set
\[ \widetilde\rho=\frac{w^T(C+\beta D)w}{w^Tw}." \]
Under the standing assumptions of the paragraph, with $C$, $D$ of `middle_affine` and $\beta$ of
display `disp/020`: for every nonzero $w\perp(g_0-g_2)$ this quotient is the $\widetilde\rho$ of
display `disp/020`, $\frac{2064TK}{U(U+129)Y}$ (so the two definitions agree). -/
theorem rho_tilde_rayleigh (c d β γ ρt : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (_hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0)
    (C D : Mat 2)
    (hC : C = (16512 / (AlgebraicSeed.U c d + 129) ^ 2) • outer ![-(d + 1/8), c + 1] ![-(d + 1/8), c + 1])
    (hD : D = (1 / (256 * (AlgebraicSeed.U c d + 129))) • outer ![127, 16] ![127, 16])
    (w : Vec 2) (hw : w ≠ 0) (hperp : dot w (g0 - g2 c d) = 0) :
    ρt = dot w ((C + β • D) *ᵥ w) / dot w w := by
  obtain ⟨hU, hV, hA, -, hY, -, -⟩ := standing_nonzero c d β γ hβ hγ hden1 hden2 ht1 ht2
  rw [middle_sum_eq c d β hβ C D hC hD]
  have hp : w 0 * (1 - c) - w 1 * d = 0 := by
    have h := hperp
    simp only [dot, Fin.sum_univ_two, Pi.sub_apply, g0, g2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h
    linarith
  have hYe : AlgebraicSeed.Y c d = d * d + (1 - c) * (1 - c) := by
    unfold AlgebraicSeed.Y
    ring
  set lam : ℝ := (w 0 * d + w 1 * (1 - c)) / AlgebraicSeed.Y c d with hlam_def
  have hwe : w = lam • ![d, 1 - c] := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, hlam_def]
      rw [div_mul_eq_mul_div, eq_div_iff hY, hYe]
      linear_combination (1 - c) * hp
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, smul_eq_mul, hlam_def]
      rw [div_mul_eq_mul_div, eq_div_iff hY, hYe]
      linear_combination (-d) * hp
  have hlam : lam ≠ 0 := by
    intro h0
    apply hw
    rw [hwe, h0, zero_smul]
  have hee : dot ![d, 1 - c] ![d, 1 - c] = AlgebraicSeed.Y c d := by
    simp only [dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hYe]
  rw [hwe, Matrix.mulVec_smul, dot_smul_right, PlanarUpdate.dot_scale_left, dot_smul_right,
    PlanarUpdate.dot_scale_left, middle_perpendicular_energy hU hV hA, hee, hρt]
  field_simp
  ring

/-- Item `C/12_D/prose/015` (`companion/chapters/12_D.tex:182`): "[set $\widetilde\rho$] and
choose $\gamma$ so that the last displacement is $\widetilde\rho(g_0-g_2)$. The last update then
gives $\widetilde\rho I$: its two projection factors are the orthogonal projector onto
$(g_0-g_2)^\perp$."

Under the standing assumptions of the paragraph, with $\gamma$ of display `disp/020`: the last
displacement $s=-\gamma\mathcal B(M_1,g_1,g_2,\beta)g_2$ is $\widetilde\rho\,y$, $y=g_0-g_2$; the
last update is $\widetilde\rho I$; both projection factors $I-sy^T/(y^Ts)$ and
$I-ys^T/(y^Ts)$ of `D:bfgs` equal $P=I-yy^T/(y^Ty)$; and $P$ is the orthogonal projector onto
$y^\perp$ ($P^2=P$, $P^T=P$, $Py=0$, $Pw=w$ for $w\perp y$). -/
theorem last_update_projector (c d β γ ρt : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0)
    (s y : Vec 2) (hs : s = bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ)
    (hy : y = g0 - g2 c d) (P : Mat 2) (hP : P = 1 - (dot y y)⁻¹ • outer y y) :
    s = ρt • y ∧
    Failure.fullUpdate (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) g0 γ = ρt • (1 : Mat 2) ∧
    1 - (dot y s)⁻¹ • outer s y = P ∧ 1 - (dot y s)⁻¹ • outer y s = P ∧
    P * P = P ∧ Pᵀ = P ∧ P *ᵥ y = 0 ∧ ∀ w : Vec 2, dot w y = 0 → P *ᵥ w = w := by
  obtain ⟨hU, hV, hA, hR, hY, hT, hK⟩ := standing_nonzero c d β γ hβ hγ hden1 hden2 ht1 ht2
  have hβ0 : β ≠ 0 := by
    rw [hβ]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hR) hK) hden1
  have hs' : s = ρt • y := by
    rw [hs, hy, Failure.fullUpdate_eq_update, middle_update hβ0 hA, show β = beta c d from hβ,
      show γ = gamma c d from hγ, last_step_generic hU hV hA hR hY, hρt]
    rfl
  have hρ0 : ρt ≠ 0 := by
    rw [hρt]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hT) hK) hden3
  have hyy : dot y y = AlgebraicSeed.Y c d := by
    rw [hy]
    exact last_curvature_norm c d
  have hyy0 : dot y y ≠ 0 := hyy ▸ hY
  have hfac : (dot y (ρt • y))⁻¹ * ρt = (dot y y)⁻¹ := by
    rw [dot_smul_right]
    field_simp
  refine ⟨hs', generic_closure c d β γ ρt hβ hγ hρt hden1 hden2 hden3 ht1 ht2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP, hs', outer_scale_left, smul_smul, hfac]
  · rw [hP, hs', outer_scale_right, smul_smul, hfac]
  · rw [hP]
    have hyy' : y 0 * y 0 + y 1 * y 1 ≠ 0 := by
      simpa only [dot, Fin.sum_univ_two] using hyy0
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, outer, dot, Matrix.one_apply, Matrix.sub_apply] <;>
      field_simp <;> ring
  · rw [hP, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, outer_transpose]
  · rw [hP, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, smul_smul,
      inv_mul_cancel₀ hyy0, one_smul, sub_self]
  · intro w hw
    rw [hP, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec]
    have hwy : dot y w = 0 := by
      rw [← hw]
      simp only [dot]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hwy, zero_smul, smul_zero, sub_zero]

/-- Item `C/12_D/prose/016` (`companion/chapters/12_D.tex:184`): "Equations~\eqref{D:polys} are
exactly $\beta=1/4$ and $\gamma=1/16$." Under the standing assumptions of the paragraph,
$264192RK-UV(U+129)=0$ if and only if $\beta=1/4$, and $16VTK-RUY=0$ if and only if
$\gamma=1/16$. -/
theorem polys_iff (c d β γ ρt : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (_hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (_hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0) :
    (264192 * AlgebraicSeed.R c d * AlgebraicSeed.K c d -
        AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) = 0 ↔ β = 1/4) ∧
    (16 * AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d -
        AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d = 0 ↔ γ = 1/16) := by
  obtain ⟨hU, hV, hA, hR, hY, -, -⟩ := standing_nonzero c d β γ hβ hγ hden1 hden2 ht1 ht2
  rw [show β = beta c d from hβ, show γ = gamma c d from hγ]
  exact ⟨(DLiteralIdentities.beta_quarter_iff hU hV hA).symm,
    (DLiteralIdentities.gamma_sixteenth_iff hU hR hY).symm⟩

/-- Item `C/12_D/disp/023` (`companion/chapters/12_D.tex:185-188`):
\[ \widetilde\rho-\rho=\frac{2064R}{V(U+129)}\left(\gamma-\frac1{16}\right), \]
with $\rho=129R/(V(U+129))$ of `D:rho` as a function of $(c,d)$, under the standing assumptions
of the paragraph. -/
theorem rho_difference (c d β γ ρt : ℝ)
    (hβ : β = 66048 * AlgebraicSeed.R c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)))
    (hγ : γ = AlgebraicSeed.V c d * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d))
    (hρt : ρt = 2064 * AlgebraicSeed.T c d * AlgebraicSeed.K c d /
      (AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d))
    (hden1 : AlgebraicSeed.U c d * AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129) ≠ 0)
    (hden2 : AlgebraicSeed.R c d * AlgebraicSeed.U c d * AlgebraicSeed.Y c d ≠ 0)
    (_hden3 : AlgebraicSeed.U c d * (AlgebraicSeed.U c d + 129) * AlgebraicSeed.Y c d ≠ 0)
    (ht1 : dot (g2 c d - g1) (bfgsStep M1 g1 β) ≠ 0)
    (ht2 : dot (g0 - g2 c d) (bfgsStep (Failure.fullUpdate M1 g1 (g2 c d) β) (g2 c d) γ) ≠ 0) :
    ρt - 129 * AlgebraicSeed.R c d / (AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)) =
      2064 * AlgebraicSeed.R c d / (AlgebraicSeed.V c d * (AlgebraicSeed.U c d + 129)) * (γ - 1/16) := by
  obtain ⟨hU, hV, hA, hR, hY, -, -⟩ := standing_nonzero c d β γ hβ hγ hden1 hden2 ht1 ht2
  rw [show ρt = rhoTilde c d from hρt, show γ = gamma c d from hγ]
  exact SeedCycle.rho_difference hU hV hA hR hY

/-- Item `C/12_D/prose/018` (`companion/chapters/12_D.tex:189`): "The Lean formalization checks
these exact identities from the actual full-BFGS formulas, together with the secant identity and
the equivalence of the inverse and Hessian updates. It proves the required positive curvatures
and positive definiteness, including the stated algebraic-root box." (A description of the
formalization; its mathematics.)

At the root, for each phase $j$ with $M_j$, $g_j$, $g_{j+1}$ ($g_3=g_0$), $\alpha_j\in
\{1,1/4,1/16\}$, $s_j=-\alpha_jM_jg_j$ and $y_j=g_{j+1}-g_j$: the curvature $y_j^Ts_j$ is
positive; the update $H_+=\mathcal B(M_j,g_j,g_{j+1},\alpha_j)$ satisfies the secant identity
$H_+y_j=s_j$; its inverse is the Hessian (direct) BFGS update of $B=M_j^{-1}$,
$H_+^{-1}=B-\frac{g_jg_j^T}{g_j^TM_jg_j}+\frac{y_jy_j^T}{y_j^Ts_j}$ (which is
$B-\frac{Bs_js_j^TB}{s_j^TBs_j}+\frac{y_jy_j^T}{y_j^Ts_j}$ since $Bs_j=-\alpha_jg_j$); and $M_j$ and
$H_+$ are positive definite. At every point $(c,d)$ of the root box, the matrices $M_0,M_1,M_2$
built from $(c,d)$ and the last update are positive definite and the three curvatures are
positive. -/
theorem formal_checks :
    (∀ j : Fin 3,
      0 < dot (SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j)
        (bfgsStep (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) (length j)) ∧
      Failure.fullUpdate (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j)
          (SeedOrbit.gradient seedC seedD (nextPhase j)) (length j) *ᵥ
        (SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j) =
        bfgsStep (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) (length j) ∧
      (Failure.fullUpdate (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j)
          (SeedOrbit.gradient seedC seedD (nextPhase j)) (length j))⁻¹ =
        (metric seedC seedD j)⁻¹ -
          (metricEnergy (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j))⁻¹ •
            outer (SeedOrbit.gradient seedC seedD j) (SeedOrbit.gradient seedC seedD j) +
          (dot (SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j)
            (bfgsStep (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) (length j)))⁻¹ •
            outer (SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j)
              (SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j) ∧
      (metric seedC seedD j).PosDef ∧
      (Failure.fullUpdate (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j)
          (SeedOrbit.gradient seedC seedD (nextPhase j)) (length j)).PosDef) ∧
    ∀ x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 →
      (∀ j : Fin 3, (metric (x 0) (x 1) j).PosDef) ∧
      0 < dot (g1 - g0) (bfgsStep (1 : Mat 2) g0 1) ∧
      0 < dot (g2 (x 0) (x 1) - g1) (bfgsStep M1 g1 (1/4)) ∧
      0 < dot (g0 - g2 (x 0) (x 1)) (bfgsStep (metric (x 0) (x 1) 2) (g2 (x 0) (x 1)) (1/16)) ∧
      (Failure.fullUpdate (metric (x 0) (x 1) 2) (g2 (x 0) (x 1)) g0 (1/16)).PosDef := by
  refine ⟨fun j => ?_, fun x hx => ?_⟩
  · have hc := source_accepted_certificate j
    have hw := hc.wolfe rfl
    have hd := hc.descent
    have hstep := source_direction j (length j)
    have hcurv : 0 < dot (SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j)
        (bfgsStep (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) (length j)) := by
      rw [hstep, show ∀ u v w : Vec 2, dot (u - v) w = dot u w - dot v w from
        fun u v w => sub_dotProduct u v w]
      linarith
    have hM := source_metric_posDef j
    refine ⟨hcurv, EReconstruction.inverse_update_secant _ _ _ hcurv.ne',
      hessianUpdate hM (source_gradient_nonzero j) _ (source_length_pos j) hcurv, hM,
      inverseBFGS_posDef hM _ _ hcurv⟩
  · obtain ⟨hmet, h0, h1, hlast, hfin, -, -⟩ := DBoxDenominators.sourceBoxDenominators x hx
    exact ⟨fun j => (hmet j).1, h0, h1, lt_trans (by norm_num) hlast, hfin⟩

/-! ### Section 12.3: every deterministic oracle decision is certified

Notation: $z_j$ = `Failure.seedPoint j` (the points of `D:x0`), $p_j=-M_jg_j$ =
`Failure.seedDir j`, $s_j$ = `Failure.seedStep j`, $g_j$ = `SeedOrbit.gradient seedC seedD j`
(`Failure.seedSlope j` with $g_3=g_0$), $G$ = `objective seedC seedD`. The rows of the table are
`q : Fin 9` with phase `trialPhase q`, trial length `trialLength q`, active branch
`trialActive q` and decision `trialAccept q`; the trial point of a row is
$z_j+\alpha p_j$. -/

/-- The trial point $z_j+\alpha p_j$ of row `q` of the table of Section 12.3. -/
def query (q : Fin 9) : Vec 2 :=
  Failure.seedPoint (trialPhase q).castSucc + trialLength q • Failure.seedDir (trialPhase q)

/-- The specified strict search from $(z_j,M_j)$ on $G$ makes the trials of phase $j$ of the table
and accepts the last one, for every $0<c_1\le1/3$ and $c_2>0$. -/
theorem seed_search {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (j : Fin 3) :
    DeterministicLineSearch.fromMetric (objective seedC seedD) (Failure.seedPoint j.castSucc)
      (metric seedC seedD j) c₁ c₂ 5 = (some (length j), trialHistory j) := by
  have h := orbit_search hc₁ hc₁' hc₂ j.val
  obtain ⟨hx, hH, -, hα⟩ := orbit_phase_parameters 0 j
  simp only [mul_zero, zero_add, pow_zero, one_smul] at hx hH hα
  rw [hx, hH, hα, Failure.phase_val] at h
  rw [Failure.seedPoint_castSucc]
  exact h

/-- The decisions of the specified strict search at the nine rows of the table, for every
$0<c_1\le1/3$ and $c_2>0$: both strict tests hold at an accepted row, the strict Armijo test
fails at a rejected row. -/
theorem table_decisions {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (q : Fin 9) :
    (trialAccept q = true →
      DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
        (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ∧
      DeterministicLineSearch.Wolfe (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
        (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₂ (trialLength q)) ∧
    (trialAccept q = false →
      ¬ DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
        (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q)) := by
  rw [Failure.seedPoint_castSucc, Failure.seedDir_eq]
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨ha, hw⟩ := source_scaled_accept one_pos hc₁ hc₁' hc₂ q hq
    simp only [one_smul] at ha hw
    exact ⟨ha, hw⟩
  · have h := source_scaled_reject one_pos hc₁ q hq
    simp only [one_smul] at h
    exact h

/-- Item `C/12_D/prose/020` (`companion/chapters/12_D.tex:204`): "At each rejected trial, the
objective is strictly greater than the current value, not merely greater than the Armijo
threshold." At each rejected row, $G(z_j)<G(z_j+\alpha p_j)$, while the Armijo threshold
$G(z_j)+c_1\alpha g_j^Tp_j$ lies below the current value for every $c_1>0$. -/
theorem rejected_above (q : Fin 9) (hq : trialAccept q = false) :
    objective seedC seedD (Failure.seedPoint (trialPhase q).castSucc) < objective seedC seedD (query q) ∧
    ∀ c₁ : ℝ, 0 < c₁ →
      objective seedC seedD (Failure.seedPoint (trialPhase q).castSucc) +
          c₁ * trialLength q * dot (SeedOrbit.gradient seedC seedD (trialPhase q)) (Failure.seedDir (trialPhase q)) <
        objective seedC seedD (Failure.seedPoint (trialPhase q).castSucc) := by
  refine ⟨Failure.seed_rejections_raise q hq, fun c₁ hc₁ => ?_⟩
  have hd := (source_trial_certificate q).descent
  rw [← Failure.seedDir_eq] at hd
  rw [mul_assoc, ← dot_smul_right]
  linarith [mul_neg_of_pos_of_neg hc₁ hd]

/-- The column $G(z_j+\alpha p_j)$ of the table of Section 12.3, as printed. -/
def tableValue : Fin 9 → ℝ :=
  ![0.121854550561, 0.384526374149, 0.136479499149, 0.072321707900, 0.668886093720,
    0.340671077685, 0.176563569667, 0.094509815658, 0.053482938654]

/-- The unit of the last printed digit of the twelve-digit decimals. -/
theorem unit_twelve (i : Fin 33) (hi : i ≠ 0) : DDisplayPrecision.unit i = 1 / 10 ^ 12 := by
  simp [DDisplayPrecision.unit, hi]

/-- Each printed value of the column $G(z_j+\alpha p_j)$ is the nearest rounding of the actual
value: the error is less than $10^{-12}/2$. -/
theorem table_value_round (q : Fin 9) :
    |objective seedC seedD (query q) - tableValue q| < 1 / 10 ^ 12 / 2 := by
  rw [query, Failure.table_trial_value]
  fin_cases q
  · exact display_round 9 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 9 (by decide))
  · exact display_round 10 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 10 (by decide))
  · exact display_round 11 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 11 (by decide))
  · exact display_round 12 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 12 (by decide))
  · exact display_round 13 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 13 (by decide))
  · exact display_round 14 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 14 (by decide))
  · exact display_round 15 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 15 (by decide))
  · exact display_round 16 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 16 (by decide))
  · exact display_round 17 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num [tableValue])
      (unit_twelve 17 (by decide))

/-- Item `C/12_D/prose/021` (`companion/chapters/12_D.tex:205-218`), the table of Section 12.3
(an unnumbered tabular), with line 204: "Use $c_1=10^{-4}$ and $c_2=1/2$ for the displayed
table. The line searches below use $p_j=-M_jg_j$."

Columns "Phase", "Trial $\alpha$", "Active branch" and "Decision" are `trialPhase`,
`trialLength`, `trialActive`, `trialAccept` (first four conjuncts, literally the table); the
active branch of each trial point is strictly active; the column $G(z_j+\alpha p_j)$
(`tableValue`) is the nearest rounding of the actual value; with $c_1=10^{-4}$, $c_2=1/2$ the
strict Armijo and weak Wolfe tests hold at the accepted rows and the strict Armijo test fails at
the rejected rows ("Armijo rejection"); and the specified strict search from $(z_j,M_j)$ makes
exactly the trials of the phase-$j$ rows, in order, and accepts the last one. -/
theorem trial_table :
    trialPhase = ![0, 1, 1, 1, 2, 2, 2, 2, 2] ∧
    trialLength = ![1, 1, 1/2, 1/4, 1, 1/2, 1/4, 1/8, 1/16] ∧
    trialActive = ![1, 0, 0, 2, 0, 0, 0, 0, 0] ∧
    trialAccept = ![true, false, false, true, false, false, false, false, true] ∧
    (∀ q : Fin 9, ∀ k, k ≠ trialActive q →
      dot (SeedOrbit.gradient seedC seedD k) (query q) <
        dot (SeedOrbit.gradient seedC seedD (trialActive q)) (query q)) ∧
    (∀ q : Fin 9, |objective seedC seedD (query q) - tableValue q| < 1 / 10 ^ 12 / 2) ∧
    (∀ q : Fin 9,
      (trialAccept q = true →
        DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
          (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) (1 / 10 ^ 4)
          (trialLength q) ∧
        DeterministicLineSearch.Wolfe (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
          (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) (1 / 2)
          (trialLength q)) ∧
      (trialAccept q = false →
        ¬ DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
          (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) (1 / 10 ^ 4)
          (trialLength q))) ∧
    (∀ j : Fin 3, DeterministicLineSearch.fromMetric (objective seedC seedD) (Failure.seedPoint j.castSucc)
      (metric seedC seedD j) (1 / 10 ^ 4) (1 / 2) 5 = (some (length j), trialHistory j)) ∧
    trialHistory = ![[trialLength 0], [trialLength 1, trialLength 2, trialLength 3],
      [trialLength 4, trialLength 5, trialLength 6, trialLength 7, trialLength 8]] := by
  have hc₁ : (0 : ℝ) < 1 / 10 ^ 4 := by norm_num
  have hc₁' : (1 / 10 ^ 4 : ℝ) ≤ 1/3 := by norm_num
  have hc₂ : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨rfl, rfl, rfl, rfl, fun q => ?_, table_value_round,
    fun q => table_decisions hc₁ hc₁' hc₂ q, fun j => seed_search hc₁ hc₁' hc₂ j, ?_⟩
  · rw [query, Failure.seed_query_eq]
    exact (source_trial_certificate q).active
  · funext j
    fin_cases j <;> rfl

/-- Item `C/12_D/disp/024` (`companion/chapters/12_D.tex:220-222`): "The starting values in the
three phases are approximately $(0.888432624149,\;0.121854550561,\;0.072321707900)$." The values
$G(z_0),G(z_1),G(z_2)$ round to the printed decimals (error below $10^{-12}/2$). -/
theorem starting_values :
    |objective seedC seedD (Failure.seedPoint 0) - 0.888432624149| < 1 / 10 ^ 12 / 2 ∧
    |objective seedC seedD (Failure.seedPoint 1) - 0.121854550561| < 1 / 10 ^ 12 / 2 ∧
    |objective seedC seedD (Failure.seedPoint 2) - 0.072321707900| < 1 / 10 ^ 12 / 2 := by
  have e0 : Failure.seedPoint 0 = point seedC seedD seedRatio 0 := Failure.seedStart_eq
  have e1 : Failure.seedPoint 1 = point seedC seedD seedRatio 1 := Failure.seedPoint_castSucc 1
  have e2 : Failure.seedPoint 2 = point seedC seedD seedRatio 2 := Failure.seedPoint_castSucc 2
  rw [e0, e1, e2]
  exact ⟨display_round 18 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 18 (by decide)),
    display_round 19 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 19 (by decide)),
    display_round 20 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 20 (by decide))⟩

/-- The Wolfe ratio of phase $j$ is the library's certified display value
`DDisplayActual.wolfeRatio j`. -/
theorem wolfe_ratio_eq (j : Fin 3) :
    dot (SeedOrbit.gradient seedC seedD (nextPhase j)) (Failure.seedStep j) /
        dot (SeedOrbit.gradient seedC seedD j) (Failure.seedStep j) = DDisplayActual.wolfeRatio j := by
  rw [Failure.seedStep_eq]
  rfl

/-- Item `C/12_D/disp/025` (`companion/chapters/12_D.tex:224-232`): "The ratios at the accepted
steps are" the table of $\frac{G(z_j)-G(z_{j+1})}{-g_j^Ts_j}$ and
$\frac{g_{j+1}^Ts_j}{g_j^Ts_j}$, $j=0,1,2$ ($g_3=g_0$). The printed decimals are the nearest
roundings (error below $10^{-12}/2$); the entry $-1$ is exact. -/
theorem accepted_ratios :
    |(objective seedC seedD (Failure.seedPoint 0) - objective seedC seedD (Failure.seedPoint 1)) /
        (-dot g0 (Failure.seedStep 0)) - 0.766578073588| < 1 / 10 ^ 12 / 2 ∧
    dot g1 (Failure.seedStep 0) / dot g0 (Failure.seedStep 0) = -1 ∧
    |(objective seedC seedD (Failure.seedPoint 1) - objective seedC seedD (Failure.seedPoint 2)) /
        (-dot g1 (Failure.seedStep 1)) - 0.393190937094| < 1 / 10 ^ 12 / 2 ∧
    |dot (g2 seedC seedD) (Failure.seedStep 1) / dot g1 (Failure.seedStep 1) - (-0.186383158092)| <
      1 / 10 ^ 12 / 2 ∧
    |(objective seedC seedD (Failure.seedPoint 2) - objective seedC seedD (Failure.seedPoint 3)) /
        (-dot (g2 seedC seedD) (Failure.seedStep 2)) - 0.375205963573| < 1 / 10 ^ 12 / 2 ∧
    |dot g0 (Failure.seedStep 2) / dot (g2 seedC seedD) (Failure.seedStep 2) - (-0.817119670485)| <
      1 / 10 ^ 12 / 2 := by
  refine ⟨display_round 21 (Failure.accepted_armijo_ratio_eq 0).symm
      (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (unit_twelve 21 (by decide)),
    by norm_num [Failure.seedStep, dot, Fin.sum_univ_two, g0, g1],
    display_round 23 (Failure.accepted_armijo_ratio_eq 1).symm
      (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (unit_twelve 23 (by decide)),
    display_round 24 (wolfe_ratio_eq 1).symm
      (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (unit_twelve 24 (by decide)),
    display_round 25 (Failure.accepted_armijo_ratio_eq 2).symm
      (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (unit_twelve 25 (by decide)),
    display_round 26 (wolfe_ratio_eq 2).symm
      (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num) (unit_twelve 26 (by decide))⟩

/-- Item `C/12_D/prose/024` (`companion/chapters/12_D.tex:233`): "In particular, each accepted
Armijo ratio exceeds $1/3$, and every accepted Wolfe ratio is negative." For $j=0,1,2$, with
$g_3=g_0$. -/
theorem ratio_signs (j : Fin 3) :
    1/3 < (objective seedC seedD (Failure.seedPoint j.castSucc) -
        objective seedC seedD (Failure.seedPoint j.succ)) /
      (-dot (Failure.seedSlope j.castSucc) (Failure.seedStep j)) ∧
    dot (Failure.seedSlope j.succ) (Failure.seedStep j) /
      dot (Failure.seedSlope j.castSucc) (Failure.seedStep j) < 0 := by
  obtain ⟨h1, h2, h3⟩ := Failure.seed_margins j
  refine ⟨?_, div_neg_of_pos_of_neg h2 h3⟩
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- Item `C/12_D/prose/026` (`companion/chapters/12_D.tex:233`): "Therefore the identical trial
tree works for \emph{all} $0<c_1\le1/3$ and $c_1<c_2<1$." For every such pair, the decisions of
the strict tests at the nine rows are those of the table, and the specified strict search from
$(z_j,M_j)$ makes the trials of phase $j$ and accepts the last. -/
theorem trial_tree_all (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (_hc₂ : c₂ < 1) :
    (∀ q : Fin 9,
      (trialAccept q = true →
        DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
          (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ∧
        DeterministicLineSearch.Wolfe (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
          (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₂ (trialLength q)) ∧
      (trialAccept q = false →
        ¬ DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint (trialPhase q).castSucc)
          (Failure.seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁
          (trialLength q))) ∧
    ∀ j : Fin 3, DeterministicLineSearch.fromMetric (objective seedC seedD) (Failure.seedPoint j.castSucc)
      (metric seedC seedD j) c₁ c₂ 5 = (some (length j), trialHistory j) :=
  ⟨fun q => table_decisions hc₁ hc₁' (hc₁.trans hc) q, fun j => seed_search hc₁ hc₁' (hc₁.trans hc) j⟩

/-- Item `C/12_D/disp/026` (`companion/chapters/12_D.tex:236-240`), equation `D:trialbounds`, with
Item `C/12_D/prose/028` (`companion/chapters/12_D.tex:235`) ("All nine trial points have a unique
active branch") and Item `C/12_D/prose/029` (`companion/chapters/12_D.tex:241`) ("The accepted
points satisfy these bounds as well"): every trial point $z_{\rm trial}$ of the table and every
point $z_0,\dots,z_3$ of the cycle (the starting and accepted points) has a strictly active
branch and satisfies
\[ |g_i^Tz|<3\quad(i=0,1,2),\qquad z_2<2,\qquad G(z)>0. \]
($z_2$ is the second coordinate `z 1`.) -/
theorem trial_bounds :
    ∀ z ∈ Set.range query ∪ Set.range Failure.seedPoint,
      (∃ i : Fin 3, ∀ k, k ≠ i →
        dot (SeedOrbit.gradient seedC seedD k) z < dot (SeedOrbit.gradient seedC seedD i) z) ∧
      (∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) z| < 3) ∧ z 1 < 2 ∧
      0 < objective seedC seedD z := by
  have hq : ∀ q : Fin 9, query q ∈ Set.range (fun j : Fin 3 => Failure.seedPoint j.castSucc) ∪
      Set.range (fun q : Fin 9 =>
        Failure.seedPoint (trialPhase q).castSucc + trialLength q • Failure.seedDir (trialPhase q)) :=
    fun q => Or.inr ⟨q, rfl⟩
  have h3 : Failure.seedPoint 3 = query 8 := by
    rw [query, Failure.seed_query_eq 8, show Failure.seedPoint 3 = Failure.seedPoint (2 : Fin 3).succ from rfl,
      Failure.seedPoint_succ]
    rfl
  rintro z (⟨q, rfl⟩ | ⟨j, rfl⟩)
  · exact Failure.seed_query_bounds _ (hq q)
  · fin_cases j
    · exact Failure.seed_query_bounds _ (Or.inl ⟨0, rfl⟩)
    · exact Failure.seed_query_bounds _ (Or.inl ⟨1, rfl⟩)
    · exact Failure.seed_query_bounds _ (Or.inl ⟨2, rfl⟩)
    · have h := Failure.seed_query_bounds _ (hq 8)
      rw [← h3] at h
      exact h

/-- Item `C/12_D/disp/027` (`companion/chapters/12_D.tex:244-246`): "Positive homogeneity and
\eqref{D:closure}--\eqref{D:x0} prove by induction that the deterministic full-BFGS run on $G$ is
\[ x_{3m+j}=\rho^mz_j,\qquad H_{3m+j}=\rho^mM_j." \]
For every $0<c_1\le1/3$, $c_1<c_2<1$ (in particular $c_1=10^{-4}$, $c_2=1/2$), the run produced
on $G$ by the specified strict search from $x_0=z_0$, $H_0=I$ (any trial budget $N\ge5$) is
unique, is the library's seed run (iterates `orbitPoint`, matrices `orbitMetric`, gradients
`orbitGradient`), and satisfies the display. -/
theorem cone_orbit (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 (objective seedC seedD),
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = Failure.seedPoint 0 ∧ R.H 0 = 1 ∧
      R.x = orbitPoint ∧ R.H = orbitMetric ∧ R.g = orbitGradient ∧
      (∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ N =
        (some (R.α k), trialHistory (phase k))) ∧
      (∀ R' : AdmissibleBFGSRun 2 (objective seedC seedD), R'.x 0 = Failure.seedPoint 0 → R'.H 0 = 1 →
        (∀ k, ∃ N L, DeterministicLineSearch.fromMetric (objective seedC seedD) (R'.x k) (R'.H k) c₁ c₂ N =
          (some (R'.α k), L)) → R'.x = R.x ∧ R'.H = R.H) ∧
      ∀ (m : ℕ) (j : Fin 3), R.x (3 * m + j) = seedRatio ^ m • Failure.seedPoint j.castSucc ∧
        R.H (3 * m + j) = seedRatio ^ m • metric seedC seedD j := by
  have hH0 : (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 :=
    (actual_run_failure hc₁ hc₁' hc hc₂).1
  have hs : ∀ k, DeterministicLineSearch.fromMetric (objective seedC seedD)
      ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).x k) ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5 =
      (some ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).α k), trialHistory (phase k)) :=
    fun k => orbit_search hc₁ hc₁' (hc₁.trans hc) k
  refine ⟨SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, Failure.seedPoint_zero_eq.symm, hH0, rfl, rfl,
    rfl, fun k N hN => fromMetric_fuel_mono (hs k) hN, ?_, fun m j => ?_⟩
  · intro R' hx' hH' hs'
    obtain ⟨h1, h2, -, -⟩ := implemented_run_unique R' (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂)
      (hx'.trans Failure.seedPoint_zero_eq) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, hs k⟩)
    exact ⟨h1, h2⟩
  · obtain ⟨hx, hH, -, -⟩ := orbit_phase_parameters m j
    exact ⟨hx.trans (by rw [Failure.seedPoint_castSucc]), hH⟩

/-- Item `C/12_D/prose/030` (`companion/chapters/12_D.tex:247`): "Every trial at the
corresponding phase is exactly $\rho^m$ times its listed base trial. All comparison quantities
scale by $\rho^m$, preserving every decision, not only acceptance at the selected length."

For the iterate $k=3m+j$ of the run on $G$ ($x_k=\rho^mz_j$, $H_k=\rho^mM_j$, $g_k=g_j$) and every
row $q$ of phase $j$: the trial point is $\rho^m(z_j+\alpha p_j)$; the search direction is
$\rho^mp_j$; the function difference and the gradient--direction products scale by $\rho^m$; and
the strict Armijo and weak Wolfe tests decide as at the base point, for all constants. -/
theorem cone_scaling (m : ℕ) (j : Fin 3) (q : Fin 9) (hq : trialPhase q = j) (c₁ c₂ : ℝ) :
    orbitPoint (3 * m + j) + trialLength q • bfgsStep (orbitMetric (3 * m + j)) (orbitGradient (3 * m + j)) 1 =
      seedRatio ^ m • (Failure.seedPoint j.castSucc + trialLength q • Failure.seedDir j) ∧
    bfgsStep (orbitMetric (3 * m + j)) (orbitGradient (3 * m + j)) 1 = seedRatio ^ m • Failure.seedDir j ∧
    objective seedC seedD (seedRatio ^ m • (Failure.seedPoint j.castSucc + trialLength q • Failure.seedDir j)) -
        objective seedC seedD (seedRatio ^ m • Failure.seedPoint j.castSucc) =
      seedRatio ^ m * (objective seedC seedD (Failure.seedPoint j.castSucc + trialLength q • Failure.seedDir j) -
        objective seedC seedD (Failure.seedPoint j.castSucc)) ∧
    (∀ i : Fin 3, dot (SeedOrbit.gradient seedC seedD i) (seedRatio ^ m • Failure.seedDir j) =
      seedRatio ^ m * dot (SeedOrbit.gradient seedC seedD i) (Failure.seedDir j)) ∧
    (DeterministicLineSearch.Armijo (objective seedC seedD) (seedRatio ^ m • Failure.seedPoint j.castSucc)
        (seedRatio ^ m • Failure.seedDir j) (SeedOrbit.gradient seedC seedD j) c₁ (trialLength q) ↔
      DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint j.castSucc) (Failure.seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₁ (trialLength q)) ∧
    (DeterministicLineSearch.Wolfe (objective seedC seedD) (seedRatio ^ m • Failure.seedPoint j.castSucc)
        (seedRatio ^ m • Failure.seedDir j) (SeedOrbit.gradient seedC seedD j) c₂ (trialLength q) ↔
      DeterministicLineSearch.Wolfe (objective seedC seedD) (Failure.seedPoint j.castSucc) (Failure.seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₂ (trialLength q)) := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, -, -, -⟩ := Failure.cone_orbit_scaling m j q hq c₁ c₂ 0
  subst hq
  have hρ : 0 < seedRatio ^ m := pow_pos source_ratio_pos_lt_one.1 m
  have hquery : Failure.seedPoint (trialPhase q).castSucc + trialLength q • Failure.seedDir (trialPhase q) =
      trial seedC seedD seedRatio (trialPhase q) (trialLength q) := Failure.seed_query_eq q
  have htrialA := (source_trial_certificate q).active
  have htrial : HasFDerivAt (objective seedC seedD)
      (gradientFunctional (SeedOrbit.gradient seedC seedD (trialActive q)))
      (seedRatio ^ m • (Failure.seedPoint (trialPhase q).castSucc + trialLength q • Failure.seedDir (trialPhase q))) := by
    rw [hquery]
    exact hasGradient_of_active (htrialA.scale hρ)
  have hstep' : bfgsStep (orbitMetric (3 * m + (trialPhase q))) (orbitGradient (3 * m + (trialPhase q))) 1 =
      seedRatio ^ m • Failure.seedDir (trialPhase q) := by
    obtain ⟨-, hH, hg, -⟩ := orbit_phase_parameters m (trialPhase q)
    rw [hH, hg, h8]
  refine ⟨h3, hstep', h6, h7, ?_, ?_⟩
  · unfold DeterministicLineSearch.Armijo
    rw [SeedOrbit.scaled_trial, Failure.seed_objective_homogeneous hρ.le,
      Failure.seed_objective_homogeneous hρ.le, dot_smul_right]
    constructor
    · intro h
      have h' : seedRatio ^ m * objective seedC seedD
          (Failure.seedPoint (trialPhase q).castSucc + trialLength q • Failure.seedDir (trialPhase q)) <
          seedRatio ^ m * (objective seedC seedD (Failure.seedPoint (trialPhase q).castSucc) +
            c₁ * trialLength q * dot (SeedOrbit.gradient seedC seedD (trialPhase q))
              (Failure.seedDir (trialPhase q))) := by linarith
      exact lt_of_mul_lt_mul_left h' hρ.le
    · intro h
      nlinarith [mul_lt_mul_of_pos_left h hρ]
  · unfold DeterministicLineSearch.Wolfe
    rw [SeedOrbit.scaled_trial, DeterministicLineSearch.actual_coordinateGradient htrial,
      dot_smul_right, dot_smul_right]
    have hq' : coordinateGradient (objective seedC seedD)
        (Failure.seedPoint (trialPhase q).castSucc + trialLength q • Failure.seedDir (trialPhase q)) =
        SeedOrbit.gradient seedC seedD (trialActive q) := by
      rw [hquery]
      exact DeterministicLineSearch.actual_coordinateGradient (hasGradient_of_active htrialA)
    rw [hq']
    constructor
    · intro h
      have h' : seedRatio ^ m * (c₂ * dot (SeedOrbit.gradient seedC seedD (trialPhase q))
          (Failure.seedDir (trialPhase q))) < seedRatio ^ m * dot (SeedOrbit.gradient seedC seedD (trialActive q))
          (Failure.seedDir (trialPhase q)) := by linarith
      exact lt_of_mul_lt_mul_left h' hρ.le
    · intro h
      nlinarith [mul_lt_mul_of_pos_left h hρ]

/-- Item `C/12_D/prose/031` (`companion/chapters/12_D.tex:247`): "Thus $x_k\to0$ and
$G(x_k)\downarrow0$." For the run on $G$ (`cone_orbit`): the iterates tend to $0$ and the values
are positive, strictly decreasing and tend to $0$. -/
theorem cone_limit :
    Tendsto orbitPoint atTop (𝓝 0) ∧ (∀ k, 0 < objective seedC seedD (orbitPoint k)) ∧
    (∀ k, objective seedC seedD (orbitPoint (k + 1)) < objective seedC seedD (orbitPoint k)) ∧
    Tendsto (fun k => objective seedC seedD (orbitPoint k)) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < 1/4 ∧ (1/4 : ℝ) ≤ 1/3 ∧ (1/4 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := by norm_num
  obtain ⟨-, hx, hF, hpos, hdec, -⟩ := actual_run_failure hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  exact ⟨hx, hpos, hdec, hF⟩

/-- Item `C/12_D/prose/032` (`companion/chapters/12_D.tex:249`): "This limit is nonstationary":
$0\notin\partial G(0)$. -/
theorem limit_nonstationary :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 :=
  limit_not_stationary

/-- Item `C/12_D/disp/028` (`companion/chapters/12_D.tex:250-252`): $d_*=(-1,16)^T$ satisfies
\[ g_0^Td_*=-1,\quad g_1^Td_*=-1,\quad g_2^Td_*=-c+16d<-1. \] -/
theorem downhill :
    dot g0 ![-1, 16] = -1 ∧ dot g1 ![-1, 16] = -1 ∧
      dot (g2 seedC seedD) ![-1, 16] = -seedC + 16 * seedD ∧ -seedC + 16 * seedD < -1 :=
  Failure.downhill_direction

/-- Item `C/12_D/prose/033` (`companion/chapters/12_D.tex:253`): "In particular $G(td_*)=-t$ for
$t\ge0$ and $0\notin\operatorname{conv}\{g_0,g_1,g_2\}$." -/
theorem ray_hull :
    (∀ t : ℝ, 0 ≤ t → objective seedC seedD (t • ![-1, 16]) = -t) ∧
    (0 : Vec 2) ∉ convexHull ℝ (Set.range (SeedOrbit.gradient seedC seedD)) :=
  ⟨fun _ ht => objective_downhill_ray ht, DLiteralIdentities.zero_not_mem_gradient_hull⟩

/-! ### Section 12.3.1: a simple coercive global failure

$\overline G(u,v)=\max\{u,-u-v/8,cu+dv,v-17\}$ is a variable `Gbar` with its defining equation
`hGbar` ($u$ = `x 0`, $v$ = `x 1`); `gbar_eq` identifies it with the library's
`SeedOrbit.coerciveObjective`. -/

/-- Item `C/12_D/disp/029` (`companion/chapters/12_D.tex:261-263`), with line 260: "The same
trajectory is a deterministic counterexample for the finite polyhedral function
\[ \overline G(u,v)=\max\{u,-u-v/8,cu+dv,v-17\}." \]
$\overline G$ is coercive (it tends to $+\infty$ along the cocompact filter), its minimum value
$-1$ is attained at $(-1,16)$, and $0$ is not stationary ($0\notin\partial\overline G(0)$,
$\overline G(0)=0$). For every $0<c_1\le1/3$, $c_1<c_2<1$, the run produced on $\overline G$ by
the specified strict search from $z_0$ with $H_0=I$ is unique and has the iterates and matrices
of the run on $G$ (`orbitPoint`, `orbitMetric`, `cone_orbit`); it converges to the nonstationary
point $0$. -/
theorem coercive_failure (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    Tendsto Gbar (cocompact (Vec 2)) atTop ∧ Gbar ![-1, 16] = -1 ∧ (∀ x, Gbar ![-1, 16] ≤ Gbar x) ∧
    Gbar 0 = 0 ∧ (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential Gbar 0 ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
      ∃ R : AdmissibleBFGSRun 2 Gbar,
        R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = Failure.seedPoint 0 ∧ R.H 0 = 1 ∧
        R.x = orbitPoint ∧ R.H = orbitMetric ∧
        (∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric Gbar (R.x k) (R.H k) c₁ c₂ N =
          (some (R.α k), trialHistory (phase k))) ∧
        (∀ R' : AdmissibleBFGSRun 2 Gbar, R'.x 0 = Failure.seedPoint 0 → R'.H 0 = 1 →
          (∀ k, ∃ N L, DeterministicLineSearch.fromMetric Gbar (R'.x k) (R'.H k) c₁ c₂ N =
            (some (R'.α k), L)) → R'.x = R.x ∧ R'.H = R.H) ∧
        Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => Gbar (R.x k)) atTop (𝓝 (Gbar 0)) := by
  have hG := gbar_eq Gbar hGbar
  subst hG
  have hopt : coerciveOptimizer = ![-1, 16] := rfl
  rw [← hopt]
  refine ⟨?_, coercive_minimum_value, fun x => by rw [coercive_minimum_value]; exact coercive_lower_bound x,
    coercive_zero_value, coercive_limit_not_stationary, ?_⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [(coercive_sublevels_compact b).compl_mem_cocompact] with x hx
    simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
    exact hx.le
  · intro c₁ c₂ hc₁ hc₁' hc hc₂
    have hH0 : (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 :=
      (actual_coercive_deterministic_failure hc₁ hc₁' hc hc₂).2.2.2.2.1
    have hs : ∀ k, DeterministicLineSearch.fromMetric coerciveObjective
        ((coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).x k) ((coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5 =
        (some ((coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).α k), trialHistory (phase k)) :=
      fun k => coercive_orbit_search hc₁ hc₁' (hc₁.trans hc) k
    refine ⟨coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, Failure.seedPoint_zero_eq.symm, hH0, rfl, rfl,
      fun k N hN => fromMetric_fuel_mono (hs k) hN, ?_, orbitPoint_tendsto, ?_⟩
    · intro R' hx' hH' hs'
      obtain ⟨h1, h2, -, -⟩ := implemented_run_unique R' (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂)
        (hx'.trans Failure.seedPoint_zero_eq) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, hs k⟩)
      exact ⟨h1, h2⟩
    · rw [coercive_zero_value]
      exact coercive_orbit_values_tendsto

/-- Item `C/12_D/prose/034` (`companion/chapters/12_D.tex:264`): "All trial values of $G$ are
positive while $v-17<0$, by \eqref{D:trialbounds} and scaling." At every iterate of the run and at
every trial point of every search: $G>0$ and $v-17<0$ ($v$ the second coordinate). -/
theorem coercive_trials :
    ∀ k, (0 < objective seedC seedD (orbitPoint k) ∧ orbitPoint k 1 - 17 < 0) ∧
      ∀ a ∈ trialHistory (phase k),
        0 < objective seedC seedD (orbitPoint k + a • bfgsStep (orbitMetric k) (orbitGradient k) 1) ∧
        (orbitPoint k + a • bfgsStep (orbitMetric k) (orbitGradient k) 1) 1 - 17 < 0 := by
  intro k
  have hc := DEmbedding.orbit_certificate k
  refine ⟨⟨by rw [objective_of_active hc.active]; exact hc.value_pos, by linarith [hc.vertical]⟩,
    fun a ha => ?_⟩
  obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
  have ht := orbit_trial_point_certificate k q hq
  exact ⟨by rw [objective_of_active ht.active]; exact ht.value_pos, by linarith [ht.vertical]⟩

/-- Where $v-17<G$, the function $\overline G$ equals $G$. -/
theorem gbar_eq_G (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17)))
    (x : Vec 2) (hx : x 1 - 17 < objective seedC seedD x) : Gbar x = objective seedC seedD x := by
  have hG := (Failure.seed_slopes).2.2.2.2.2.2 x
  have e0 : dot g0 x = x 0 := by simp [dot, g0, Fin.sum_univ_two]
  have e1 : dot g1 x = -x 0 - x 1 / 8 := by
    simp [dot, g1, Fin.sum_univ_two]
    ring
  have e2 : dot (g2 seedC seedD) x = seedC * x 0 + seedD * x 1 := by simp [dot, g2, Fin.sum_univ_two]
  rw [e0, e1, e2] at hG
  rw [hGbar, ← max_assoc, ← hG]
  exact max_eq_left hx.le

/-- Item `C/12_D/prose/035` (`companion/chapters/12_D.tex:264`): "The fourth piece never affects
the line search." At every iterate and every trial point of the run, $\overline G=G$; and for every
$0<c_1\le1/3$, $c_2>0$ the specified strict search on $\overline G$ from $(x_k,H_k)$ returns the
same accepted length and trial list as on $G$. -/
theorem coercive_same_search (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    (∀ k, Gbar (orbitPoint k) = objective seedC seedD (orbitPoint k) ∧
      ∀ a ∈ trialHistory (phase k),
        Gbar (orbitPoint k + a • bfgsStep (orbitMetric k) (orbitGradient k) 1) =
          objective seedC seedD (orbitPoint k + a • bfgsStep (orbitMetric k) (orbitGradient k) 1)) ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → 0 < c₂ → ∀ k,
      DeterministicLineSearch.fromMetric Gbar (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k) c₁ c₂ 5 := by
  refine ⟨fun k => ⟨gbar_eq_G Gbar hGbar _ (by linarith [(coercive_trials k).1.1, (coercive_trials k).1.2]),
    fun a ha => gbar_eq_G Gbar hGbar _ (by
      linarith [((coercive_trials k).2 a ha).1, ((coercive_trials k).2 a ha).2])⟩,
    fun c₁ c₂ hc₁ hc₁' hc₂ k => ?_⟩
  have hG := gbar_eq Gbar hGbar
  subst hG
  rw [coercive_orbit_search hc₁ hc₁' hc₂ k, orbit_search hc₁ hc₁' hc₂ k]

/-- Item `C/12_D/prose/036` (`companion/chapters/12_D.tex:264`): "The convex combination of
branches $0,1,3$ with weights $(8/17,8/17,1/17)$ is identically $-1$." -/
theorem coercive_combination :
    (0 : ℝ) < 8/17 ∧ (0 : ℝ) < 1/17 ∧ (8/17 : ℝ) + 8/17 + 1/17 = 1 ∧
    ∀ x : Vec 2, 8/17 * x 0 + 8/17 * (-x 0 - x 1 / 8) + 1/17 * (x 1 - 17) = -1 :=
  ⟨by norm_num, by norm_num, by norm_num, fun x => by ring⟩

/-- Item `C/12_D/prose/037` (`companion/chapters/12_D.tex:264`): "Equality fixes the unique
minimizer $(-1,16)$, and branch $2$ is strictly below $-1$ there." $\overline G\ge-1$
everywhere, $\overline G(-1,16)=-1$, $(-1,16)$ is the only point with value $-1$, and
$c\cdot(-1)+d\cdot16<-1$. -/
theorem coercive_minimizer (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    (∀ x, -1 ≤ Gbar x) ∧ Gbar ![-1, 16] = -1 ∧ (∀ x, Gbar x = -1 → x = ![-1, 16]) ∧
    seedC * (-1) + seedD * 16 < -1 := by
  have hG := gbar_eq Gbar hGbar
  subst hG
  have hopt : coerciveOptimizer = ![-1, 16] := rfl
  rw [← hopt]
  refine ⟨coercive_lower_bound, coercive_minimum_value, fun x hx => coercive_unique_optimizer hx, ?_⟩
  linarith [downhill.2.2.2]

/-- Item `C/12_D/prose/038` (`companion/chapters/12_D.tex:264`): "Sublevels are bounded, because
$u\le t$, $v\le t+17$, and $-u-v/8\le t$ give lower bounds on both coordinates." On
$\{\overline G\le t\}$: $u\le t$, $v\le t+17$, $-u-v/8\le t$, hence $v\ge-16t$ and
$u\ge-t-(t+17)/8$; the sublevel set is bounded. -/
theorem coercive_sublevels (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) (t : ℝ) :
    (∀ x : Vec 2, Gbar x ≤ t → x 0 ≤ t ∧ x 1 ≤ t + 17 ∧ -x 0 - x 1 / 8 ≤ t ∧
      -16 * t ≤ x 1 ∧ -t - (t + 17) / 8 ≤ x 0) ∧
    Bornology.IsBounded {x : Vec 2 | Gbar x ≤ t} := by
  have hb : ∀ x : Vec 2, Gbar x ≤ t → x 0 ≤ t ∧ x 1 ≤ t + 17 ∧ -x 0 - x 1 / 8 ≤ t ∧
      -16 * t ≤ x 1 ∧ -t - (t + 17) / 8 ≤ x 0 := by
    intro x hx
    rw [hGbar] at hx
    have h0 : x 0 ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
    have h1 : -x 0 - x 1 / 8 ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
    have h3 : x 1 - 17 ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
    refine ⟨h0, by linarith, h1, by linarith, by linarith⟩
  refine ⟨hb, ?_⟩
  apply (isCompact_Icc (a := fun _ : Fin 2 => min (-t - (t + 17) / 8) (-16 * t))
    (b := fun _ : Fin 2 => t + 17)).isBounded.subset
  intro x hx
  obtain ⟨h0, h1, -, h2, h3⟩ := hb x hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact (min_le_left _ _).trans h3
    · exact (min_le_right _ _).trans h2
  · fin_cases i
    · show x 0 ≤ t + 17
      linarith
    · exact h1

/-! ### Section 12.4: two smooth convex scalar functions

$\vartheta$ = `theta` (`DScalarGeometric.theta` $=1/16$), $a_n$ = `scale n` $=\vartheta^n$,
$\varepsilon_0$ = `DScalarRamp.epsilon` $=1/128$, $b_*$ = `DEmbedding.bStar` $=2c-32d$,
$c_b$ = `DScalarRamp.center b`, $P_b$ = `DScalarRamp.ramp b`, $J_b$ = `DScalarRamp.primitive b`,
$\xi$ = `coordinate b (scale n) x`, $\varphi_b$ = `DScalar.phi b`, $\varphi_b'$ =
`deriv (DScalar.phi b)`, $\varphi_b''$ = `deriv (deriv (DScalar.phi b))`. The scalar functions are
defined only for $b\in\{2,b_*\}$ (line 284): hypothesis `hb : b = 2 ∨ b = DEmbedding.bStar`. -/

/-- Item `C/12_D/disp/032` (`companion/chapters/12_D.tex:289-297`): "Define a monotone $C^1$ ramp
$P_b$ on $[0,1]$ by
\[ P_b(\xi)=\begin{cases}0,&\xi\le c_b-\epsilon_0,\\ 3t^2-2t^3,&c_b-\epsilon_0<\xi<c_b+\epsilon_0,
\quad t=(\xi-c_b+\epsilon_0)/(2\epsilon_0),\\ 1,&\xi\ge c_b+\epsilon_0.\end{cases}" \]
The library's `DScalarRamp.ramp b` (defined on $\mathbb R$) satisfies these formulas on $[0,1]$
and is monotone and $C^1$ there. -/
theorem ramp_def {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    MonotoneOn (DScalarRamp.ramp b) (Icc 0 1) ∧ ContDiffOn ℝ 1 (DScalarRamp.ramp b) (Icc 0 1) ∧
    ∀ ξ ∈ Icc (0 : ℝ) 1,
      (ξ ≤ DScalarRamp.center b - DScalarRamp.epsilon → DScalarRamp.ramp b ξ = 0) ∧
      (DScalarRamp.center b - DScalarRamp.epsilon < ξ → ξ < DScalarRamp.center b + DScalarRamp.epsilon →
        DScalarRamp.ramp b ξ =
          3 * ((ξ - DScalarRamp.center b + DScalarRamp.epsilon) / (2 * DScalarRamp.epsilon)) ^ 2 -
            2 * ((ξ - DScalarRamp.center b + DScalarRamp.epsilon) / (2 * DScalarRamp.epsilon)) ^ 3) ∧
      (DScalarRamp.center b + DScalarRamp.epsilon ≤ ξ → DScalarRamp.ramp b ξ = 1) := by
  have _hb := hb
  refine ⟨(DScalarRamp.ramp_monotone b).monotoneOn _, (DScalarRamp.ramp_contDiff b).contDiffOn,
    fun ξ _ => ⟨DScalarRamp.ramp_eq_zero, fun h1 h2 => DScalarRamp.ramp_eq_cubic h1 h2,
      DScalarRamp.ramp_eq_one⟩⟩

/-- Item `C/12_D/prose/041` (`companion/chapters/12_D.tex:298`): "Then $0\le P_b'\le96$ and
$\int_0^1P_b(\xi)\,d\xi=1-c_b$." -/
theorem ramp_bounds {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    (∀ ξ ∈ Icc (0 : ℝ) 1, 0 ≤ deriv (DScalarRamp.ramp b) ξ ∧ deriv (DScalarRamp.ramp b) ξ ≤ 96) ∧
    ∫ ξ in (0 : ℝ)..1, DScalarRamp.ramp b ξ = 1 - DScalarRamp.center b := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  exact ⟨fun ξ _ => DScalarRamp.deriv_ramp_bounds b ξ, DScalarRamp.integral_ramp hl hr⟩

/-- Item `C/12_D/disp/033` (`companion/chapters/12_D.tex:299-305`): "Its primitive
$J_b(\xi)=\int_0^\xi P_b(t)\,dt$ is
\[ J_b(\xi)=\begin{cases}0,&\xi\le c_b-\epsilon_0,\\ 2\epsilon_0(t^3-t^4/2),&c_b-\epsilon_0<\xi<
c_b+\epsilon_0,\\ \xi-c_b,&\xi\ge c_b+\epsilon_0.\end{cases}" \]
For $\xi\in[0,1]$ ($t$ as in `ramp_def`); the library's `DScalarRamp.primitive b` is $J_b$. -/
theorem primitive_def {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    ∀ ξ ∈ Icc (0 : ℝ) 1,
      DScalarRamp.primitive b ξ = ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t ∧
      (ξ ≤ DScalarRamp.center b - DScalarRamp.epsilon → ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t = 0) ∧
      (DScalarRamp.center b - DScalarRamp.epsilon < ξ → ξ < DScalarRamp.center b + DScalarRamp.epsilon →
        ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t = 2 * DScalarRamp.epsilon *
          (((ξ - DScalarRamp.center b + DScalarRamp.epsilon) / (2 * DScalarRamp.epsilon)) ^ 3 -
            ((ξ - DScalarRamp.center b + DScalarRamp.epsilon) / (2 * DScalarRamp.epsilon)) ^ 4 / 2)) ∧
      (DScalarRamp.center b + DScalarRamp.epsilon ≤ ξ →
        ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t = ξ - DScalarRamp.center b) := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  intro ξ _
  rw [← DScalarRamp.primitive_eq_integral hl hr ξ]
  exact ⟨rfl, DScalarRamp.primitive_eq_zero, fun h1 h2 => DScalarRamp.primitive_eq_quartic h1 h2,
    DScalarRamp.primitive_eq_affine⟩

/-- Items `C/12_D/disp/034` (`companion/chapters/12_D.tex:307-309`),
`C/12_D/disp/035` (`companion/chapters/12_D.tex:311-315`, equation `D:scalar`) and
`C/12_D/disp/036` (`companion/chapters/12_D.tex:317-323`): the definition of $\varphi_b$. For
$x\in[b\vartheta a_n,ba_n]$ ($n\ge0$), $\xi=\frac{x/(ba_n)-\vartheta}{1-\vartheta}\in[0,1]$ and
\[ \varphi_b(x)=(\vartheta a_n)^3+ba_n^3(1-\vartheta)\left[\vartheta^2\xi+(1-\vartheta^2)J_b(\xi)
   \right]; \]
and $\varphi_b(x)=1-3(x+1)+3(x+1)^2$ ($x<-1$), $-x^3$ ($-1\le x\le0$), $1+x-b$ ($x\ge b$). The
library's `DScalar.phi b` satisfies these formulas, and they determine it
(`BfgsCoverage.Article.Failure.phi_unique`). -/
theorem phi_def {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    (∀ (n : ℕ) (x : ℝ), b * theta * scale n ≤ x → x ≤ b * scale n →
      coordinate b (scale n) x = (x / (b * scale n) - theta) / (1 - theta) ∧
      coordinate b (scale n) x ∈ Icc (0 : ℝ) 1 ∧
      DScalar.phi b x = (theta * scale n) ^ 3 + b * (scale n) ^ 3 * (1 - theta) *
        (theta ^ 2 * coordinate b (scale n) x +
          (1 - theta ^ 2) * DScalarRamp.primitive b (coordinate b (scale n) x))) ∧
    (∀ x : ℝ, x < -1 → DScalar.phi b x = 1 - 3 * (x + 1) + 3 * (x + 1) ^ 2) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 0 → DScalar.phi b x = -x ^ 3) ∧
    (∀ x : ℝ, b ≤ x → DScalar.phi b x = 1 + x - b) := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  obtain ⟨-, f2, f3, f4⟩ := Failure.phi_formulas hb
  refine ⟨fun n x h1 h2 => ⟨rfl, ?_, DScalar.phi_interval hl hr n h1 h2⟩, f2, f3, f4⟩
  have hb0 : 0 < b := by linarith
  have ha := scale_pos n
  have hba : 0 < b * scale n := mul_pos hb0 ha
  have hθ : 0 < 1 - theta := by norm_num [theta]
  have hx1 : theta ≤ x / (b * scale n) := by
    rw [le_div_iff₀ hba]
    linarith
  have hx2 : x / (b * scale n) ≤ 1 := by
    rw [div_le_one hba]
    exact h2
  constructor
  · exact div_nonneg (by linarith) hθ.le
  · show (x / (b * scale n) - theta) / (1 - theta) ≤ 1
    rw [div_le_one hθ]
    linarith

/-- The formula `D:scalar` of the $n$th positive interval as a function of $x$,
$(\vartheta a_n)^3+ba_n^3(1-\vartheta)[\vartheta^2\xi+(1-\vartheta^2)J_b(\xi)]$ with
$\xi=\frac{x/(ba_n)-\vartheta}{1-\vartheta}$. -/
def intervalFormula (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (theta * scale n) ^ 3 + b * (scale n) ^ 3 * (1 - theta) *
    (theta ^ 2 * ((x / (b * scale n) - theta) / (1 - theta)) +
      (1 - theta ^ 2) * DScalarRamp.primitive b ((x / (b * scale n) - theta) / (1 - theta)))

/-- Item `C/12_D/prose/042` (`companion/chapters/12_D.tex:324`): "These intervals cover the real
line, with agreeing formulas at shared endpoints." The intervals $x<-1$, $[-1,0]$,
$[b\vartheta a_n,ba_n]$ ($n\ge0$) and $x\ge b$ cover $\mathbb R$; the shared endpoints are $-1$,
$ba_{n+1}=b\vartheta a_n$ and $b=ba_0$, and the adjoining formulas agree there. -/
theorem intervals_cover {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    (∀ x : ℝ, x < -1 ∨ (-1 ≤ x ∧ x ≤ 0) ∨ (∃ n : ℕ, b * theta * scale n ≤ x ∧ x ≤ b * scale n) ∨
      b ≤ x) ∧
    (1 - 3 * ((-1 : ℝ) + 1) + 3 * ((-1 : ℝ) + 1) ^ 2 = -(-1 : ℝ) ^ 3) ∧
    (∀ n : ℕ, b * scale (n + 1) = b * theta * scale n ∧
      intervalFormula b (n + 1) (b * scale (n + 1)) = intervalFormula b n (b * theta * scale n)) ∧
    intervalFormula b 0 (b * scale 0) = 1 + b - b := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  have hb0 : 0 < b := by linarith
  have hf : ∀ (n : ℕ) (x : ℝ), b * theta * scale n ≤ x → x ≤ b * scale n →
      intervalFormula b n x = DScalar.phi b x := fun n x h1 h2 =>
    (DScalar.phi_interval hl hr n h1 h2).symm
  have hθ : theta ≤ 1 := by norm_num [theta]
  refine ⟨fun x => ?_, by norm_num, fun n => ?_, ?_⟩
  · rcases lt_or_le x (-1) with h | h
    · exact Or.inl h
    rcases le_or_lt x 0 with h0 | h0
    · exact Or.inr (Or.inl ⟨h, h0⟩)
    rcases le_or_lt b x with hx | hx
    · exact Or.inr (Or.inr (Or.inr hx))
    obtain ⟨n, h1, h2⟩ := positive_interval_cover hb0 h0 hx.le
    exact Or.inr (Or.inr (Or.inl ⟨n, h1.le, h2⟩))
  · have hs : b * scale (n + 1) = b * theta * scale n := by
      rw [scale_succ]
      ring
    have ha := scale_pos n
    refine ⟨hs, ?_⟩
    rw [hf (n + 1) _ (by
        have := mul_le_mul_of_nonneg_left hθ (mul_pos hb0 (scale_pos (n + 1))).le
        nlinarith) le_rfl,
      hf n _ le_rfl (by
        have := mul_le_mul_of_nonneg_right hθ (mul_pos hb0 ha).le
        nlinarith), hs]
  · rw [hf 0 _ (by
        have := mul_le_mul_of_nonneg_right hθ (mul_pos hb0 (scale_pos 0)).le
        nlinarith) le_rfl]
    rw [scale_zero, mul_one]
    exact DScalar.phi_eq_outer hl hr le_rfl

/-- Item `C/12_D/lemma/D:scalarlemma` (`companion/chapters/12_D.tex:326-334`), Lemma
`D:scalarlemma`, including its display Item `C/12_D/disp/037` (`companion/chapters/12_D.tex:328-333`)
(equations `D:jets`, `D:curvature`, `D:affineplateau`).

"Each $\varphi_b$ is globally convex, $C^2$, nonnegative, coercive, and uniquely minimized at
$0$. Moreover,
\[ \varphi_b(ba_n)=a_n^3,\quad \varphi_b'(ba_n)=a_n^2,\quad\varphi_b''(ba_n)=0, \]
\[ 0\le\varphi_b''(x)\le\max\{6,102/b\}\quad(x\in\mathbb R), \]
\[ \varphi_b(ba_n+h)=a_n^3+a_n^2h\quad\text{for }|h|\le a_n/2." \]
For $b\in\{2,b_*\}$ and $n\ge0$. Coercive: $\varphi_b\to\infty$ along the cocompact filter of
$\mathbb R$. -/
theorem scalar_lemma {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    ConvexOn ℝ univ (DScalar.phi b) ∧ ContDiff ℝ 2 (DScalar.phi b) ∧ (∀ x, 0 ≤ DScalar.phi b x) ∧
    Tendsto (DScalar.phi b) (cocompact ℝ) atTop ∧
    (∀ x, DScalar.phi b 0 ≤ DScalar.phi b x) ∧ (∀ x, DScalar.phi b x = DScalar.phi b 0 → x = 0) ∧
    (∀ n : ℕ, DScalar.phi b (b * scale n) = (scale n) ^ 3 ∧
      deriv (DScalar.phi b) (b * scale n) = (scale n) ^ 2 ∧
      deriv (deriv (DScalar.phi b)) (b * scale n) = 0) ∧
    (∀ x, 0 ≤ deriv (deriv (DScalar.phi b)) x ∧ deriv (deriv (DScalar.phi b)) x ≤ max 6 (102 / b)) ∧
    ∀ (n : ℕ) (h : ℝ), |h| ≤ scale n / 2 →
      DScalar.phi b (b * scale n + h) = (scale n) ^ 3 + (scale n) ^ 2 * h := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  obtain ⟨hmin, huniq⟩ := DScalar.phi_unique_minimizer hl hr
  exact ⟨DScalar.phi_convex hl hr, DScalar.phi_contDiff hl hr, DScalar.phi_nonnegative hl hr,
    DScalar.phi_coercive hl hr, hmin, huniq,
    fun n => ⟨DScalar.phi_node hl hr n, (DScalar.phi_node_hasDerivAt hl hr n).deriv,
      (DScalar.phi_node_second_hasDerivAt hl hr n).deriv⟩,
    DScalar.phi_second_derivative_bounds hl hr, fun n h hh => DScalar.phi_plateau hl hr n hh⟩

/-- Item `C/12_D/disp/039` (`companion/chapters/12_D.tex:343-346`), in the proof of Lemma
`D:scalarlemma`: \[ \vartheta^2+(1-\vartheta^2)(1-c_b)=\frac{1+\vartheta+\vartheta^2}{b}. \] -/
theorem matching_identity {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    theta ^ 2 + (1 - theta ^ 2) * (1 - DScalarRamp.center b) = (1 + theta + theta ^ 2) / b := by
  obtain ⟨hl, _⟩ := Failure.scalar_parameter_bounds hb
  exact DScalarRamp.matching_identity (by linarith)

/-- Item `C/12_D/disp/040` (`companion/chapters/12_D.tex:350-353`), in the proof of Lemma
`D:scalarlemma`: as $x\downarrow0$,
\[ \varphi_b(x)=O(x^3),\qquad\varphi_b'(x)=O(x^2),\qquad\varphi_b''(x)=O(x) \]
(big-O along $x\to0^+$, the filter `𝓝[>] 0`). -/
theorem asymptotic_orders {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    DScalar.phi b =O[𝓝[>] 0] (fun x : ℝ => x ^ 3) ∧
    deriv (DScalar.phi b) =O[𝓝[>] 0] (fun x : ℝ => x ^ 2) ∧
    deriv (deriv (DScalar.phi b)) =O[𝓝[>] 0] (fun x : ℝ => x) := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  rw [DScalar.deriv_phi hl hr, DScalar.deriv_phiFirst hl]
  exact DScalar.positive_asymptotic_orders hl hr

/-- Item `C/12_D/disp/042` (`companion/chapters/12_D.tex:362-368`), in the proof of Lemma
`D:scalarlemma`: "Exact rational interval bounds give" the table of $c_b$,
$\ell_b=b(1-\vartheta)(1-c_b-\epsilon_0)$ and $u_b=b(1-\vartheta)(c_b-\epsilon_0)/\vartheta$ for
$b=2$ and $b=b_*$ (`DScalarRamp.lowerLength`, `DScalarRamp.upperLength`, first conjunct). Each
printed decimal is the nearest rounding of the value (error below $10^{-12}/2$). -/
theorem scalar_table :
    (∀ b : ℝ, DScalarRamp.lowerLength b =
        b * (1 - DScalarRamp.theta) * (1 - DScalarRamp.center b - DScalarRamp.epsilon) ∧
      DScalarRamp.upperLength b =
        b * (1 - DScalarRamp.theta) * (DScalarRamp.center b - DScalarRamp.epsilon) / DScalarRamp.theta) ∧
    |DScalarRamp.center 2 - 0.468627450980| < 1 / 10 ^ 12 / 2 ∧
    |DScalarRamp.lowerLength 2 - 0.981675091912| < 1 / 10 ^ 12 / 2 ∧
    |DScalarRamp.upperLength 2 - 13.824448529412| < 1 / 10 ^ 12 / 2 ∧
    |DScalarRamp.center DEmbedding.bStar - 0.971910573260| < 1 / 10 ^ 12 / 2 ∧
    |DScalarRamp.lowerLength DEmbedding.bStar - 0.635765118557| < 1 / 10 ^ 12 / 2 ∧
    |DScalarRamp.upperLength DEmbedding.bStar - 483.655089309488| < 1 / 10 ^ 12 / 2 :=
  ⟨fun _ => ⟨rfl, rfl⟩,
    display_round 27 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 27 (by decide)),
    display_round 28 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 28 (by decide)),
    display_round 29 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 29 (by decide)),
    display_round 30 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 30 (by decide)),
    display_round 31 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 31 (by decide)),
    display_round 32 rfl (by simp only [DDisplayPrecision.corrected, Matrix.cons_val]; norm_num)
      (unit_twelve 32 (by decide))⟩

/-- On the open interval $(b\vartheta a_n,ba_n)$, $\varphi_b''$ is the $n$th curvature component. -/
theorem second_eq_component {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (n : ℕ) (x : ℝ)
    (h1 : b * theta * scale n < x) (h2 : x < b * scale n) :
    deriv (deriv (DScalar.phi b)) =ᶠ[𝓝 x] DScalar.curvatureComponent b n := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  rw [DScalar.deriv_phi hl hr, DScalar.deriv_phiFirst hl]
  filter_upwards [Ioo_mem_nhds h1 h2] with y hy
  have hθ : 0 ≤ b * theta * scale n := by
    have := scale_pos n
    have : (0 : ℝ) < theta := theta_pos
    positivity
  rw [DScalar.phiSecond, DScalarNegative.second_eq_zero (by linarith [hy.1]), add_zero,
    DScalar.positiveCurvature_interval hl hr n hy.1.le hy.2.le]

/-- Item `C/12_D/disp/043` (`companion/chapters/12_D.tex:374-379`): "Within a ramp,
\[ |\varphi_b'''(x)|\le\frac{1+\vartheta}{b^2(1-\vartheta)}\frac{3}{2\epsilon_0^2}
   =\frac{139264}{5b^2}." \]
"Within a ramp": $x$ in the $n$th positive interval with $c_b-\epsilon_0<\xi<c_b+\epsilon_0$; there
$\varphi_b''$ is differentiable with derivative $\varphi_b'''(x)=v$, and $|v|$ obeys the bound; the
constant equals $139264/(5b^2)$. -/
theorem third_derivative_bound {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (n : ℕ) (x : ℝ)
    (hl' : DScalarRamp.center b - DScalarRamp.epsilon < coordinate b (scale n) x)
    (hr' : coordinate b (scale n) x < DScalarRamp.center b + DScalarRamp.epsilon) :
    ∃ v : ℝ, HasDerivAt (deriv (deriv (DScalar.phi b))) v x ∧
      |v| ≤ (1 + theta) / (b ^ 2 * (1 - theta)) * (3 / (2 * DScalarRamp.epsilon ^ 2)) ∧
      (1 + theta) / (b ^ 2 * (1 - theta)) * (3 / (2 * DScalarRamp.epsilon ^ 2)) = 139264 / (5 * b ^ 2) := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  have hb0 : 0 < b := by linarith
  have ha := scale_pos n
  have hba : 0 < b * scale n := mul_pos hb0 ha
  have hθ : (0 : ℝ) < 1 - theta := by norm_num [theta]
  obtain ⟨hin0, -, hin1⟩ := DScalarRamp.transition_inside hl hr
  have hc0 : 0 < coordinate b (scale n) x := lt_trans hin0 hl'
  have hc1 : coordinate b (scale n) x < 1 := lt_trans hr' hin1
  have hx1 : b * theta * scale n < x := by
    have h := hc0
    unfold coordinate at h
    have h' : theta < x / (b * scale n) := by
      have := (div_pos_iff_of_pos_right hθ).mp h
      linarith
    rw [lt_div_iff₀ hba] at h'
    linarith
  have hx2 : x < b * scale n := by
    have h := hc1
    unfold coordinate at h
    rw [div_lt_one hθ] at h
    have h' : x / (b * scale n) < 1 := by linarith
    rwa [div_lt_one hba] at h'
  have hder := DScalarRamp.intervalCurvature_hasDerivAt_inside hb0 ha hl' hr'
  have hbound := DScalarRamp.intervalCurvature_derivative_inside_bound hb0 ha hl' hr'
  have hconst : (1 + theta) / (b ^ 2 * (1 - theta)) * (3 / (2 * DScalarRamp.epsilon ^ 2)) =
      139264 / (5 * b ^ 2) := by
    norm_num [theta, DScalarRamp.epsilon]
    field_simp
    ring
  refine ⟨_, ?_, hconst ▸ hbound, hconst⟩
  exact hder.congr_of_eventuallyEq (second_eq_component hb n x hx1 hx2)

/-- Items `C/12_D/prose/043` (`companion/chapters/12_D.tex:373`), `C/12_D/prose/044`
(`companion/chapters/12_D.tex:380`) and `C/12_D/prose/045` (`companion/chapters/12_D.tex:380`):
"The construction even gives globally Lipschitz second derivatives." / "The second derivative is
continuous across every join and at the accumulation point $0$." / "The uniform bound above,
together with the bound $6$ on the negative cubic part, proves global Lipschitz continuity of
$\varphi_b''$ by summing over interval lengths."

$\varphi_b''$ is continuous (on $\mathbb R$, in particular at every join and at $0$); on the
negative cubic part $-1<x<0$ its derivative is $-6$, of absolute value $6$; and it is globally
Lipschitz with constant $\max\{6,139264/(5b^2)\}$. -/
theorem second_derivative_regularity {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    Continuous (deriv (deriv (DScalar.phi b))) ∧
    (∀ x : ℝ, -1 < x → x < 0 → HasDerivAt (deriv (deriv (DScalar.phi b))) (-6) x) ∧
    ∀ x y : ℝ, |deriv (deriv (DScalar.phi b)) x - deriv (deriv (DScalar.phi b)) y| ≤
      max 6 (139264 / (5 * b ^ 2)) * |x - y| := by
  obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
  have hlip := DScalar.phi_second_derivative_lipschitz hl hr
  refine ⟨hlip.continuous, fun x h1 h2 => ?_, fun x y => ?_⟩
  · have heq : deriv (deriv (DScalar.phi b)) =ᶠ[𝓝 x] fun y => -6 * y := by
      rw [DScalar.deriv_phi hl hr, DScalar.deriv_phiFirst hl]
      filter_upwards [Ioo_mem_nhds h1 h2] with y hy
      rw [DScalar.phiSecond, DScalar.positiveCurvature_nonpos hl hr hy.2.le, zero_add,
        DScalarNegative.second_eq_clip]
      have hc : DScalarRamp.clip (-y) = -y := by
        unfold DScalarRamp.clip
        rw [min_eq_right (by linarith [hy.1]), max_eq_right (by linarith [hy.2])]
      rw [hc]
      ring
    have hd : HasDerivAt (fun y : ℝ => -6 * y) (-6) x := by
      simpa using (hasDerivAt_id x).const_mul (-6)
    exact hd.congr_of_eventuallyEq heq
  · have h := hlip.dist_le_mul x y
    simpa only [Real.dist_eq, NNReal.coe_mk] using h

/-- Item `C/12_D/prose/046` (`companion/chapters/12_D.tex:380`): "Thus the branches below are in
$C^{2,1}$ as well." The four branches $f_i$ of `D:fullobjective` are $C^2$ with globally Lipschitz
Hessians (Euclidean operator norm against Euclidean distance). -/
theorem branches_C21 :
    ∀ i : Fin 4, ContDiff ℝ 2 (DEmbedding.branch i) ∧ ∃ L : ℝ, ∀ x y : Vec 2,
      FrameNorms.euclideanOpNorm
        (RadialHessian.matrix (DEmbedding.branch i) x - RadialHessian.matrix (DEmbedding.branch i) y) ≤
        L * ‖euclideanVector (x - y)‖ :=
  fun i => ⟨DEmbedding.branch_contDiff i, 60000, DEmbedding.branch_hessian_lipschitz i⟩

/-- A ridge $f(x)=\varphi(g^Tx)$ that is analytic everywhere has an everywhere analytic profile
$\varphi$ (compose with $t\mapsto tw$, $g^Tw=1$). -/
theorem analytic_of_ridge {φ : ℝ → ℝ} {f : Vec 2 → ℝ} {g w : Vec 2} (hf : ∀ x, f x = φ (dot g x))
    (hw : dot g w = 1) (h : ∀ x, AnalyticAt ℝ f x) : ∀ t, AnalyticAt ℝ φ t := by
  intro t
  have he : AnalyticAt ℝ (fun s : ℝ => s • w) t :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) w).analyticAt t
  have hc : AnalyticAt ℝ (f ∘ fun s : ℝ => s • w) t := AnalyticAt.comp (h _) he
  have hfun : (f ∘ fun s : ℝ => s • w) = φ := by
    funext s
    simp only [Function.comp_apply, hf, dot_smul_right, hw, mul_one]
  rwa [hfun] at hc

/-- A function on $\mathbb R^n$ that is constant along a nonzero direction $w$ through $0$ is not
$\mu$-strongly convex for any $\mu>0$: neither $f-\frac\mu2\|\cdot\|_2^2$ is convex
(`FixedNormal.EuclideanStrongConvexOn`) nor $f$ is $\mu$-strongly convex for the sup norm of
`Vec n` (Mathlib's `StrongConvexOn`). Compare the midpoint $0$ of $\pm w$. -/
theorem not_strongly_convex_of_flat {n : ℕ} {f : Vec n → ℝ} {w : Vec n} (hw : w ≠ 0)
    (hflat : ∀ t : ℝ, f (t • w) = f 0) {μ : ℝ} (hμ : 0 < μ) :
    ¬ FixedNormal.EuclideanStrongConvexOn univ μ f ∧ ¬ StrongConvexOn univ μ f := by
  have hm : f ((-1 : ℝ) • w) = f 0 := hflat (-1)
  have hp : f ((1 : ℝ) • w) = f 0 := hflat 1
  rw [neg_one_smul] at hm
  rw [one_smul] at hp
  have hmid : (1 / 2 : ℝ) • -w + (1 / 2 : ℝ) • w = 0 := by
    rw [smul_neg, neg_add_cancel]
  constructor
  · intro h
    have hs : 0 < sqNorm w := by
      rcases Function.ne_iff.mp hw with ⟨i, hi⟩
      have hi2 : 0 < (w i) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
      exact lt_of_lt_of_le hi2
        (Finset.single_le_sum (f := fun j => (w j) ^ 2) (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i))
    have h1 := h.2 (mem_univ (-w)) (mem_univ w) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hn : sqNorm (-w) = sqNorm w := by simp [sqNorm]
    have h0 : sqNorm (0 : Vec n) = 0 := by simp [sqNorm]
    simp only [hmid, hm, hp, hn, h0, smul_eq_mul] at h1
    nlinarith
  · intro h
    have hs : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have h1 := h.2 (mem_univ (-w)) (mem_univ w) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h2 : ‖-w - w‖ = 2 * ‖w‖ := by
      rw [show -w - w = (-2 : ℝ) • w by module, norm_smul]
      norm_num
    simp only [hmid, hm, hp, h2, smul_eq_mul] at h1
    nlinarith [mul_pos hμ (mul_pos hs hs)]

/-- Each branch of `D:fullobjective` is constant along a nonzero direction: $f_0(u,v)=\varphi_2(u)$
along $(0,1)$, $f_1(u,v)=\varphi_2(-u-v/8)$ along $(1,-8)$, $f_2(u,v)=\varphi_{b_*}(cu+dv)$ along
$(d,-c)$ ($c\ne0$) and $f_3(u,v)=v$ along $(1,0)$. -/
theorem branch_flat (i : Fin 4) : ∃ w : Vec 2, w ≠ 0 ∧ ∀ t : ℝ,
    DEmbedding.branch i (t • w) = DEmbedding.branch i 0 := by
  have hc : seedC ≠ 0 := by
    have := (AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1).1
    change (318 / 1000 : ℝ) < seedC at this
    intro h
    rw [h] at this
    norm_num at this
  have h0 : ∀ t : ℝ, DEmbedding.branch 0 (t • ![0, 1]) = DEmbedding.branch 0 0 := by
    intro t
    rw [(Failure.upper_objective _).2.2.1, (Failure.upper_objective _).2.2.1]
    simp
  have h1 : ∀ t : ℝ, DEmbedding.branch 1 (t • ![1, -8]) = DEmbedding.branch 1 0 := by
    intro t
    rw [(Failure.upper_objective _).2.2.2.1, (Failure.upper_objective _).2.2.2.1]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.zero_apply]
    ring
  have h2 : ∀ t : ℝ, DEmbedding.branch 2 (t • ![seedD, -seedC]) = DEmbedding.branch 2 0 := by
    intro t
    rw [(Failure.upper_objective _).2.2.2.2.1, (Failure.upper_objective _).2.2.2.2.1]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.zero_apply]
    ring
  have h3 : ∀ t : ℝ, DEmbedding.branch 3 (t • ![1, 0]) = DEmbedding.branch 3 0 := by
    intro t
    rw [(Failure.upper_objective _).2.2.2.2.2, (Failure.upper_objective _).2.2.2.2.2]
    simp
  fin_cases i
  · exact ⟨![0, 1], fun h => by simpa using congrFun h 1, h0⟩
  · exact ⟨![1, -8], fun h => by simpa using congrFun h 0, h1⟩
  · exact ⟨![seedD, -seedC], fun h => hc (by simpa using congrFun h 1), h2⟩
  · exact ⟨![1, 0], fun h => by simpa using congrFun h 0, h3⟩

/-- Item `C/12_D/prose/047` (`companion/chapters/12_D.tex:380`), corrected on 15 October 2026
(M14): "This does not make the first three branches analytic, nor any branch uniformly strongly
convex." The former wording, "This does not make them analytic or uniformly strongly convex",
spoke of "the branches below", the four branches $f_0,\dots,f_3$ of `D:fullobjective`; the fourth,
$f_3(u,v)=v$, is analytic (`branch3_analytic`). Proved here: for
$b\in\{2,b_*\}$, $\varphi_b$ is not analytic on $\mathbb R$ and $\varphi_b''$ has no positive
lower bound; $f_0,f_1,f_2$ (built from $\varphi_2,\varphi_2,\varphi_{b_*}$) are not analytic on
$\mathbb R^2$; and no branch $f_i$, $i=0,\dots,3$, is uniformly strongly convex: for every
$\mu>0$, $\nabla^2f_i\succeq\mu I$ fails at some point, $f_i-\frac\mu2\|\cdot\|_2^2$ is not convex
(`FixedNormal.EuclideanStrongConvexOn`), and $f_i$ is not $\mu$-strongly convex for the sup norm
of `Vec 2` (`StrongConvexOn`). -/
theorem not_analytic :
    (∀ b : ℝ, (b = 2 ∨ b = DEmbedding.bStar) →
      (¬ ∀ x : ℝ, AnalyticAt ℝ (DScalar.phi b) x) ∧
      ¬ ∃ μ : ℝ, 0 < μ ∧ ∀ x : ℝ, μ ≤ deriv (deriv (DScalar.phi b)) x) ∧
    (∀ i : Fin 3, ¬ ∀ x : Vec 2, AnalyticAt ℝ (DEmbedding.branch i.castSucc) x) ∧
    (∀ i : Fin 4, ¬ ∃ μ : ℝ, 0 < μ ∧ ∀ x : Vec 2,
      (RadialHessian.matrix (DEmbedding.branch i) x - μ • (1 : Mat 2)).PosSemidef) ∧
    ∀ (i : Fin 4) (μ : ℝ), 0 < μ →
      ¬ FixedNormal.EuclideanStrongConvexOn univ μ (DEmbedding.branch i) ∧
      ¬ StrongConvexOn univ μ (DEmbedding.branch i) := by
  have hphi : ∀ b : ℝ, (b = 2 ∨ b = DEmbedding.bStar) → ¬ ∀ x : ℝ, AnalyticAt ℝ (DScalar.phi b) x := by
    intro b hb h
    obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
    have hψ : AnalyticOnNhd ℝ (fun x : ℝ => DScalar.phi b x + x ^ 3) univ :=
      fun x _ => (h x).add (analyticAt_id.pow 3)
    have hzero : (fun x : ℝ => DScalar.phi b x + x ^ 3) =ᶠ[𝓝 (-1/2 : ℝ)] 0 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < -1/2) (by norm_num : (-1/2 : ℝ) < 0)]
        with y hy
      rw [DScalar.phi_eq_negative_cubic hl hr hy.1.le hy.2.le]
      simp
    have hall := hψ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ _) hzero (mem_univ b)
    simp only [Pi.zero_apply] at hall
    rw [DScalar.phi_eq_outer hl hr le_rfl] at hall
    nlinarith [pow_pos (by linarith : (0 : ℝ) < b) 3]
  refine ⟨fun b hb => ⟨hphi b hb, fun ⟨μ, hμ, hμx⟩ => ?_⟩, fun i h => ?_,
    Failure.no_uniform_lower_curvature.2.2, fun i μ hμ => ?_⟩
  · obtain ⟨hl, hr⟩ := Failure.scalar_parameter_bounds hb
    have h0 := hμx 0
    rw [DScalar.deriv_phi hl hr, DScalar.deriv_phiFirst hl, DScalar.phiSecond,
      DScalar.positiveCurvature_nonpos hl hr le_rfl, DScalarNegative.second_eq_zero le_rfl] at h0
    linarith
  · have hp := DEmbedding.parameter_bounds i
    have hpar : DEmbedding.parameter i = 2 ∨ DEmbedding.parameter i = DEmbedding.bStar := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    obtain ⟨w, hw⟩ : ∃ w : Vec 2, dot (SeedOrbit.gradient seedC seedD i) w = 1 := by
      have hc : 0 < seedC := by
        have := (AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1).1
        change (318 / 1000 : ℝ) < seedC at this
        linarith
      fin_cases i
      · exact ⟨![1, 0], by simp [SeedOrbit.gradient, g0, dot, Fin.sum_univ_two]⟩
      · exact ⟨![-1, 0], by simp [SeedOrbit.gradient, g1, dot, Fin.sum_univ_two]⟩
      · exact ⟨![1 / seedC, 0], by
          simp [SeedOrbit.gradient, g2, dot, Fin.sum_univ_two]
          field_simp⟩
    exact hphi _ hpar (analytic_of_ridge (fun x => DEmbedding.branch_old i x) hw h)
  · obtain ⟨w, hw, hflat⟩ := branch_flat i
    exact not_strongly_convex_of_flat hw hflat hμ

/-- Counterexample to the literal reading of Item `C/12_D/prose/047`
(`companion/chapters/12_D.tex:380`) as printed before its correction of 15 October 2026 (M14):
"This does not make them analytic", "them" being the branches of `D:fullobjective`. The fourth
branch $f_3(u,v)=v$ is linear, hence analytic at every point (the corrected statement is
`not_analytic`). -/
theorem branch3_analytic : ∀ x : Vec 2, AnalyticAt ℝ (DEmbedding.branch 3) x := by
  intro x
  have h : DEmbedding.branch 3 = fun y : Vec 2 => y 1 := by
    funext y
    exact (Failure.upper_objective y).2.2.2.2.2
  rw [h]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).analyticAt x

/-! ### Section 12.5: the single objective with bad starts arbitrarily near its minimizer

$F$ = `DEmbedding.objective`, the maximum of the branches `DEmbedding.branch i`
(display `D:fullobjective`, `BfgsCoverage.Article.Failure.upper_objective`): $f_i(x)=\varphi_{b_i}(g_i^Tx)$
for $i\le2$ with $(b_0,b_1,b_2)=(2,2,b_*)$ (`DEmbedding.parameter`, `DEmbedding.branch_old`),
$f_3(u,v)=v$. Hessians are `RadialHessian.matrix`, operator norms Euclidean
(`FrameNorms.euclideanOpNorm`). $p_n$ = `DEmbedding.center n`. -/

/-- Item `C/12_D/prose/048` (`companion/chapters/12_D.tex:404`): "Each branch is convex and $C^2$.
For $i\le2$, its Hessian is the scalar second derivative times $g_ig_i^T$":
$\nabla^2f_i(x)=\varphi_{b_i}''(g_i^Tx)\,g_ig_i^T$. -/
theorem branch_hessians :
    (∀ i : Fin 4, ConvexOn ℝ univ (DEmbedding.branch i) ∧ ContDiff ℝ 2 (DEmbedding.branch i)) ∧
    (∀ (i : Fin 3) (x : Vec 2), DEmbedding.branch i.castSucc x =
      DScalar.phi (DEmbedding.parameter i) (dot (SeedOrbit.gradient seedC seedD i) x)) ∧
    DEmbedding.parameter = ![2, 2, DEmbedding.bStar] ∧
    ∀ (i : Fin 3) (x : Vec 2), RadialHessian.matrix (DEmbedding.branch i.castSucc) x =
      deriv (deriv (DScalar.phi (DEmbedding.parameter i))) (dot (SeedOrbit.gradient seedC seedD i) x) •
        outer (SeedOrbit.gradient seedC seedD i) (SeedOrbit.gradient seedC seedD i) := by
  refine ⟨fun i => ⟨DEmbedding.branch_convex i, DEmbedding.branch_contDiff i⟩, DEmbedding.branch_old,
    rfl, fun i x => ?_⟩
  obtain ⟨hl, hr⟩ := DEmbedding.parameter_bounds i
  rw [DEmbedding.branch_old_hessian, DScalar.deriv_phi hl hr, DScalar.deriv_phiFirst hl]

/-- Item `C/12_D/disp/045` (`companion/chapters/12_D.tex:405-408`):
\[ \|\nabla^2f_0\|\le51,\qquad\|\nabla^2f_1\|\le51\frac{65}{64}<52, \]
at every point (Euclidean operator norm). -/
theorem hessian_bounds_01 (x : Vec 2) :
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch 0) x) ≤ 51 ∧
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch 1) x) ≤ 51 * (65 / 64) ∧
    (51 : ℝ) * (65 / 64) < 52 := by
  obtain ⟨h0, h1, -, -, -⟩ := DEmbedding.branch_individual_hessian_bounds x
  exact ⟨h0, h1, by norm_num⟩

/-- Item `C/12_D/prose/049` (`companion/chapters/12_D.tex:409`): "while $b_*>33$ gives
$\varphi_{b_*}''\le6$ and $c^2+d^2<2$". -/
theorem bstar_curvature :
    33 < DEmbedding.bStar ∧ (∀ t : ℝ, deriv (deriv (DScalar.phi DEmbedding.bStar)) t ≤ 6) ∧
    seedC ^ 2 + seedD ^ 2 < 2 := by
  have hb := DEmbedding.bStar_bounds
  have h6 : max 6 (102 / DEmbedding.bStar) = 6 := by
    apply max_eq_left
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨hb.1, fun t => ?_, ?_⟩
  · have h := (DScalar.phi_second_derivative_bounds (by linarith) hb.2.le t).2
    rwa [h6] at h
  · have h := DEmbedding.gradient_sqNorm_lt_two 2
    simpa [sqNorm, SeedOrbit.gradient, g2, Fin.sum_univ_two] using h

/-- Item `C/12_D/disp/046` (`companion/chapters/12_D.tex:410-412`):
\[ \|\nabla^2f_2\|<12,\qquad\nabla^2f_3=0, \]
at every point (Euclidean operator norm). -/
theorem hessian_bounds_23 (x : Vec 2) :
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch 2) x) < 12 ∧
    RadialHessian.matrix (DEmbedding.branch 3) x = 0 := by
  obtain ⟨-, -, -, h2, h3⟩ := DEmbedding.branch_individual_hessian_bounds x
  exact ⟨h2, h3⟩

/-- Item `C/12_D/prose/050` (`companion/chapters/12_D.tex:413`): "A common global upper bound $64I$
therefore holds. The preceding derivative estimate and $\|g_i\|<2$ also give a common finite
Lipschitz bound for the branch Hessians (for example $60000$ suffices)." ($\|g_i\|$ Euclidean;
the Lipschitz bound is for the Euclidean operator norm against the Euclidean distance.) -/
theorem common_bounds :
    (∀ (i : Fin 4) (x : Vec 2),
      ((64 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (DEmbedding.branch i) x).PosSemidef) ∧
    (∀ i : Fin 3, ‖euclideanVector (SeedOrbit.gradient seedC seedD i)‖ < 2) ∧
    ∀ (i : Fin 4) (x y : Vec 2), FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (DEmbedding.branch i) x - RadialHessian.matrix (DEmbedding.branch i) y) ≤
        60000 * ‖euclideanVector (x - y)‖ := by
  refine ⟨fun i x => (DEmbedding.branch_hessian_bounds i x).2, fun i => ?_,
    DEmbedding.branch_hessian_lipschitz⟩
  have h := DEmbedding.gradient_sqNorm_lt_two i
  have hsq : ‖euclideanVector (SeedOrbit.gradient seedC seedD i)‖ ^ 2 =
      sqNorm (SeedOrbit.gradient seedC seedD i) := by
    rw [FrameNorms.euclidean_norm_sq]
    rfl
  have hn := norm_nonneg (euclideanVector (SeedOrbit.gradient seedC seedD i))
  nlinarith

/-- Items `C/12_D/prose/051` (`companion/chapters/12_D.tex:415`), `C/12_D/prose/052`
(`companion/chapters/12_D.tex:417`), `C/12_D/disp/047` (`companion/chapters/12_D.tex:418-420`) and
`C/12_D/prose/053` (`companion/chapters/12_D.tex:421`).

"The first three branches are nonnegative and vanish at zero. If $F(x)=0$, its first two scalar
arguments must vanish; $g_0$ and $g_1$ are independent, so $x=0$. The same two scalar arguments
lie in bounded scalar sublevels whenever $F(x)$ is bounded above, proving compactness of every
sublevel of $F$." / "At zero, the first three branches have zero gradient. Therefore
\[ F'(0;h)=\max\{0,h_2\}, \]
which proves that the unique minimizer is nonsmooth."

The bounded scalar sublevel: $F(x)\le a$ puts $g_0^Tx$ and $g_1^Tx$ in
$[\min\{-1,-a\},\max\{2,a+2\}]$. $F'(0;h)$ is the right derivative of $t\mapsto F(th)$ at $0$;
$h_2$ = `h 1`. -/
theorem objective_minimizer :
    (∀ (i : Fin 3) (x : Vec 2), 0 ≤ DEmbedding.branch i.castSucc x) ∧
    (∀ i : Fin 3, DEmbedding.branch i.castSucc 0 = 0) ∧
    (∀ x : Vec 2, DEmbedding.objective x = 0 → dot g0 x = 0 ∧ dot g1 x = 0) ∧
    LinearIndependent ℝ ![g0, g1] ∧
    (∀ x : Vec 2, DEmbedding.objective x = 0 → x = 0) ∧
    (∀ (a : ℝ) (x : Vec 2), DEmbedding.objective x ≤ a →
      min (-1) (-a) ≤ dot g0 x ∧ dot g0 x ≤ max 2 (a + 2) ∧
      min (-1) (-a) ≤ dot g1 x ∧ dot g1 x ≤ max 2 (a + 2)) ∧
    (∀ a : ℝ, IsCompact {x | DEmbedding.objective x ≤ a}) ∧
    (∀ i : Fin 3, HasFDerivAt (DEmbedding.branch i.castSucc) (gradientFunctional 0) 0) ∧
    (∀ h : Vec 2, Tendsto (fun t : ℝ => (DEmbedding.objective (t • h) - DEmbedding.objective 0) / t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1)))) ∧
    (∀ x, DEmbedding.objective 0 ≤ DEmbedding.objective x) ∧
    (∀ x, DEmbedding.objective x = DEmbedding.objective 0 → x = 0) ∧
    ¬ DifferentiableAt ℝ DEmbedding.objective (0 : Vec 2) := by
  have hnn : ∀ (i : Fin 3) (x : Vec 2), 0 ≤ DEmbedding.branch i.castSucc x := fun i x => by
    rw [DEmbedding.branch_old]
    exact DScalar.phi_nonnegative (DEmbedding.parameter_bounds i).1 (DEmbedding.parameter_bounds i).2 _
  have hb0 : ∀ x : Vec 2, DEmbedding.branch 0 x = DScalar.phi 2 (dot g0 x) := fun x =>
    DEmbedding.branch_old 0 x
  have hb1 : ∀ x : Vec 2, DEmbedding.branch 1 x = DScalar.phi 2 (dot g1 x) := fun x =>
    DEmbedding.branch_old 1 x
  have hzero : ∀ x : Vec 2, DEmbedding.objective x = 0 → dot g0 x = 0 ∧ dot g1 x = 0 := by
    intro x hx
    have h0 := DEmbedding.branch_le 0 x
    have h1 := DEmbedding.branch_le 1 x
    have n0 := hnn 0 x
    have n1 := hnn 1 x
    simp only [Fin.castSucc_zero] at n0
    have e0 : DScalar.phi 2 (dot g0 x) = 0 := by rw [← hb0]; linarith
    have e1 : DScalar.phi 2 (dot g1 x) = 0 := by
      rw [← hb1]
      have : DEmbedding.branch (Fin.castSucc 1) x = DEmbedding.branch 1 x := rfl
      linarith
    exact ⟨(DScalar.phi_zero_iff (by norm_num) (by norm_num) _).mp e0,
      (DScalar.phi_zero_iff (by norm_num) (by norm_num) _).mp e1⟩
  refine ⟨hnn, fun i => DEmbedding.branch_zero _, hzero, ?_, fun x hx => DEmbedding.objective_unique_zero hx,
    fun a x hx => ?_, DEmbedding.objective_sublevels_compact, fun i => ?_,
    DEmbedding.objective_directional_derivative_zero, fun x => ?_, fun x hx => ?_,
    DEmbedding.objective_not_differentiable_zero⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have e0 := congrFun hst 0
    have e1 := congrFun hst 1
    simp [g0, g1] at e0 e1
    constructor <;> linarith
  · have h0 := (DEmbedding.branch_le 0 x).trans hx
    have h1 := (DEmbedding.branch_le 1 x).trans hx
    rw [hb0] at h0
    rw [hb1] at h1
    obtain ⟨a0, b0⟩ := DScalar.phi_sublevel_bounds (by norm_num) (by norm_num) h0
    obtain ⟨a1, b1⟩ := DScalar.phi_sublevel_bounds (by norm_num) (by norm_num) h1
    exact ⟨a0, b0, a1, b1⟩
  · have h := DEmbedding.branch_old_hasGradient i 0
    have hz : DEmbedding.ridgeGradient (DEmbedding.parameter i) (SeedOrbit.gradient seedC seedD i) 0 = 0 := by
      simp [DEmbedding.ridgeGradient, dot, DEmbedding.phiFirst_zero (DEmbedding.parameter_bounds i).1
        (DEmbedding.parameter_bounds i).2]
    rwa [hz] at h
  · rw [DEmbedding.objective_zero]
    exact DEmbedding.objective_nonnegative x
  · rw [DEmbedding.objective_zero] at hx
    exact DEmbedding.objective_unique_zero hx

/-- Item `C/12_D/disp/048` (`companion/chapters/12_D.tex:424-426`): $p_n=a_n(2,-32)^T$, the
library's `DEmbedding.center n`. -/
theorem center_def (n : ℕ) : DEmbedding.center n = scale n • ![2, -32] := rfl

/-- Item `C/12_D/prose/056` (`companion/chapters/12_D.tex:433`): "At $p_n$, the direction
$d_*=(-1,16)^T$ strictly decreases all three active branches." For $i\le2$, $f_i(p_n)=F(p_n)$
(active), and $t\mapsto f_i(p_n+td_*)$ has derivative $a_n^2g_i^Td_*<0$ at $t=0$. -/
theorem center_branch_slopes (n : ℕ) (i : Fin 3) :
    DEmbedding.branch i.castSucc (DEmbedding.center n) = DEmbedding.objective (DEmbedding.center n) ∧
    HasDerivAt (fun t : ℝ => DEmbedding.branch i.castSucc (DEmbedding.center n + t • ![-1, 16]))
      ((scale n) ^ 2 * dot (SeedOrbit.gradient seedC seedD i) ![-1, 16]) 0 ∧
    (scale n) ^ 2 * dot (SeedOrbit.gradient seedC seedD i) ![-1, 16] < 0 := by
  have hg := DEmbedding.branch_hasGradient_plateau n i (h := 0)
    (by simp [dot]; exact scale_pos n)
  rw [add_zero] at hg
  have hl : HasDerivAt (fun t : ℝ => DEmbedding.center n + t • (![-1, 16] : Vec 2)) ![-1, 16] 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (![-1, 16] : Vec 2)).const_add (DEmbedding.center n)
  have hl0 : DEmbedding.center n = DEmbedding.center n + (0 : ℝ) • (![-1, 16] : Vec 2) := by
    simp
  have hcomp := hg.comp_hasDerivAt_of_eq 0 hl hl0
  have hneg : dot (SeedOrbit.gradient seedC seedD i) ![-1, 16] < 0 := by
    obtain ⟨d0, d1, d2, d3⟩ := downhill
    fin_cases i
    · change dot g0 ![-1, 16] < 0
      rw [d0]
      norm_num
    · change dot g1 ![-1, 16] < 0
      rw [d1]
      norm_num
    · change dot (g2 seedC seedD) ![-1, 16] < 0
      rw [d2]
      linarith
  refine ⟨(DEmbedding.center_active_branches n).1 i, ?_, mul_neg_of_pos_of_neg (pow_pos (scale_pos n) 2) hneg⟩
  convert hcomp using 1
  rw [gradientFunctional_apply, PlanarUpdate.dot_scale_left]

/-- Item `C/12_D/disp/050` (`companion/chapters/12_D.tex:434-438`): "Hence
\[ F(p_n)=a_n^3>0,\qquad F'(p_n;d_*)=-a_n^2<0,\qquad0\notin\partial F(p_n)." \]
$F'(p_n;d_*)$ is the right derivative of $t\mapsto F(p_n+td_*)$ at $0$. -/
theorem center_facts (n : ℕ) :
    DEmbedding.objective (DEmbedding.center n) = (scale n) ^ 3 ∧ 0 < (scale n) ^ 3 ∧
    Tendsto (fun t : ℝ => (DEmbedding.objective (DEmbedding.center n + t • ![-1, 16]) -
      DEmbedding.objective (DEmbedding.center n)) / t) (𝓝[>] 0) (𝓝 (-(scale n) ^ 2)) ∧
    -(scale n) ^ 2 < 0 ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential DEmbedding.objective (DEmbedding.center n) := by
  obtain ⟨h1, h2, h3⟩ := Failure.center_value_slope n
  exact ⟨h1, pow_pos (scale_pos n) 3, h2, h3, DEmbedding.center_nonstationary n⟩

/-! ### Section 12.6: all rejected trials also stay in the local model

The $n$th run ($n\ge1$, pair $0<c_1\le1/3$, $c_1<c_2<1$) is `DEmbedding.run hn c₁ c₂ …`,
produced by the specified strict search (`final_orbit`). -/

/-- Item `C/12_D/disp/051` (`companion/chapters/12_D.tex:454-456`): "For each $n\ge1$, initialize
\[ x_0^{(n)}=p_n+a_n^2z_0,\qquad H_0=I." \]
The runs `DEmbedding.run` start there. -/
theorem initial_def (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) :
    (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x 0 = DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0 ∧
    (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 := by
  refine ⟨?_, DEmbedding.run_initial_matrix hn hc₁ hc₁' hc hc₂⟩
  change DEmbedding.center n + (scale n) ^ 2 • orbitPoint 0 = _
  rw [Failure.seedPoint_zero_eq]

/-- Item `C/12_D/disp/052` (`companion/chapters/12_D.tex:458-461`), equation `D:finalorbit`: "The
claimed deterministic trajectory is
\[ x_{3m+j}^{(n)}=p_n+a_n^2\rho^mz_j,\qquad H_{3m+j}^{(n)}=\rho^mM_j,\qquad j=0,1,2." \]
For $n\ge1$ and every $0<c_1\le1/3$, $c_1<c_2<1$: the run produced on $F$ by the specified strict
search from $x_0^{(n)}$, $H_0=I$ (any budget $N\ge5$) is unique, is `DEmbedding.run`, and
satisfies the display. -/
theorem final_orbit (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 DEmbedding.objective,
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0 ∧
      R.H 0 = 1 ∧ R.x = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x ∧
      R.H = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H ∧
      (∀ k N, 5 ≤ N → DeterministicLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ N =
        (some (R.α k), trialHistory (phase k))) ∧
      (∀ R' : AdmissibleBFGSRun 2 DEmbedding.objective,
        R'.x 0 = DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0 → R'.H 0 = 1 →
        (∀ k, ∃ N L, DeterministicLineSearch.fromMetric DEmbedding.objective (R'.x k) (R'.H k) c₁ c₂ N =
          (some (R'.α k), L)) → R'.x = R.x ∧ R'.H = R.H) ∧
      ∀ (m : ℕ) (j : Fin 3),
        R.x (3 * m + j) = DEmbedding.center n + ((scale n) ^ 2 * seedRatio ^ m) • Failure.seedPoint j.castSucc ∧
        R.H (3 * m + j) = seedRatio ^ m • metric seedC seedD j := by
  obtain ⟨hx0, hH0⟩ := initial_def n hn c₁ c₂ hc₁ hc₁' hc hc₂
  have hs : ∀ k, DeterministicLineSearch.fromMetric DEmbedding.objective
      ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k) ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
      c₁ c₂ 5 = (some ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).α k), trialHistory (phase k)) :=
    fun k => DEmbedding.run_search hn hc₁ hc₁' hc hc₂ k
  refine ⟨DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, hx0, hH0, rfl, rfl,
    fun k N hN => fromMetric_fuel_mono (hs k) hN, ?_, fun m j => ?_⟩
  · intro R' hx' hH' hs'
    obtain ⟨h1, h2, -, -⟩ := implemented_run_unique R' (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂)
      (hx'.trans hx0.symm) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, hs k⟩)
    exact ⟨h1, h2⟩
  · obtain ⟨hx, hH, -, -⟩ := DEmbedding.run_phase_parameters hn hc₁ hc₁' hc hc₂ m j
    refine ⟨hx.trans ?_, hH⟩
    rw [Failure.seedPoint_castSucc, smul_smul]

/-- The phase of the iterate $3m+j$ is $j$. -/
theorem phase_cycle (m : ℕ) (j : Fin 3) : phase (3 * m + j) = j := by
  apply Fin.ext
  change (3 * m + j.val) % 3 = j.val
  have := j.isLt
  omega

/-- Item `C/12_D/disp/053` (`companion/chapters/12_D.tex:463-465`): "At the corresponding phase,
\emph{every} trial generated by the line search has the form
\[ p_n+a_n^2\rho^m z_{\rm trial}, \]
where $z_{\rm trial}$ is one of the nine base trials already certified." At the iterate $3m+j$
of the $n$th run the search makes the trials of phase $j$ of the table (`trialHistory j`), and the
trial point of length $a$ is $p_n+a_n^2\rho^m z_q$ for the row $q$ of phase $j$ with length $a$
($z_q$ = `query q`). -/
theorem trial_form (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (m : ℕ) (j : Fin 3) :
    DeterministicLineSearch.fromMetric DEmbedding.objective
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m + j))
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m + j)) c₁ c₂ 5 =
      (some ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).α (3 * m + j)), trialHistory j) ∧
    ∀ a ∈ trialHistory j, ∃ q : Fin 9, trialPhase q = j ∧ trialLength q = a ∧
      (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m + j) +
          a • bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m + j))
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g (3 * m + j)) 1 =
        DEmbedding.center n + ((scale n) ^ 2 * seedRatio ^ m) • query q := by
  refine ⟨?_, fun a ha => ?_⟩
  · have h := DEmbedding.run_search hn hc₁ hc₁' hc hc₂ (3 * m + j)
    dsimp only at h
    rwa [phase_cycle] at h
  · obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
    refine ⟨q, hq, rfl, ?_⟩
    have h1 := (cone_scaling m j q hq 0 0).1
    have h2 : (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m + j) + trialLength q •
        bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m + j))
          ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g (3 * m + j)) 1 =
        DEmbedding.center n + (scale n) ^ 2 • SeedEmbedding.trialPoint (3 * m + j) q :=
      SeedEmbedding.translated_trial _ _ _ q
    rw [h2, SeedEmbedding.trialPoint, h1, smul_smul, query, hq]

/-- Item `C/12_D/prose/057` (`companion/chapters/12_D.tex:471`): "Thus~\eqref{D:localcone} holds at
every accepted and rejected trial." For $n\ge1$, $m\ge0$ and each row $q$, the trial displacement
$h=a_n^2\rho^mz_q$ satisfies the slab condition $|g_i^Th|\le a_n/2$ ($i=0,1,2$) of `D:localcone`,
and $F(p_n+h)=a_n^3+a_n^2G(h)$. -/
theorem local_model_at_trials (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : Fin 9) :
    (∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) (((scale n) ^ 2 * seedRatio ^ m) • query q)| ≤
      scale n / 2) ∧
    DEmbedding.objective (DEmbedding.center n + ((scale n) ^ 2 * seedRatio ^ m) • query q) =
      (scale n) ^ 3 + (scale n) ^ 2 * objective seedC seedD (((scale n) ^ 2 * seedRatio ^ m) • query q) := by
  have hslab : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) (((scale n) ^ 2 * seedRatio ^ m) • query q)| ≤
      scale n / 2 := fun i => by
    obtain ⟨h1, h2, h3⟩ := Failure.query_slab n hn m q i
    exact (h1.trans_le h2).le.trans h3.le
  exact ⟨hslab, DEmbedding.local_cone n hslab⟩

/-- Item `C/12_D/prose/058` (`companion/chapters/12_D.tex:477`): "Every function difference and every
predicted directional decrease is the corresponding seed quantity multiplied by $a_n^4\rho^m$. The
additive $a_n^3$ cancels from Armijo. Therefore all rejection and acceptance decisions are the same
as in the seed table. In particular the accepted lengths are actual outputs of the deterministic
search."

At the iterate $k=3m+j$ of the $n$th run ($x$, $H$, $g$ its point, matrix and gradient,
$p=-Hg$) and each row $q$ of phase $j$ with length $\alpha$: $F(x+\alpha p)-F(x)=a_n^4\rho^m
(G(z_q)-G(z_j))$; $g^T(\alpha p)=a_n^4\rho^m\,g_j^T(\alpha p_j)$; the strict Armijo and weak Wolfe
tests decide as in the seed table (at $(z_j,p_j,g_j)$); and the search returns the accepted
length $\alpha_j$ with the trial list of phase $j$. -/
theorem embedded_decisions (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (m : ℕ) (j : Fin 3) (q : Fin 9) (hq : trialPhase q = j)
    (x : Vec 2) (H : Mat 2) (g p : Vec 2)
    (hx : x = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (3 * m + j))
    (hH : H = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H (3 * m + j))
    (hg : g = (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g (3 * m + j)) (hp : p = bfgsStep H g 1) :
    DEmbedding.objective (x + trialLength q • p) - DEmbedding.objective x =
      (scale n) ^ 4 * seedRatio ^ m *
        (objective seedC seedD (query q) - objective seedC seedD (Failure.seedPoint j.castSucc)) ∧
    dot g (trialLength q • p) =
      (scale n) ^ 4 * seedRatio ^ m * dot (SeedOrbit.gradient seedC seedD j) (trialLength q • Failure.seedDir j) ∧
    (DeterministicLineSearch.Armijo DEmbedding.objective x p g c₁ (trialLength q) ↔
      DeterministicLineSearch.Armijo (objective seedC seedD) (Failure.seedPoint j.castSucc) (Failure.seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₁ (trialLength q)) ∧
    (DeterministicLineSearch.Wolfe DEmbedding.objective x p g c₂ (trialLength q) ↔
      DeterministicLineSearch.Wolfe (objective seedC seedD) (Failure.seedPoint j.castSucc) (Failure.seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₂ (trialLength q)) ∧
    DeterministicLineSearch.fromMetric DEmbedding.objective x H c₁ c₂ 5 = (some (length j), trialHistory j) := by
  have hph := phase_cycle m j
  have hq' : trialPhase q = phase (3 * m + j) := hq.trans hph.symm
  obtain ⟨hpx, -, hpg, hpα⟩ := orbit_phase_parameters m j
  obtain ⟨c1, c2, -, -, c5, c6⟩ := cone_scaling m j q hq c₁ c₂
  have ht : 0 < (scale n) ^ 2 := pow_pos (scale_pos n) 2
  have hρ : 0 < seedRatio ^ m := pow_pos source_ratio_pos_lt_one.1 m
  have hz : orbitPoint (3 * m + j) = seedRatio ^ m • Failure.seedPoint j.castSucc := by
    rw [hpx, Failure.seedPoint_castSucc]
  have hxe : x = DEmbedding.center n + (scale n) ^ 2 • orbitPoint (3 * m + j) := hx
  have hge : g = (scale n) ^ 2 • orbitGradient (3 * m + j) := hg
  have hHe : H = orbitMetric (3 * m + j) := hH
  have hpe : p = (scale n) ^ 2 • bfgsStep (orbitMetric (3 * m + j)) (orbitGradient (3 * m + j)) 1 := by
    rw [hp, hHe, hge, bfgsStep_scale_gradient]
  have htrial : x + trialLength q • p = DEmbedding.center n + (scale n) ^ 2 •
      SeedEmbedding.trialPoint (3 * m + j) q := by
    rw [hx, hp, hH, hg]
    exact SeedEmbedding.translated_trial _ _ _ q
  have hvt := DEmbedding.certified_value hn (orbit_trial_point_certificate (3 * m + j) q hq')
  have hvx := DEmbedding.certified_value hn (DEmbedding.orbit_certificate (3 * m + j))
  have htp : SeedEmbedding.trialPoint (3 * m + j) q = seedRatio ^ m • query q := by
    rw [SeedEmbedding.trialPoint, c1, query, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htrial, SeedEmbedding.trialPoint, hvt, c1, hxe, hvx, hz, Failure.seed_objective_homogeneous hρ.le,
      Failure.seed_objective_homogeneous hρ.le, query, hq]
    ring
  · rw [hge, hpe, c2, hpg]
    simp only [PlanarUpdate.dot_scale_left, dot_smul_right]
    ring
  · have hA := (SeedEmbedding.trial_predicates (DEmbedding.actualOracleData hn) ht (3 * m + j) q hq' c₁ c₂).1
    rw [c2, hpg, hz] at hA
    rw [hx, hp, hH, hg]
    exact hA.trans c5
  · have hW := (SeedEmbedding.trial_predicates (DEmbedding.actualOracleData hn) ht (3 * m + j) q hq' c₁ c₂).2
    rw [c2, hpg, hz] at hW
    rw [hx, hp, hH, hg]
    exact hW.trans c6
  · have h := DEmbedding.run_search hn hc₁ hc₁' hc hc₂ (3 * m + j)
    dsimp only at h
    rw [hph] at h
    rw [hx, hH, h]
    change (some (orbitLength (3 * m + j)), trialHistory j) = _
    rw [hpα]

/-- Item `C/12_D/prose/059` (`companion/chapters/12_D.tex:479`): "Substituting gradients scaled by
$a_n^2$ and steps scaled by $a_n^2\rho^m$ into~\eqref{D:bfgs} leaves the projection factors
unchanged and scales the rank-one term by $\rho^m$. This proves the matrix part
of~\eqref{D:finalorbit}."

For a matrix $\rho^mH$ ($r=\rho^m>0$) and gradients $\lambda g,\lambda g^+$ ($\lambda=a_n^2>0$): the
step is $s'=\lambda r\,s$ and $y'=\lambda y$, where $s=-\alpha Hg$, $y=g^+-g$; the projection
factors $s'y'^T/(y'^Ts')$ and $y's'^T/(y'^Ts')$ are those of $(s,y)$; the rank-one term is $r$
times that of $(s,y)$; so $\mathcal B(rH,\lambda g,\lambda g^+,\alpha)=r\,\mathcal B(H,g,g^+,\alpha)$. -/
theorem scaled_update {n : ℕ} (H : Mat n) (g gplus : Vec n) (α lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (s y s' y' : Vec n) (hs : s = bfgsStep H g α) (hy : y = gplus - g)
    (hs' : s' = bfgsStep (r • H) (lam • g) α) (hy' : y' = lam • gplus - lam • g) :
    s' = (lam * r) • s ∧ y' = lam • y ∧
    (dot y' s')⁻¹ • outer s' y' = (dot y s)⁻¹ • outer s y ∧
    (dot y' s')⁻¹ • outer y' s' = (dot y s)⁻¹ • outer y s ∧
    (dot y' s')⁻¹ • outer s' s' = r • ((dot y s)⁻¹ • outer s s) ∧
    Failure.fullUpdate (r • H) (lam • g) (lam • gplus) α = r • Failure.fullUpdate H g gplus α := by
  have hs'' : s' = (lam * r) • s := by
    rw [hs', hs, bfgsStep_scale_matrix, bfgsStep_scale_gradient, smul_smul, mul_comm r lam]
  have hy'' : y' = lam • y := by rw [hy', hy, smul_sub]
  have hdot : dot y' s' = (lam * (lam * r)) * dot y s := by
    rw [hy'', hs'', dot_smul_right, PlanarUpdate.dot_scale_left]
    ring
  have hl : lam ≠ 0 := hlam.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hc : lam * (lam * r) ≠ 0 := mul_ne_zero hl (mul_ne_zero hl hr')
  have scal : ∀ t : ℝ, (lam * (lam * r) * t)⁻¹ * (lam * (lam * r)) = t⁻¹ := fun t => by
    rw [mul_inv, mul_comm (lam * (lam * r))⁻¹ t⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  refine ⟨hs'', hy'', ?_, ?_, ?_, ?_⟩
  · rw [hdot, hs'', hy'', outer_scale_left, outer_scale_right, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, show lam * r * lam = lam * (lam * r) by ring]
    exact scal _
  · rw [hdot, hs'', hy'', outer_scale_left, outer_scale_right, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc]
    exact scal _
  · rw [hdot, hs'', outer_scale_left, outer_scale_right, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, show lam * r * (lam * r) = lam * (lam * r) * r by ring, ← mul_assoc, scal, mul_comm]
  · rw [Failure.fullUpdate, Failure.fullUpdate, bfgsStep_scale_matrix, bfgsStep_scale_gradient,
      ← smul_sub, smul_comm r lam, inverseBFGS_scale_secant_pair _ _ _ hl, inverseBFGS_scale _ _ _ hr']

/-- Item `C/12_D/prose/060` (`companion/chapters/12_D.tex:479`): "All finite matrices are SPD, and all
oracle evaluations are at differentiable points." For the $n$th run: every matrix $H_k$ is
positive definite (`Matrix.PosDef`: symmetric positive definite), and $F$ is differentiable at
every iterate and every trial point. -/
theorem spd_differentiable (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    (∀ k, ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k).PosDef) ∧
    ∀ k, DifferentiableAt ℝ DEmbedding.objective ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k) ∧
      ∀ a ∈ trialHistory (phase k), DifferentiableAt ℝ DEmbedding.objective
        ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k + a •
          bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1) := by
  refine ⟨(DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).positive_definite, fun k =>
    ⟨((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).hasGradient k).differentiableAt, fun a ha => ?_⟩⟩
  obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
  exact (DEmbedding.run_all_trials_differentiable hn hc₁ hc₁' hc hc₂ k q hq).differentiableAt

/-- Item `C/12_D/disp/056` (`companion/chapters/12_D.tex:482-485`): "Consequently,
\[ x_k^{(n)}\to p_n\ne0,\qquad F(x_k^{(n)})\downarrow a_n^3>0." \]
For the $n$th run: convergence to $p_n\ne0$, strictly decreasing values with limit
$a_n^3=F(p_n)>0$. -/
theorem final_limits (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    Tendsto (DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x atTop (𝓝 (DEmbedding.center n)) ∧
    DEmbedding.center n ≠ 0 ∧
    (∀ k, DEmbedding.objective ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x (k + 1)) <
      DEmbedding.objective ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)) ∧
    Tendsto (fun k => DEmbedding.objective ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)) atTop
      (𝓝 ((scale n) ^ 3)) ∧
    0 < (scale n) ^ 3 := by
  have h := DEmbedding.run_value_tendsto hn hc₁ hc₁' hc hc₂
  rw [DEmbedding.center_value] at h
  exact ⟨DEmbedding.run_point_tendsto hn hc₁ hc₁' hc hc₂, DEmbedding.center_ne_zero n,
    DEmbedding.run_value_strict_decrease hn hc₁ hc₁' hc hc₂, h, pow_pos (scale_pos n) 3⟩

/-- Item `C/12_D/prose/061` (`companion/chapters/12_D.tex:486`): "Yet $x_0^{(n)}\to0$ and
$F(x_0^{(n)})\to0$." -/
theorem initial_limits :
    Tendsto (fun n => DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0) atTop (𝓝 0) ∧
    Tendsto (fun n => DEmbedding.objective (DEmbedding.center n + (scale n) ^ 2 • Failure.seedPoint 0))
      atTop (𝓝 0) := by
  have e : Failure.seedPoint 0 = orbitPoint 0 := Failure.seedPoint_zero_eq
  rw [e]
  exact ⟨DEmbedding.initial_points_tendsto, DEmbedding.initial_values_tendsto⟩

/-- $\max_{\rm base\ trials}\|z_{\rm trial}\|$: the maximum of the Euclidean norms of the nine base
trials of the table. -/
def baseTrialMax : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : Fin 9 => ‖euclideanVector (query q)‖)

theorem baseTrialMax_eq : baseTrialMax = DEuclideanLocality.maxTrialNorm := by
  unfold baseTrialMax DEuclideanLocality.maxTrialNorm
  congr 1
  funext q
  rw [query, Failure.seed_query_eq]

/-- Item `C/12_D/disp/057` (`companion/chapters/12_D.tex:487-489`), with line 486: "Also the
supremum of the norms of \emph{all accepted and trial points} in the $n$th trajectory is bounded
by
\[ a_n\|(2,-32)\|+a_n^2\max_{\rm base\ trials}\|z_{\rm trial}\|\to0." \]
Euclidean norms. For $n\ge1$ and every admissible pair, every accepted point and every trial point
of the $n$th run has norm at most the bound, so the supremum of these norms is at most the bound
(the set is bounded above); and the bound tends to $0$. -/
theorem trajectory_bound :
    (∀ (n : ℕ) (hn : 1 ≤ n) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1),
      (∀ k, ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)‖ ≤
          scale n * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale n) ^ 2 * baseTrialMax ∧
        ∀ a ∈ trialHistory (phase k),
          ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k + a •
            bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
              ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1)‖ ≤
          scale n * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale n) ^ 2 * baseTrialMax) ∧
      BddAbove {r : ℝ | ∃ k, r = ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)‖ ∨
        ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k +
          a • bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1)‖} ∧
      sSup {r : ℝ | ∃ k, r = ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)‖ ∨
        ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k +
          a • bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1)‖} ≤
        scale n * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale n) ^ 2 * baseTrialMax) ∧
    Tendsto (fun n => scale n * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale n) ^ 2 * baseTrialMax)
      atTop (𝓝 0) := by
  have hb : ∀ n, scale n * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale n) ^ 2 * baseTrialMax =
      DEuclideanLocality.sourceBound n := fun n => by
    rw [baseTrialMax_eq, DEuclideanLocality.sourceBound]
  refine ⟨fun n hn c₁ c₂ hc₁ hc₁' hc hc₂ => ?_, ?_⟩
  · rw [hb n]
    have hpt : ∀ k, ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)‖ ≤
        DEuclideanLocality.sourceBound n := fun k =>
      DEuclideanLocality.translated_bound n (DEuclideanLocality.orbit_le_max k)
    have htr : ∀ k, ∀ a ∈ trialHistory (phase k),
        ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k + a •
          bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1)‖ ≤ DEuclideanLocality.sourceBound n := by
      intro k a ha
      obtain ⟨q, hq, rfl⟩ := Failure.mem_trialHistory ha
      change ‖euclideanVector (SeedEmbedding.point (DEmbedding.center n) ((scale n) ^ 2) k +
        trialLength q • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale n) ^ 2) k) 1)‖ ≤ _
      rw [SeedEmbedding.translated_trial]
      exact DEuclideanLocality.translated_bound n (DEuclideanLocality.actual_trial_le_max k q hq)
    have hmem : ∀ r ∈ {r : ℝ | ∃ k, r = ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k)‖ ∨
        ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).x k +
          a • bfgsStep ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1)‖}, r ≤ DEuclideanLocality.sourceBound n := by
      rintro r ⟨k, rfl | ⟨a, ha, rfl⟩⟩
      · exact hpt k
      · exact htr k a ha
    refine ⟨fun k => ⟨hpt k, htr k⟩, ⟨_, hmem⟩, csSup_le ⟨_, 0, Or.inl rfl⟩ hmem⟩
  · simpa only [hb] using DEuclideanLocality.source_bound_tendsto

/-! ### Non-vacuity -/

/-- The standing assumptions of this file can all hold at once: the parameter range contains
$(10^{-4},1/2)$; $b=2$ is admissible; $\overline G$ exists; the standing assumptions of the
derivation paragraph (lines 167-189) hold at the chapter's root $(c,d)$ with $\beta=1/4$,
$\gamma=1/16$; there is a nonzero $w\perp(g_0-g_2)$; there is a point inside a ramp; there are
accepted and rejected rows; $G$ is differentiable at $z_0$ (hypothesis of `specified_search`). -/
example : ((0 : ℝ) < 1 / 10 ^ 4 ∧ (1 / 10 ^ 4 : ℝ) ≤ 1/3 ∧ (1 / 10 ^ 4 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1) ∧
    ((2 : ℝ) = 2 ∨ (2 : ℝ) = DEmbedding.bStar) ∧
    (∃ Gbar : Vec 2 → ℝ, ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) ∧
    (beta seedC seedD = 66048 * AlgebraicSeed.R seedC seedD * AlgebraicSeed.K seedC seedD /
        (AlgebraicSeed.U seedC seedD * AlgebraicSeed.V seedC seedD * (AlgebraicSeed.U seedC seedD + 129)) ∧
      AlgebraicSeed.U seedC seedD * AlgebraicSeed.V seedC seedD * (AlgebraicSeed.U seedC seedD + 129) ≠ 0 ∧
      AlgebraicSeed.R seedC seedD * AlgebraicSeed.U seedC seedD * AlgebraicSeed.Y seedC seedD ≠ 0 ∧
      AlgebraicSeed.U seedC seedD * (AlgebraicSeed.U seedC seedD + 129) * AlgebraicSeed.Y seedC seedD ≠ 0 ∧
      dot (g2 seedC seedD - g1) (bfgsStep M1 g1 (beta seedC seedD)) ≠ 0 ∧
      dot (g0 - g2 seedC seedD) (bfgsStep (Failure.fullUpdate M1 g1 (g2 seedC seedD) (beta seedC seedD))
        (g2 seedC seedD) (gamma seedC seedD)) ≠ 0) ∧
    (∃ w : Vec 2, w ≠ 0 ∧ dot w (g0 - g2 seedC seedD) = 0) ∧
    (∃ x : ℝ, DScalarRamp.center 2 - DScalarRamp.epsilon < coordinate 2 (scale 0) x ∧
      coordinate 2 (scale 0) x < DScalarRamp.center 2 + DScalarRamp.epsilon) ∧
    trialAccept 0 = true ∧ trialAccept 1 = false ∧
    HasFDerivAt (objective seedC seedD) (gradientFunctional g0) (Failure.seedPoint 0) := by
  obtain ⟨hU, hV, hR, -, -, hY, hA, -, -⟩ := AlgebraicSeed.box_denominators_and_ratio AlgebraicSeed.root_spec.1
  obtain ⟨hβ, hγ, -⟩ := source_parameters
  obtain ⟨-, -, -, h4⟩ := AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1
  have hcurv := (formal_checks.1 1).1
  have hlast := (formal_checks.1 2).1
  refine ⟨by norm_num, Or.inl rfl, ⟨_, fun _ => rfl⟩,
    ⟨rfl, (mul_pos (mul_pos hU hV) hA).ne', (mul_pos (mul_pos hR hU) hY).ne',
      (mul_pos (mul_pos hU hA) hY).ne', ?_, ?_⟩, ⟨![seedD, 1 - seedC], ?_, ?_⟩,
    ⟨2 * scale 0 * (theta + (1 - theta) * DScalarRamp.center 2), ?_⟩, rfl, rfl, ?_⟩
  · rw [hβ]
    exact hcurv.ne'
  · rw [hβ, hγ]
    exact hlast.ne'
  · intro h0
    have e := congrFun h0 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at e
    change AlgebraicSeed.root 1 = 0 at e
    linarith
  · simp only [dot, Fin.sum_univ_two, Pi.sub_apply, g0, g2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  · have hc : coordinate 2 (scale 0) (2 * scale 0 * (theta + (1 - theta) * DScalarRamp.center 2)) =
        DScalarRamp.center 2 := by
      unfold coordinate
      have hs : scale 0 = 1 := pow_zero theta
      rw [hs]
      norm_num [theta]
    rw [hc]
    have he : (0 : ℝ) < DScalarRamp.epsilon := by norm_num [DScalarRamp.epsilon]
    constructor <;> linarith
  · rw [Failure.seedPoint_zero_eq]
    exact orbit_hasGradient 0

end BfgsCoverage.Companion.Ch12D
