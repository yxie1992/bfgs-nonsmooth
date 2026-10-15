import BfgsVerification.DNonStrictObjectives
import BfgsVerification.DEuclideanLocality
import BfgsVerification.DDisplayPrecision
import BfgsVerification.DLiteralTargets
import BfgsVerification.LQuadraticSeed
import BfgsArticle.NonStrictTransfer
import BfgsArticle.LUniformLocal

/-!
# Lean coverage: `paper/sections/failure.tex`

Section `art:failure` ("Failure: a contracting mechanism and local realizations"). Register:
`editorial/lean_coverage/register/A_failure.json`. Theorem `art:local-failure` itself
(`paper/statements/negative_upper.tex`, included at line 49) is covered in
`BfgsArticle.Coverage.Article.NegativeUpper`; its proof (lines 385-425) is covered here.

## The specified implementation (lines 21-44)

The line search is `NonStrictLineSearch.fromMetric F x H c₁ c₂ N`
(`specified_search`): at a differentiable point $x$ it uses $g=\nabla F(x)$
(`coordinateGradient`) and $p=-Hg$, starts with $\alpha_{\rm lo}=0$,
$\alpha_{\rm hi}=+\infty$ (`none`), $\alpha=1$, tests the non-strict Armijo and weak Wolfe
inequalities `art:failure_tests` in this order (`NonStrictLineSearch.Armijo`,
`NonStrictLineSearch.Wolfe`), bisects after an Armijo rejection and doubles (or bisects
once $\alpha_{\rm hi}<\infty$) after a Wolfe rejection. It returns the accepted length and the
list of all trial lengths; the budget `N` only bounds the number of trials
(`fromMetric_fuel_mono`). A run of the implementation is an `AdmissibleBFGSRun` (step
$x_{k+1}=x_k-\alpha_kH_kg_k$, full update `art:failure_update` = `fullUpdate` at every
step) whose lengths are the outputs of the search; it is determined by its initial point and
matrix (`implemented_run_unique`). The theorems below state the search equations for the
runs, for every pair $0<c_1\le1/3$, $c_1<c_2<1$ of Theorem `art:local-failure`.

## The parameter range of Lemma `art:seed_cycle` and Table `art:trial_table` (corrected, M11)

The query list and the Decision column depend on the line-search constants: the Armijo ratios
at the accepted trials are about $0.76658$, $0.39319$, $0.37521$ (`accepted_armijo_iff`,
`accepted_armijo_ratios`), so for $c_1=0.38$, $c_2=1/2$ the phase-2 trial $1/16$ is rejected
(`seed_cycle_range_counterexample`). Until 15 October 2026 the lemma and the table fixed no
constants; the correction M11 added the range $0<c_1\le1/3$, $c_2>0$ to the lemma's query-list
sentence and to the table's caption (lines 107-108 and 147-148). `seed_cycle` and `trial_table`
state the claims for this range, which contains that of Theorem `art:local-failure`.

## Notation

* $(c_\circ,d_\circ)$ = (`seedC`, `seedD`) = (`root 0`, `root 1`), the root of Lemma
  `art:root_certificate`; $\rho$ = `seedRatio`; $g_i$ = `SeedOrbit.gradient seedC seedD i`
  (`g0`, `g1`, `g2 seedC seedD`); $G$ = `SeedOrbit.objective seedC seedD`;
  $M_j$ = `SeedOrbit.metric seedC seedD j`; $\alpha_j$ = `SeedOrbit.length j`.
* Defined here, literally as in the TeX: `seedStep` ($s_0,s_1,s_2$), `seedStart` ($z_0$),
  `seedPoint` ($z_0,\dots,z_3$), `seedDir` ($p_j=-M_jg_j$), `seedSlope` ($g_0,\dots,g_3$ with
  $g_3=g_0$), `fullUpdate` ($\mathcal B$), the enclosure columns of Table `art:trial_table`
  (`currentLower`, `currentUpper`, `trialLower`, `trialUpper`) and `baseQueryMax`.
* Table `art:trial_table`: the library's `trialPhase`, `trialLength`, `trialActive`,
  `trialAccept` are its columns (rows `q : Fin 9`); `trialHistory j` is the trial list of
  phase $j$; `phase k = k % 3`.
* Scalar functions: $\theta$ = `DScalarGeometric.theta` = `DScalarRamp.theta` $=1/16$,
  $a_\ell$ = `scale ℓ`, $\varepsilon$ = `DScalarRamp.epsilon` $=1/128$, $b_*$ =
  `DEmbedding.bStar`, $t_b$ = `DScalarRamp.center b`, $v$ = `DScalarRamp.rampCoordinate b ξ`,
  $P_b$ = `DScalarRamp.ramp b`, $J_b$ = `DScalarRamp.primitive b`, $\varphi_b$ =
  `DScalar.phi b` (`phi_formulas`, `phi_unique`).
* The objective `art:upper_objective` is `DEmbedding.objective`, the maximum of
  `DEmbedding.branch i`; $\bar x_\ell$ = `DEmbedding.center ℓ`; the $\ell$th run is
  `DEmbedding.run`, the seed run is `SeedOrbit.run` (`orbitPoint`, `orbitMetric`), and the run
  on $\overline G$ is `SeedOrbit.coerciveRun`.
* `Vec 2` carries the sup norm; Euclidean norms are `‖euclideanVector z‖`; Hessians are
  `RadialHessian.matrix`, the matrix of `fderiv ℝ (fderiv ℝ F) x`. Where $F$ is differentiable
  on a neighborhood of $x$ and the derivative map is differentiable at $x$ (the convention of
  lines 484-486), it is the classical Hessian, the derivative of the gradient map
  (`classical_hessian`); the branches of the first construction are $C^2$, so this holds at
  every point.
* `lam` stands for $\lambda$ and `𝒢` for $\mathcal G$ in the covariance theorems.

## Items

| Item | Lines | Lean |
|---|---|---|
| `prose/003`, `disp/001` (`art:failure_tests`) | 22-32, 26-29 | `specified_search`, `failure_tests` |
| `prose/005`, `prose/006` | 34-35, 44 | `strict_tests_same_decisions`, `strict_tests_same_decisions_lower`, `run_update_full` |
| `disp/002` (`art:failure_update`) | 38-43 | `fullUpdate`, `failure_update` |
| `prose/009`, `prose/010` | 52-54 | `failure_starts_null`, `no_uniform_lower_curvature` |
| `prose/012` | 66 | `target_lengths_bisections` |
| `disp/003`-`disp/006`, `prose/014`, `prose/015` | 74-98 | `seed_slopes`, `seed_coarse_bounds`, `seed_rho`, `seed_matrices_steps`, `seed_points`, `displacement_closure` |
| `lemma/art:seed_cycle` (corrected), `disp/007`-`disp/009` | 100-120 | `seed_cycle`, `seed_closures`, `seed_margins`, `seed_query_bounds` |
| `table/art:trial_table` (corrected), `prose/016`-`prose/023` | 122-162 | `trial_table`, `rejected_raise_value`, `accepted_pass_tests`, `seed_search`, `no_wolfe_rejection` |
| range of the lemma and the table (corrected, M11) | 107-108, 147-148 | `accepted_armijo_iff`, `accepted_armijo_ratios`, `seed_cycle_range_counterexample` |
| `disp/010`, `disp/011`, `prose/026`-`prose/028` | 184-200 | `cone_orbit`, `downhill_direction`, `cone_orbit_scaling`, `cone_limit_nonstationary` |
| `corollary/art:failure_polyhedral` (`disp/012`) | 202-209 | `failure_polyhedral` |
| `disp/013`, `disp/014`, `prose/032`-`prose/038` | 227-260 | `matched_scaling`, `matched_update`, `matched_comparisons`, `matched_search_transfer`, `matched_run_transfer`, `matched_identity_matrix`, `first_embedding_scales` |
| `prose/039`-`prose/043`, `disp/015`-`disp/018` | 263-303 | `scalar_nodes`, `phi_unique`, `scalar_constants`, `ramp_center_coordinate`, `ramp_primitive`, `primitive_formulas`, `phi_formulas` |
| `lemma/art:upper_scalar_lemma` (`disp/019`, `disp/020`), `disp/021`, `disp/022` | 305-354 | `upper_scalar_lemma`, `positive_interval_derivatives`, `constant_derivative_lengths` |
| `disp/023`, `disp/024`, `prose/044`-`prose/048` | 358-383 | `upper_objective`, `upper_local_model`, `objective_branch_hessians`, `objective_minimizer`, `center_arguments`, `local_model_branches`, `center_value_slope` |
| `disp/025`-`disp/028` (proof of Theorem `art:local-failure`) | 387-422 | `upper_orbit`, `query_slab`, `query_values`, `query_norm_bound` |
| `prose/050` (Figure `art:shrinking-scales`) | 436-439 | `shrinking_scales` |
| `prose/052`-`prose/054`, `prose/056`, `prose/059` | 449-486 | `no_uniform_lower_curvature`, `quadratic_restores_curvature`, `quadratic_changes_dynamics`, `regularity_map_first_row`, `classical_hessian` |

The remaining items (summaries, restatements of the theorems, statements about the
lower-curvature construction, figure and table items) are `SAME_AS`, `PART_OF`, `PROOF` or
`NON_CLAIM` in the register. An `example` at the end shows that the standing assumptions can
hold at once.
-/

noncomputable section
open Set Filter Matrix BfgsVerification
open scoped Topology

namespace BfgsCoverage.Article.Failure

open SeedOrbit SeedCycle

/-! ### The specified implementation -/

/-- A successful search keeps its output when one more trial is allowed. -/
theorem search_fuel_succ {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ : ℝ} :
    ∀ (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a b : ℝ) (L : List ℝ),
      NonStrictLineSearch.search F x p g c₁ c₂ fuel l h a = (some b, L) →
      NonStrictLineSearch.search F x p g c₁ c₂ (fuel + 1) l h a = (some b, L) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l h a b L hs
    simp [NonStrictLineSearch.search] at hs
  | succ fuel ih =>
    intro l h a b L hs
    by_cases hA : NonStrictLineSearch.Armijo F x p g c₁ a
    · by_cases hW : NonStrictLineSearch.Wolfe F x p g c₂ a
      · rw [NonStrictLineSearch.search_accept fuel hA hW] at hs
        rw [NonStrictLineSearch.search_accept (fuel + 1) hA hW, hs]
      · rw [NonStrictLineSearch.search, if_pos hA, if_neg hW] at hs ⊢
        generalize hr : NonStrictLineSearch.search F x p g c₁ c₂ fuel a h
          (NonStrictLineSearch.nextTrial a h) = r at hs
        obtain ⟨r1, r2⟩ := r
        simp only [Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [ih a h (NonStrictLineSearch.nextTrial a h) b r2 hr]
    · rw [NonStrictLineSearch.search, if_neg hA] at hs ⊢
      generalize hr : NonStrictLineSearch.search F x p g c₁ c₂ fuel l (some a)
        (NonStrictLineSearch.nextTrial l (some a)) = r at hs
      obtain ⟨r1, r2⟩ := r
      simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [ih l (some a) (NonStrictLineSearch.nextTrial l (some a)) b r2 hr]

/-- The trial budget only bounds the number of trials: a successful output of the
specified search is its output for every larger budget. -/
theorem fromMetric_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x : Vec n} {H : Mat n} {c₁ c₂ : ℝ}
    {fuel N : ℕ} {b : ℝ} {L : List ℝ}
    (hs : NonStrictLineSearch.fromMetric F x H c₁ c₂ fuel = (some b, L)) (hN : fuel ≤ N) :
    NonStrictLineSearch.fromMetric F x H c₁ c₂ N = (some b, L) := by
  unfold NonStrictLineSearch.fromMetric at hs ⊢
  induction N, hN using Nat.le_induction with
  | base => exact hs
  | succ N _ ih => exact search_fuel_succ N 0 none 1 b L ih

/-- The implementation is deterministic: two full-BFGS runs on the same objective with the
same initial point and matrix, whose lengths are outputs of the specified search (with some
trial budgets), coincide. -/
theorem implemented_run_unique {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ}
    (R R' : AdmissibleBFGSRun n F) (hx : R.x 0 = R'.x 0) (hH : R.H 0 = R'.H 0)
    (hs : ∀ k, ∃ N L, NonStrictLineSearch.fromMetric F (R.x k) (R.H k) c₁ c₂ N = (some (R.α k), L))
    (hs' : ∀ k, ∃ N L, NonStrictLineSearch.fromMetric F (R'.x k) (R'.H k) c₁ c₂ N =
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

open Classical in
/-- Item `A/failure/prose/003` (`paper/sections/failure.tex:22-32`): the specified line
search. At a differentiable point $x$ with $g=\nabla F(x)$ and $p=-Hg$, the search
`NonStrictLineSearch.fromMetric F x H c₁ c₂ N` is the bracketing search started with
$\alpha_{\rm lo}=0$, $\alpha_{\rm hi}=+\infty$ (`none`) and $\alpha=1$; one step with lower
bracket `lo`, upper bracket `hi` and trial `α` tests Armijo first and weak Wolfe second,
accepts if both hold, sets $\alpha_{\rm hi}=\alpha$ and tries $(\alpha_{\rm lo}+\alpha)/2$
after an Armijo rejection, and sets $\alpha_{\rm lo}=\alpha$ and tries
$(\alpha+\alpha_{\rm hi})/2$, or $2\alpha$ while $\alpha_{\rm hi}=\infty$, after a Wolfe
rejection. The output is the accepted length and the list of all trial lengths; the budget
`N` only bounds the number of trials (`fromMetric_fuel_mono`). -/
theorem specified_search {n : ℕ} (F : Vec n → ℝ) (x : Vec n) (H : Mat n) (c₁ c₂ : ℝ)
    (g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x) (p : Vec n) (hp : p = -(H *ᵥ g)) :
    (∀ N, NonStrictLineSearch.fromMetric F x H c₁ c₂ N =
      NonStrictLineSearch.search F x p g c₁ c₂ N 0 none 1) ∧
    ∀ (N : ℕ) (lo : ℝ) (hi : Option ℝ) (α : ℝ),
      NonStrictLineSearch.search F x p g c₁ c₂ (N + 1) lo hi α =
        if NonStrictLineSearch.Armijo F x p g c₁ α then
          if NonStrictLineSearch.Wolfe F x p g c₂ α then (some α, [α])
          else ((NonStrictLineSearch.search F x p g c₁ c₂ N α hi
              (match hi with | none => 2 * α | some u => (α + u) / 2)).1,
            α :: (NonStrictLineSearch.search F x p g c₁ c₂ N α hi
              (match hi with | none => 2 * α | some u => (α + u) / 2)).2)
        else ((NonStrictLineSearch.search F x p g c₁ c₂ N lo (some α) ((lo + α) / 2)).1,
          α :: (NonStrictLineSearch.search F x p g c₁ c₂ N lo (some α) ((lo + α) / 2)).2) := by
  have hstep : bfgsStep H g 1 = p := by simp [hp, bfgsStep]
  refine ⟨fun N => ?_, fun N lo hi α => ?_⟩
  · unfold NonStrictLineSearch.fromMetric
    rw [DeterministicLineSearch.actual_coordinateGradient hg, hstep]
  · rw [NonStrictLineSearch.search]
    rfl

/-- Item `A/failure/disp/001` (`paper/sections/failure.tex:26-29`), equation
`art:failure_tests`: the two tests of the search,
\[ F(x+\alpha p)\le F(x)+c_1\alpha g^Tp,\qquad \nabla F(x+\alpha p)^Tp\ge c_2g^Tp. \]
`NonStrictLineSearch.Armijo` is literally the first inequality. `NonStrictLineSearch.Wolfe`
uses `coordinateGradient F (x + α • p)`, which is $\nabla F(x+\alpha p)$ at a differentiable
trial point (here `hg'`). -/
theorem failure_tests {n : ℕ} (F : Vec n → ℝ) (x p g : Vec n) (c₁ c₂ α : ℝ) (g' : Vec n)
    (hg' : HasFDerivAt F (gradientFunctional g') (x + α • p)) :
    (NonStrictLineSearch.Armijo F x p g c₁ α ↔ F (x + α • p) ≤ F x + c₁ * α * dot g p) ∧
    (NonStrictLineSearch.Wolfe F x p g c₂ α ↔ dot g' p ≥ c₂ * dot g p) := by
  refine ⟨Iff.rfl, ?_⟩
  unfold NonStrictLineSearch.Wolfe
  rw [DeterministicLineSearch.actual_coordinateGradient hg']

/-- Item `A/failure/prose/005` (`paper/sections/failure.tex:34-35`): "All comparisons in the
construction are strict, so strict acceptance tests give the same decisions." The sentence
describes the implementation used by both Theorem `art:local-failure` and Theorem
`art:local-failure-lower`; this theorem covers the first construction and
`strict_tests_same_decisions_lower` the constructions with positive lower curvature. For every
$0<c_1\le1/3$, $c_1<c_2<1$, at every iterate of the three runs of the first construction (the
seed run on $G$, the run on $\overline G$ of Corollary `art:failure_polyhedral`, and the $\ell$th
run of Theorem `art:local-failure`, $\ell\ge1$), the specified search with the non-strict tests
(`NonStrictLineSearch`) and the search with the strict tests $F(x+\alpha p)<F(x)+c_1\alpha
g^Tp$, $\nabla F(x+\alpha p)^Tp>c_2g^Tp$ (`DeterministicLineSearch`) return the same accepted
length and the same trial list. -/
theorem strict_tests_same_decisions (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    (∀ k, NonStrictLineSearch.fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k)
        c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric (objective seedC seedD) (orbitPoint k) (orbitMetric k)
        c₁ c₂ 5) ∧
    (∀ k, NonStrictLineSearch.fromMetric coerciveObjective (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric coerciveObjective (orbitPoint k) (orbitMetric k)
        c₁ c₂ 5) ∧
    (∀ ℓ (hℓ : 1 ≤ ℓ) k,
      NonStrictLineSearch.fromMetric DEmbedding.objective
          ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k)
          ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric DEmbedding.objective
          ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k)
          ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5) := by
  obtain ⟨h1, h2, h3⟩ := DLiteralTargets.nonStrictRun c₁ c₂ hc₁ hc₁' hc hc₂
  exact ⟨fun k => (h1 k).2, fun k => (h2 k).2, fun ℓ hℓ k => (h3 ℓ hℓ k).2⟩

/-- Item `A/failure/prose/005` (`paper/sections/failure.tex:34-35`), for the constructions with
positive lower curvature (Theorem `art:local-failure-lower` and Proposition
`art:quadratic_failure`, which use the same implementation): "All comparisons in the
construction are strict, so strict acceptance tests give the same decisions." For every
$0<c_1\le1/3$, $c_1<c_2<1$:
(1) the runs of Theorem `art:local-failure-lower`, on the objective of
Appendix `art:lower_curvature` (`LUniform.smoothObjective`), with iterates `x ℓ` and matrices
`H ℓ` chosen before the pair ($H_0=I$, $x_0^{(\ell)}\to0$) and converging to the centers
`LUniform.failureCenter ℓ`, and
(2) for every $\mu>0$ and every neighborhood $U$ of $0$, the perturbed bad orbit on
$Q_\mu$ (`LQuadraticSeed.objective μ`) of Proposition `art:quadratic_failure`, chosen before
the pair inside $U$ and converging to the wrong corner $0$,
are runs of the specified search, and at every iterate the search with the non-strict tests
(`NonStrictLineSearch`) and the search with the strict tests (`DeterministicLineSearch`)
return the same accepted length and the same trial list. -/
theorem strict_tests_same_decisions_lower :
    (∃ x : ℕ → ℕ → Vec 2, ∃ H : ℕ → ℕ → Mat 2,
      (∀ ℓ, H ℓ 0 = 1) ∧ Tendsto (fun ℓ => x ℓ 0) atTop (𝓝 0) ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
        ∃ R : ℕ → AdmissibleBFGSRun 2 LUniform.smoothObjective, ∀ ℓ,
          (R ℓ).c₁ = c₁ ∧ (R ℓ).c₂ = c₂ ∧ (R ℓ).x = x ℓ ∧ (R ℓ).H = H ℓ ∧
          Tendsto (R ℓ).x atTop (𝓝 (LUniform.failureCenter ℓ)) ∧
          ∀ k, NonStrictLineSearch.fromMetric LUniform.smoothObjective ((R ℓ).x k) ((R ℓ).H k)
              c₁ c₂ 5 = (some ((R ℓ).α k), trialHistory (phase k)) ∧
            DeterministicLineSearch.fromMetric LUniform.smoothObjective ((R ℓ).x k) ((R ℓ).H k)
              c₁ c₂ 5 = (some ((R ℓ).α k), trialHistory (phase k))) ∧
    (∀ μ : ℝ, 0 < μ → ∀ U ∈ 𝓝 (0 : Vec 2), ∃ x : ℕ → Vec 2, ∃ H : ℕ → Mat 2, (H 0).PosDef ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
        ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
          R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x = x ∧ R.H = H ∧ (∀ k, R.x k ∈ U) ∧
          Tendsto R.x atTop (𝓝 0) ∧
          ∀ k, NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k)
              c₁ c₂ 5 = (some (R.α k), trialHistory (phase k)) ∧
            DeterministicLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k)
              c₁ c₂ 5 = (some (R.α k), trialHistory (phase k))) := by
  refine ⟨?_, fun μ hμ U hU => ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, ⟨x, H, g, hH0, hx0, hruns⟩, -⟩ := LUniform.uniformSmoothLocalFailure
    refine ⟨x, H, hH0, hx0, fun c₁ c₂ hc₁ hc₁' hc hc₂ => ?_⟩
    obtain ⟨R, hR, -⟩ := hruns c₁ c₂ hc₁ hc₁' hc hc₂
    refine ⟨R, fun ℓ => ?_⟩
    obtain ⟨hx, hH, -, h1, h2, hlim, -, -, -, -, hstep, -, -⟩ := hR ℓ
    exact ⟨h1, h2, hx, hH, hlim, fun k => ⟨(hstep k).2.2.2.1, (hstep k).2.2.2.2.1⟩⟩
  · obtain ⟨x, H, hH0, hruns⟩ := LUniform.uniform_global_failure hμ U hU
    refine ⟨x, H, hH0, fun c₁ c₂ hc₁ hc₁' hc hc₂ => ?_⟩
    obtain ⟨R, hx, hH, h1, h2, hlim, -, -, -, -, -, hns, hs, hU', -⟩ := hruns c₁ c₂ hc₁ hc₁' hc hc₂
    exact ⟨R, h1, h2, hx, hH, hU', hlim, fun k => ⟨hns k, hs k⟩⟩

/-- The full inverse update $\mathcal B(H,g,g^+,\alpha)$ of equation `art:failure_update`. -/
def fullUpdate {n : ℕ} (H : Mat n) (g gplus : Vec n) (α : ℝ) : Mat n :=
  inverseBFGS H (bfgsStep H g α) (gplus - g)

/-- Item `A/failure/disp/002` (`paper/sections/failure.tex:38-43`), equation
`art:failure_update`:
\[ \mathcal B(H,g,g^+,\alpha)=\Bigl(I-\frac{sy^T}{y^Ts}\Bigr)H\Bigl(I-\frac{ys^T}{y^Ts}\Bigr)
   +\frac{ss^T}{y^Ts},\quad s=-\alpha Hg,\quad y=g^+-g. \]
`fullUpdate` unfolds to this formula; in dimension two it is the library's
`SeedCycle.update`. -/
theorem failure_update {n : ℕ} (H : Mat n) (g gplus : Vec n) (α : ℝ) (s y : Vec n)
    (hs : s = -α • (H *ᵥ g)) (hy : y = gplus - g) :
    fullUpdate H g gplus α =
      (1 - (dot y s)⁻¹ • outer s y) * H * (1 - (dot y s)⁻¹ • outer y s) + (dot y s)⁻¹ • outer s s := by
  subst hs hy
  rfl

/-- In dimension two, `fullUpdate` is the library's `SeedCycle.update`. -/
theorem fullUpdate_eq_update (H : Mat 2) (g gplus : Vec 2) (α : ℝ) :
    fullUpdate H g gplus α = SeedCycle.update H g gplus α := rfl

/-- Item `A/failure/prose/006` (`paper/sections/failure.tex:44`): "No resetting or
rescaling of the stored matrix is performed." In every run (`AdmissibleBFGSRun`) the next
matrix is the full update of the current one: $H_{k+1}=\mathcal B(H_k,g_k,g_{k+1},\alpha_k)$
for every $k$. -/
theorem run_update_full {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.H (k + 1) = fullUpdate (R.H k) (R.g k) (R.g (k + 1)) (R.α k) :=
  R.update k

/-- Every length in the trial list of phase `j` is the length of a row of
Table `art:trial_table` of that phase. -/
theorem mem_trialHistory {j : Fin 3} {a : ℝ} (ha : a ∈ trialHistory j) :
    ∃ q : Fin 9, trialPhase q = j ∧ trialLength q = a := by
  fin_cases j
  · have h : a ∈ [(1 : ℝ)] := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨0, rfl, h ▸ rfl⟩
  · have h : a ∈ [(1 : ℝ), 1/2, 1/4] := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨2, rfl, rfl⟩
    · exact ⟨3, rfl, rfl⟩
  · have h : a ∈ [(1 : ℝ), 1/2, 1/4, 1/8, 1/16] := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨4, rfl, rfl⟩
    · exact ⟨5, rfl, rfl⟩
    · exact ⟨6, rfl, rfl⟩
    · exact ⟨7, rfl, rfl⟩
    · exact ⟨8, rfl, rfl⟩

/-! ### The seed objects -/

/-- The steps $s_0,s_1,s_2$ of equation `art:seed_steps`. -/
def seedStep : Fin 3 → Vec 2 :=
  ![![-1, 0], ![127/1024, 1/64], seedRatio • ![1 - seedC, -seedD]]

/-- The point $z_0$ of equation `art:seed_points`. -/
def seedStart : Vec 2 :=
  (1 / (1 - seedRatio)) • ![897/1024 - seedRatio * (1 - seedC), seedRatio * seedD - 1/64]

/-- The points $z_0,\dots,z_3$ of equation `art:seed_points`: $z_{j+1}=z_j+s_j$. -/
def seedPoint : Fin 4 → Vec 2 :=
  ![seedStart, seedStart + seedStep 0, seedStart + seedStep 0 + seedStep 1,
    seedStart + seedStep 0 + seedStep 1 + seedStep 2]

/-- The directions $p_j=-M_jg_j$ of Lemma `art:seed_cycle`. -/
def seedDir (j : Fin 3) : Vec 2 := -(metric seedC seedD j *ᵥ SeedOrbit.gradient seedC seedD j)

/-- $g_0,g_1,g_2,g_3$ with $g_3=g_0$ (display `art:seed_margins`). -/
def seedSlope : Fin 4 → Vec 2 := ![g0, g1, g2 seedC seedD, g0]

/-- $\rho<1$. -/
theorem ratio_lt_one : seedRatio < 1 := source_ratio_pos_lt_one.2

/-- $1-\rho\ne0$. -/
theorem one_sub_ratio_ne : 1 - seedRatio ≠ 0 := by
  have := ratio_lt_one
  linarith

/-- $z_0$ is the library's `SeedOrbit.point seedC seedD seedRatio 0`. -/
theorem seedStart_eq : seedStart = point seedC seedD seedRatio 0 := by
  have h := one_sub_ratio_ne
  ext i
  fin_cases i <;> simp [seedStart, point, initialPoint] <;> field_simp <;> left <;> ring

/-- $z_0,z_1,z_2$ are the library's `SeedOrbit.point seedC seedD seedRatio j`. -/
theorem seedPoint_castSucc (j : Fin 3) : seedPoint j.castSucc = point seedC seedD seedRatio j := by
  have h := seedStart_eq
  fin_cases j
  · exact h
  · change seedStart + seedStep 0 = point seedC seedD seedRatio 1
    rw [h]
    rfl
  · change seedStart + seedStep 0 + seedStep 1 = point seedC seedD seedRatio 2
    rw [h]
    ext i
    fin_cases i
    · simp [seedStep, point]
      ring
    · simp [seedStep, point]

/-- The displayed steps are the BFGS steps $s_j=-\alpha_jM_jg_j$. -/
theorem seedStep_eq (j : Fin 3) :
    seedStep j = bfgsStep (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) (length j) := by
  rw [source_direction]
  fin_cases j <;> ext i <;> fin_cases i <;> simp [seedStep, direction, length] <;> ring

/-- $p_j=-M_jg_j$ is the library's `SeedOrbit.direction`. -/
theorem seedDir_eq (j : Fin 3) : seedDir j = direction seedC seedD seedRatio j := by
  have h := source_direction j 1
  rw [one_smul] at h
  rw [← h, seedDir, bfgsStep, neg_smul, one_smul]

/-- $z_{j+1}=z_j+\alpha_jp_j$ is the accepted trial point of phase $j$. -/
theorem seedPoint_succ (j : Fin 3) :
    seedPoint j.succ = trial seedC seedD seedRatio j (length j) := by
  rw [trial, ← seedPoint_castSucc, ← source_direction, ← seedStep_eq]
  fin_cases j <;> rfl

/-- $g_{j+1}$ (with $g_3=g_0$) is the gradient of the next phase. -/
theorem seedSlope_succ (j : Fin 3) : seedSlope j.succ = SeedOrbit.gradient seedC seedD (nextPhase j) := by
  fin_cases j <;> rfl

/-- $g_j$ for $j=0,1,2$. -/
theorem seedSlope_castSucc (j : Fin 3) : seedSlope j.castSucc = SeedOrbit.gradient seedC seedD j := by
  fin_cases j <;> rfl

/-- Item `A/failure/disp/003` (`paper/sections/failure.tex:74-77`): the definitions
\[ g_0=(1,0)^T,\quad g_1=(-1,-1/8)^T,\quad g_2=(c_\circ,d_\circ)^T,\quad
   G(z)=\max_{0\le i\le2}g_i^Tz, \]
with $(c_\circ,d_\circ)=$ (`seedC`, `seedD`) $=$ (`root 0`, `root 1`), the root of
Lemma `art:root_certificate`. The library's `SeedOrbit.gradient seedC seedD i` is $g_i$ and
`SeedOrbit.objective seedC seedD` is $G$. -/
theorem seed_slopes :
    g0 = ![1, 0] ∧ g1 = ![-1, -1/8] ∧ g2 seedC seedD = ![seedC, seedD] ∧
    seedC = AlgebraicSeed.root 0 ∧ seedD = AlgebraicSeed.root 1 ∧
    SeedOrbit.gradient seedC seedD = ![g0, g1, g2 seedC seedD] ∧
    ∀ z : Vec 2, objective seedC seedD z =
      max (max (dot g0 z) (dot g1 z)) (dot (g2 seedC seedD) z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun z => ?_⟩
  apply le_antisymm
  · unfold objective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro i _
    fin_cases i <;> simp [MaxAffine.Family.branch, family, SeedOrbit.gradient]
  · have h : ∀ i, dot (SeedOrbit.gradient seedC seedD i) z ≤ objective seedC seedD z :=
      fun i => by simpa [MaxAffine.Family.branch, family] using (family seedC seedD).branch_le i z
    exact max_le (max_le (h 0) (h 1)) (h 2)

/-- Item `A/failure/prose/014` (`paper/sections/failure.tex:78-79`): "The useful coarse
bounds are $0.318<c_\circ<0.319$ and $-1.026<d_\circ<-1.025$." -/
theorem seed_coarse_bounds :
    (0.318 : ℝ) < seedC ∧ seedC < 0.319 ∧ (-1.026 : ℝ) < seedD ∧ seedD < -1.025 := by
  obtain ⟨h1, h2, h3, h4⟩ := AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1
  norm_num
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Item `A/failure/disp/004` (`paper/sections/failure.tex:80-83`), equation `art:seed_rho`:
\[ \rho=\frac{129(c_\circ-8d_\circ)}{(16c_\circ-127d_\circ-16)(127c_\circ+16d_\circ+129)},
   \qquad 0.060<\rho<0.061. \]
The library's `seedRatio` is $\rho$ (the first conjunct is its defining formula). -/
theorem seed_rho :
    seedRatio = 129 * (seedC - 8 * seedD) /
      ((16 * seedC - 127 * seedD - 16) * (127 * seedC + 16 * seedD + 129)) ∧
    (0.060 : ℝ) < seedRatio ∧ seedRatio < 0.061 := by
  obtain ⟨-, -, -, -, -, -, -, h1, h2⟩ := AlgebraicSeed.box_denominators_and_ratio
    AlgebraicSeed.root_spec.1
  refine ⟨rfl, ?_⟩
  norm_num
  exact ⟨by linarith, by linarith⟩

/-- Item `A/failure/disp/005` (`paper/sections/failure.tex:85-91`), equations
`art:seed_matrices` and `art:seed_steps`:
\[ M_0=I,\quad M_1=\begin{pmatrix}129/256&-1/16\\-1/16&1\end{pmatrix},\quad
   M_2=\mathcal B(M_1,g_1,g_2,1/4),\qquad
   s_0=(-1,0)^T,\quad s_1=(127/1024,1/64)^T,\quad s_2=\rho(1-c_\circ,-d_\circ)^T. \]
The library's `SeedOrbit.metric seedC seedD j` is $M_j$; `seedStep` is literally
$(s_0,s_1,s_2)$. The last conjunct (not part of the display) identifies the displayed steps
with the BFGS steps $s_j=-\alpha_jM_jg_j$, $\alpha=(1,1/4,1/16)$ (`SeedOrbit.length`). -/
theorem seed_matrices_steps :
    metric seedC seedD 0 = 1 ∧ metric seedC seedD 1 = !![129/256, -1/16; -1/16, 1] ∧
    metric seedC seedD 2 = fullUpdate (metric seedC seedD 1) g1 (g2 seedC seedD) (1/4) ∧
    seedStep 0 = ![-1, 0] ∧ seedStep 1 = ![127/1024, 1/64] ∧
    seedStep 2 = seedRatio • ![1 - seedC, -seedD] ∧
    length = ![1, 1/4, 1/16] ∧
    ∀ j, seedStep j = -length j • (metric seedC seedD j *ᵥ SeedOrbit.gradient seedC seedD j) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun j => seedStep_eq j⟩

/-- Item `A/failure/disp/006` (`paper/sections/failure.tex:94-98`), equation
`art:seed_points`:
\[ z_0=\frac1{1-\rho}\begin{pmatrix}897/1024-\rho(1-c_\circ)\\ \rho d_\circ-1/64\end{pmatrix},
   \qquad z_{j+1}=z_j+s_j\quad(j=0,1,2). \]
`seedPoint` is literally $(z_0,z_1,z_2,z_3)$; the last conjunct identifies $z_0,z_1,z_2$ with
the library's `SeedOrbit.point`. -/
theorem seed_points :
    seedPoint 0 = (1 / (1 - seedRatio)) •
      ![897/1024 - seedRatio * (1 - seedC), seedRatio * seedD - 1/64] ∧
    (∀ j : Fin 3, seedPoint j.succ = seedPoint j.castSucc + seedStep j) ∧
    ∀ j : Fin 3, seedPoint j.castSucc = point seedC seedD seedRatio j := by
  refine ⟨rfl, fun j => ?_, seedPoint_castSucc⟩
  fin_cases j <;> rfl

/-- Item `A/failure/prose/015` (`paper/sections/failure.tex:92-93`): "The point is then
determined by the displacement closure $s_0+s_1+s_2=-(1-\rho)z_0$." -/
theorem displacement_closure :
    seedStep 0 + seedStep 1 + seedStep 2 = -(1 - seedRatio) • seedPoint 0 := by
  have h := one_sub_ratio_ne
  ext i
  fin_cases i <;> simp [seedStep, seedPoint, seedStart] <;> field_simp <;> ring

/-! ### Lemma `art:seed_cycle` -/

theorem phase_val (j : Fin 3) : phase j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)

/-- Item `A/failure/prose/022` (`paper/sections/failure.tex:160-162`): "Thus the displayed
lengths are outputs of the specified search for the entire parameter range in
Theorem `art:local-failure`; no accepted-length sequence is assumed." The specified search
from $(z_j,M_j)$ on $G$ returns the accepted length $\alpha_j$ and the trial list of phase
$j$ for every $0<c_1\le1/3$ and $c_2>0$, which contains the range $0<c_1\le1/3$,
$c_1<c_2<1$ of the theorem. -/
theorem seed_search {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (j : Fin 3) :
    NonStrictLineSearch.fromMetric (objective seedC seedD) (seedPoint j.castSucc)
      (metric seedC seedD j) c₁ c₂ 5 = (some (length j), trialHistory j) := by
  have h := DNonStrictObjectives.seed_fromMetric hc₁ hc₁' hc₂ j.val
  obtain ⟨hx, hH, -, hα⟩ := orbit_phase_parameters 0 j
  simp only [mul_zero, zero_add, pow_zero, one_smul] at hx hH hα
  rw [hx, hH, hα, phase_val] at h
  rw [seedPoint_castSucc]
  exact h

/-- $G(z_j)=g_j^Tz_j$. -/
theorem seed_base_active (j : Fin 3) :
    objective seedC seedD (seedPoint j.castSucc) =
      dot (SeedOrbit.gradient seedC seedD j) (seedPoint j.castSucc) := by
  rw [seedPoint_castSucc]
  exact objective_of_active (source_base_certificate j).active

/-- The base query $z_j+\alpha p_j$ of row `q` is the library's `SeedOrbit.trial`. -/
theorem seed_query_eq (q : Fin 9) :
    seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q) =
      trial seedC seedD seedRatio (trialPhase q) (trialLength q) := by
  rw [seedPoint_castSucc, seedDir_eq]
  rfl

/-- $G$ at the base query of row `q` is the value of its active branch. -/
theorem seed_query_active (q : Fin 9) :
    objective seedC seedD (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) =
      dot (SeedOrbit.gradient seedC seedD (trialActive q))
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) := by
  rw [seed_query_eq]
  exact objective_of_active (source_trial_certificate q).active

/-- Item `A/failure/disp/007` (`paper/sections/failure.tex:102-105`), in Lemma
`art:seed_cycle`:
\[ \mathcal B(I,g_0,g_1,1)=M_1,\qquad \mathcal B(M_2,g_2,g_0,1/16)=\rho I,\qquad z_3=\rho z_0. \]
$\mathcal B$ is `fullUpdate` (equation `art:failure_update`), $M_j$ is `metric seedC seedD j`
and $z_j$ is `seedPoint j`. -/
theorem seed_closures :
    fullUpdate 1 g0 g1 1 = metric seedC seedD 1 ∧
    fullUpdate (metric seedC seedD 2) (g2 seedC seedD) g0 (1/16) = seedRatio • (1 : Mat 2) ∧
    seedPoint 3 = seedRatio • seedPoint 0 := by
  refine ⟨first_update, source_metric_two_update, ?_⟩
  have h := one_sub_ratio_ne
  ext i
  fin_cases i <;> simp [seedStep, seedPoint, seedStart] <;> field_simp <;> ring

/-- At every rejected row of Table `art:trial_table` the objective strictly exceeds its
current value, $G(z_j)<G(z_j+\alpha p_j)$ (Lemma `art:seed_cycle`: "At every rejection the
objective strictly exceeds its current value"). -/
theorem seed_rejections_raise (q : Fin 9) (hq : trialAccept q = false) :
    objective seedC seedD (seedPoint (trialPhase q).castSucc) <
      objective seedC seedD
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) := by
  have hd := (source_trial_certificate q).decision
  rw [hq] at hd
  simp only [Bool.false_eq_true, if_false] at hd
  rw [seed_base_active, seed_query_active, seed_query_eq, seedPoint_castSucc]
  exact hd

/-- Item `A/failure/disp/008` (`paper/sections/failure.tex:110-113`), equation
`art:seed_margins` of Lemma `art:seed_cycle`: at every acceptance, $j=0,1,2$,
\[ G(z_j)+\tfrac13g_j^Ts_j-G(z_{j+1})>0,\qquad g_{j+1}^Ts_j>0>g_j^Ts_j, \]
where $g_3=g_0$ ($g_j$ is `seedSlope j`, $s_j$ is `seedStep j`). -/
theorem seed_margins (j : Fin 3) :
    objective seedC seedD (seedPoint j.castSucc) + 1/3 * dot (seedSlope j.castSucc) (seedStep j) -
        objective seedC seedD (seedPoint j.succ) > 0 ∧
      dot (seedSlope j.succ) (seedStep j) > 0 ∧ 0 > dot (seedSlope j.castSucc) (seedStep j) := by
  have hc := source_accepted_certificate j
  have hd := hc.decision
  simp only [if_true] at hd
  have hw := hc.wolfe rfl
  have hn := hc.descent
  have hstep : seedStep j = length j • direction seedC seedD seedRatio j := by
    rw [seedStep_eq, source_direction]
  have hval : objective seedC seedD (seedPoint j.succ) =
      dot (SeedOrbit.gradient seedC seedD (nextPhase j)) (trial seedC seedD seedRatio j (length j)) := by
    rw [seedPoint_succ]
    exact objective_of_active hc.active
  rw [seed_base_active, hval, seedSlope_succ, seedSlope_castSucc, hstep, seedPoint_castSucc]
  refine ⟨?_, hw, hn⟩
  linarith

/-- Item `A/failure/disp/009` (`paper/sections/failure.tex:117-119`), equation
`art:seed_query_bounds` of Lemma `art:seed_cycle`: "All listed queries and the three starting
points have a unique active branch, and each such point $z$, with second coordinate $[z]_2$,
satisfies \[ |g_i^Tz|<3\quad(i=0,1,2),\qquad [z]_2<2,\qquad G(z)>0. \]"
The listed queries are the nine rows $z_j+\alpha p_j$ of Table `art:trial_table`
($p_j=-M_jg_j$ is `seedDir j`); $[z]_2$ is `z 1`. -/
theorem seed_query_bounds :
    ∀ z ∈ Set.range (fun j : Fin 3 => seedPoint j.castSucc) ∪
        Set.range (fun q : Fin 9 =>
          seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)),
      (∃ i : Fin 3, ∀ k, k ≠ i →
        dot (SeedOrbit.gradient seedC seedD k) z < dot (SeedOrbit.gradient seedC seedD i) z) ∧
      (∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) z| < 3) ∧ z 1 < 2 ∧
      0 < objective seedC seedD z := by
  rintro z (⟨j, rfl⟩ | ⟨q, rfl⟩) <;> dsimp only
  · have hc := source_base_certificate j
    rw [seed_base_active, seedPoint_castSucc]
    exact ⟨⟨j, hc.active⟩, hc.branch_bounds, hc.vertical, hc.value_pos⟩
  · have hc := (source_trial_certificate q).toPointCertificate
    rw [seed_query_active, seed_query_eq]
    exact ⟨⟨trialActive q, hc.active⟩, hc.branch_bounds, hc.vertical, hc.value_pos⟩

/-- Item `A/failure/lemma/art:seed_cycle` (`paper/sections/failure.tex:100-120`), Lemma
`art:seed_cycle` (Exact cycle and strict trial decisions), with the parameter range that the
correction M11 of 15 October 2026 added to its query-list sentence.

"The matrices in `art:seed_matrices` are positive definite, and
\[ \mathcal B(I,g_0,g_1,1)=M_1,\qquad \mathcal B(M_2,g_2,g_0,1/16)=\rho I,\qquad z_3=\rho z_0. \]
At $z_j$, $j=0,1,2$, the unique active gradient is $g_j$. With $p_j=-M_jg_j$, for every
$0<c_1\le1/3$ and $c_2>0$ the entire line-search query list is Table `art:trial_table`. At every
rejection the objective strictly exceeds its current value. At every acceptance,
\[ G(z_j)+\tfrac13g_j^Ts_j-G(z_{j+1})>0,\qquad g_{j+1}^Ts_j>0>g_j^Ts_j, \]
where $g_3=g_0$. All listed queries and the three starting points have a unique active
branch, and each such point $z$, with second coordinate $[z]_2$, satisfies
\[ |g_i^Tz|<3\quad(i=0,1,2),\qquad [z]_2<2,\qquad G(z)>0. \]"

The query list depends on the line-search constants, and before the correction the lemma fixed
none: the accepted trial $1/16$ of phase 2 passes Armijo only for $c_1\le r_2<0.37521$
(`accepted_armijo_iff`, `accepted_armijo_ratios`), and for $c_1=0.38$, $c_2=1/2$ the search from
$(z_2,M_2)$ does not return the table's phase-2 list (`seed_cycle_range_counterexample`). This
theorem is the lemma as printed (sixth conjunct: the specified search from $(z_j,M_j)$ makes
exactly the trials of phase $j$ of the table and accepts its last length).
$M_j$ is `metric seedC seedD j`, $z_j$ is `seedPoint j`, $s_j$ is `seedStep j`, $p_j$ is
`seedDir j` $=-M_jg_j$, $g_j$ (with $g_3=g_0$) is `seedSlope j`, $G$ is `objective seedC seedD`
and $[z]_2$ is `z 1`; the listed queries are $z_j+\alpha p_j$ for the nine rows $(j,\alpha)$ of
the table (`trialPhase`, `trialLength`). The displays are also stated on their own:
`seed_closures`, `seed_margins`, `seed_query_bounds`. -/
theorem seed_cycle :
    (∀ j : Fin 3, (metric seedC seedD j).PosDef) ∧
    fullUpdate 1 g0 g1 1 = metric seedC seedD 1 ∧
    fullUpdate (metric seedC seedD 2) (g2 seedC seedD) g0 (1/16) = seedRatio • (1 : Mat 2) ∧
    seedPoint 3 = seedRatio • seedPoint 0 ∧
    (∀ j : Fin 3, ∀ i, i ≠ j → dot (SeedOrbit.gradient seedC seedD i) (seedPoint j.castSucc) <
      dot (SeedOrbit.gradient seedC seedD j) (seedPoint j.castSucc)) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → 0 < c₂ →
      NonStrictLineSearch.fromMetric (objective seedC seedD) (seedPoint 0) (metric seedC seedD 0)
          c₁ c₂ 5 = (some 1, [1]) ∧
      NonStrictLineSearch.fromMetric (objective seedC seedD) (seedPoint 1) (metric seedC seedD 1)
          c₁ c₂ 5 = (some (1/4), [1, 1/2, 1/4]) ∧
      NonStrictLineSearch.fromMetric (objective seedC seedD) (seedPoint 2) (metric seedC seedD 2)
          c₁ c₂ 5 = (some (1/16), [1, 1/2, 1/4, 1/8, 1/16])) ∧
    (∀ q : Fin 9, trialAccept q = false →
      objective seedC seedD (seedPoint (trialPhase q).castSucc) <
        objective seedC seedD
          (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))) ∧
    (∀ j : Fin 3,
      objective seedC seedD (seedPoint j.castSucc) + 1/3 * dot (seedSlope j.castSucc) (seedStep j) -
          objective seedC seedD (seedPoint j.succ) > 0 ∧
        dot (seedSlope j.succ) (seedStep j) > 0 ∧ 0 > dot (seedSlope j.castSucc) (seedStep j)) ∧
    (∀ z ∈ Set.range (fun j : Fin 3 => seedPoint j.castSucc) ∪
        Set.range (fun q : Fin 9 =>
          seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)),
      (∃ i : Fin 3, ∀ k, k ≠ i →
        dot (SeedOrbit.gradient seedC seedD k) z < dot (SeedOrbit.gradient seedC seedD i) z) ∧
      (∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) z| < 3) ∧ z 1 < 2 ∧
      0 < objective seedC seedD z) := by
  obtain ⟨h1, h2, h3⟩ := seed_closures
  refine ⟨source_metric_posDef, h1, h2, h3, ?_, ?_, seed_rejections_raise, seed_margins,
    seed_query_bounds⟩
  · intro j
    rw [seedPoint_castSucc]
    exact (source_base_certificate j).active
  · intro c₁ c₂ hc₁ hc₁' hc₂
    exact ⟨seed_search hc₁ hc₁' hc₂ 0, seed_search hc₁ hc₁' hc₂ 1, seed_search hc₁ hc₁' hc₂ 2⟩

/-! ### Table `art:trial_table` -/

/-- Column "$10^4G$ current" of Table `art:trial_table`, lower ends: enclosures of
$10^4G(z_j)$. -/
def currentLower : Fin 3 → ℝ := ![8884, 1218, 723]
/-- Column "$10^4G$ current", upper ends. -/
def currentUpper : Fin 3 → ℝ := ![8885, 1219, 724]
/-- Column "$10^4G$ trial", lower ends: enclosures of $10^4G(z_j+\alpha p_j)$, row by row. -/
def trialLower : Fin 9 → ℝ := ![1218, 3845, 1364, 723, 6687, 3406, 1765, 944, 534]
/-- Column "$10^4G$ trial", upper ends. -/
def trialUpper : Fin 9 → ℝ := ![1219, 3846, 1365, 724, 6691, 3408, 1767, 946, 536]

/-- $p_j$ is the step of length one used by the library's display values. -/
theorem seedDir_eq_actualStep (j : Fin 3) : seedDir j = DDisplayActual.actualStep j 1 := by
  simp [seedDir, DDisplayActual.actualStep, bfgsStep]

/-- $G$ at the base query of row `q` is the library's certified display value. -/
theorem table_trial_value (q : Fin 9) :
    objective seedC seedD (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) =
      DDisplayActual.trialValue q := by
  rw [seedPoint_castSucc, seedDir_eq_actualStep]
  rfl

/-- A rational enclosure of a certified display value gives an enclosure of $10^4$ times it. -/
theorem display_enclosure (i : Fin 33) (lo hi : ℝ) (hlo : lo / 10^4 < DDisplayRaw.lower i)
    (hhi : DDisplayRaw.upper i < hi / 10^4) :
    lo < 10^4 * DDisplayActual.values i ∧ 10^4 * DDisplayActual.values i < hi := by
  have h := DDisplayPrecision.actual_bounds i
  have h1 := hlo.trans_le h.1
  have h2 := h.2.trans_lt hhi
  constructor <;> linarith

/-- The column "$10^4G$ current" of Table `art:trial_table`. -/
theorem table_current (j : Fin 3) :
    currentLower j < 10^4 * objective seedC seedD (seedPoint j.castSucc) ∧
      10^4 * objective seedC seedD (seedPoint j.castSucc) < currentUpper j := by
  rw [seedPoint_castSucc]
  fin_cases j
  · exact display_enclosure 18 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [currentLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [currentUpper])
  · exact display_enclosure 19 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [currentLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [currentUpper])
  · exact display_enclosure 20 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [currentLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [currentUpper])

/-- The column "$10^4G$ trial" of Table `art:trial_table`. -/
theorem table_trial (q : Fin 9) :
    trialLower q < 10^4 * objective seedC seedD
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) ∧
      10^4 * objective seedC seedD
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) < trialUpper q := by
  rw [table_trial_value]
  fin_cases q
  · exact display_enclosure 9 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 10 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 11 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 12 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 13 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 14 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 15 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 16 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])
  · exact display_enclosure 17 _ _ (by simp only [DDisplayRaw.lower, Matrix.cons_val]; norm_num [trialLower])
      (by simp only [DDisplayRaw.upper, Matrix.cons_val]; norm_num [trialUpper])

/-- At a rejected row of Table `art:trial_table` the non-strict Armijo test fails for every
$c_1>0$. -/
theorem table_reject {c₁ : ℝ} (hc₁ : 0 < c₁) (q : Fin 9) (hq : trialAccept q = false) :
    ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
      (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q) := by
  rw [seedPoint_castSucc, seedDir_eq]
  have hc := source_trial_certificate q
  rw [hq] at hc
  have hr := hc.actual_reject (source_base_certificate (trialPhase q)).active hc₁
  rw [dot_smul_right, ← mul_assoc] at hr
  exact not_le.mpr hr

/-- The decisions of the specified search at the nine rows of Table `art:trial_table`, for
every $0<c_1\le1/3$ and $c_2>0$: both tests hold at an accepted row, Armijo fails at a
rejected row. -/
theorem table_decision {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (q : Fin 9) :
    (trialAccept q = true →
      NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
        (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ∧
      NonStrictLineSearch.Wolfe (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
        (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₂ (trialLength q)) ∧
    (trialAccept q = false →
      ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
        (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q)) := by
  refine ⟨fun hq => ?_, fun hq => table_reject hc₁ q hq⟩
  rw [seedPoint_castSucc, seedDir_eq]
  obtain ⟨ha, hw⟩ := source_scaled_accept one_pos hc₁ hc₁' hc₂ q hq
  simp only [one_smul] at ha hw
  exact ⟨le_of_lt ha, le_of_lt hw⟩

/-- Item `A/failure/table/art:trial_table` (`paper/sections/failure.tex:122-151`), Table
`art:trial_table`, with the parameter range that the correction M11 of 15 October 2026 added to
its caption (the Decision column, "the deterministic trial tree", holds for $0<c_1\le1/3$,
$c_2>0$, but the row $(2,1/16)$ is rejected for $c_1=0.38$, `seed_cycle_range_counterexample`);
and the caption claim Item `A/failure/prose/018` (`paper/sections/failure.tex:149`): "All displayed
intervals are rational enclosures, not rounded values."

Columns "Phase $j$", "Trial $\alpha$", "Active branch" and "Decision" are the library's
`trialPhase`, `trialLength`, `trialActive` and `trialAccept` (first four conjuncts, literally
the table). "Current" is $G(z_j)$ and "trial" is $G(z_j+\alpha p_j)$, $p_j=-M_jg_j$
(`seedDir`); the displayed open intervals `currentLower`/`currentUpper` and
`trialLower`/`trialUpper` enclose $10^4G$ (fifth and sixth conjuncts, rational enclosures
proved from the certified values). The active branch of each trial point is strict. These
cells hold as printed. The decisions are those of the specified search for every
$0<c_1\le1/3$ and $c_2>0$ (the caption's sentence): Armijo and weak Wolfe hold at the
accepted rows, Armijo fails at the rejected rows; and the search from $(z_j,M_j)$ makes
exactly the trials of the phase-$j$ rows, in order, and accepts the last. -/
theorem trial_table :
    trialPhase = ![0, 1, 1, 1, 2, 2, 2, 2, 2] ∧
    trialLength = ![1, 1, 1/2, 1/4, 1, 1/2, 1/4, 1/8, 1/16] ∧
    trialActive = ![1, 0, 0, 2, 0, 0, 0, 0, 0] ∧
    trialAccept = ![true, false, false, true, false, false, false, false, true] ∧
    (∀ j : Fin 3, currentLower j < 10^4 * objective seedC seedD (seedPoint j.castSucc) ∧
      10^4 * objective seedC seedD (seedPoint j.castSucc) < currentUpper j) ∧
    (∀ q : Fin 9,
      trialLower q < 10^4 * objective seedC seedD
          (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) ∧
      10^4 * objective seedC seedD
          (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) < trialUpper q ∧
      ∀ k, k ≠ trialActive q →
        dot (SeedOrbit.gradient seedC seedD k)
            (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) <
          dot (SeedOrbit.gradient seedC seedD (trialActive q))
            (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → 0 < c₂ → ∀ q : Fin 9,
      (trialAccept q = true →
        NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
          (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ∧
        NonStrictLineSearch.Wolfe (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
          (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₂ (trialLength q)) ∧
      (trialAccept q = false →
        ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
          (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q))) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → 0 < c₂ → ∀ j : Fin 3,
      NonStrictLineSearch.fromMetric (objective seedC seedD) (seedPoint j.castSucc)
        (metric seedC seedD j) c₁ c₂ 5 = (some (length j), trialHistory j)) ∧
    trialHistory = ![[trialLength 0], [trialLength 1, trialLength 2, trialLength 3],
      [trialLength 4, trialLength 5, trialLength 6, trialLength 7, trialLength 8]] := by
  refine ⟨rfl, rfl, rfl, rfl, table_current, fun q => ⟨(table_trial q).1, (table_trial q).2, ?_⟩,
    fun c₁ c₂ hc₁ hc₁' hc₂ q => table_decision hc₁ hc₁' hc₂ q,
    fun c₁ c₂ hc₁ hc₁' hc₂ j => seed_search hc₁ hc₁' hc₂ j, ?_⟩
  · rw [seed_query_eq]
    exact (source_trial_certificate q).active
  · funext j
    fin_cases j <;> rfl

/-- Item `A/failure/prose/020` (`paper/sections/failure.tex:155-157`), and the caption claim
Item `A/failure/prose/016` (`paper/sections/failure.tex:145-146`) of Table `art:trial_table`
("Every rejected trial raises the objective and therefore fails Armijo"):
"Every rejected candidate has a value larger than the current value, so it fails Armijo
for every $c_1>0$." -/
theorem rejected_raise_value (q : Fin 9) (hq : trialAccept q = false) :
    objective seedC seedD (seedPoint (trialPhase q).castSucc) <
      objective seedC seedD (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) ∧
    ∀ c₁ : ℝ, 0 < c₁ →
      ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
        (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q) := by
  exact ⟨seed_rejections_raise q hq, fun c₁ hc₁ => table_reject hc₁ q hq⟩

/-- Item `A/failure/prose/021` (`paper/sections/failure.tex:157-160`): "At each accepted
candidate the decrease exceeds one third of the predicted decrease, while the new
directional derivative is positive and the old one is negative. Hence Armijo holds for
$c_1\le1/3$ and weak Wolfe holds for every $c_2>0$." The first sentence restates
display `art:seed_margins` (`seed_margins`); the conclusion: -/
theorem accepted_pass_tests (q : Fin 9) (hq : trialAccept q = true) :
    (∀ c₁ : ℝ, c₁ ≤ 1/3 →
      NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
        (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₁ (trialLength q)) ∧
    (∀ c₂ : ℝ, 0 < c₂ →
      NonStrictLineSearch.Wolfe (objective seedC seedD) (seedPoint (trialPhase q).castSucc)
        (seedDir (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) c₂ (trialLength q)) := by
  have hc := source_trial_certificate q
  rw [hq] at hc
  have hd := hc.decision
  simp only [if_true] at hd
  have hw := hc.wolfe rfl
  have hn := hc.descent
  have hα := source_trial_length_pos q
  rw [seedPoint_castSucc, seedDir_eq]
  rw [dot_smul_right] at hd hw hn
  have hbase := objective_of_active (source_base_certificate (trialPhase q)).active
  have htrial := objective_of_active hc.active
  have hgrad := DeterministicLineSearch.actual_coordinateGradient (hasGradient_of_active hc.active)
  refine ⟨fun c₁ hc₁ => ?_, fun c₂ hc₂ => ?_⟩
  · unfold NonStrictLineSearch.Armijo
    change objective seedC seedD (trial seedC seedD seedRatio (trialPhase q) (trialLength q)) ≤ _
    rw [htrial, hbase]
    nlinarith
  · unfold NonStrictLineSearch.Wolfe
    change _ ≤ dot (coordinateGradient (objective seedC seedD)
      (trial seedC seedD seedRatio (trialPhase q) (trialLength q))) _
    rw [hgrad]
    have h1 : 0 < dot (SeedOrbit.gradient seedC seedD (trialActive q))
        (direction seedC seedD seedRatio (trialPhase q)) := by
      by_contra h
      push_neg at h
      nlinarith
    have h2 : dot (SeedOrbit.gradient seedC seedD (trialPhase q))
        (direction seedC seedD seedRatio (trialPhase q)) < 0 := by
      by_contra h
      push_neg at h
      nlinarith
    nlinarith

/-- Item `A/failure/prose/023` (`paper/sections/failure.tex:163`): "The routine never needs
a Wolfe rejection on this example." For every $0<c_1\le1/3$, $c_1<c_2<1$, at every trial of
every line search of the seed run (`orbitPoint`, `orbitMetric`; Lemma `art:seed_cycle` and
equation `art:cone_orbit`), Armijo implies weak Wolfe, so a Wolfe rejection (Armijo holds,
Wolfe fails) never occurs. -/
theorem no_wolfe_rejection {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂)
    (_hc₂ : c₂ < 1) (k : ℕ) (q : Fin 9) (hq : trialPhase q = phase k) :
    NonStrictLineSearch.Armijo (objective seedC seedD) (orbitPoint k)
        (bfgsStep (orbitMetric k) (orbitGradient k) 1) (orbitGradient k) c₁ (trialLength q) →
      NonStrictLineSearch.Wolfe (objective seedC seedD) (orbitPoint k)
        (bfgsStep (orbitMetric k) (orbitGradient k) 1) (orbitGradient k) c₂ (trialLength q) := by
  intro hA
  cases hacc : trialAccept q with
  | true =>
    have h := (SeedEmbedding.NonStrict.trial_accept DNonStrictObjectives.seedOracleData one_pos hc₁
      hc₁' (hc₁.trans hc) k q hq hacc).2
    simpa only [SeedEmbedding.point, SeedEmbedding.gradient, one_smul, zero_add] using h
  | false =>
    have h := SeedEmbedding.NonStrict.trial_reject DNonStrictObjectives.seedOracleData one_pos hc₁
      k q hq hacc
    simp only [SeedEmbedding.point, SeedEmbedding.gradient, one_smul, zero_add] at h
    exact absurd hA h

/-! ### The parameter range of Lemma `art:seed_cycle` and Table `art:trial_table` -/

/-- The Armijo ratio of phase $j$ is the library's certified display value
`DDisplayActual.armijoRatio j`. -/
theorem accepted_armijo_ratio_eq (j : Fin 3) :
    (objective seedC seedD (seedPoint j.castSucc) - objective seedC seedD (seedPoint j.succ)) /
        (-dot (SeedOrbit.gradient seedC seedD j) (seedStep j)) = DDisplayActual.armijoRatio j := by
  rw [seedPoint_succ, seedPoint_castSucc, seedStep_eq, DDisplayActual.armijoRatio,
    DDisplayActual.baseValue, trial, ← source_direction]
  rfl

/-- Armijo at the accepted trial of phase $j$ is an upper bound on $c_1$: the non-strict
Armijo test at $z_j$ in the direction $p_j$ with the accepted length $\alpha_j$ holds if and
only if $c_1\le r_j=(G(z_j)-G(z_{j+1}))/(-g_j^Ts_j)$. -/
theorem accepted_armijo_iff (j : Fin 3) (c₁ : ℝ) :
    NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint j.castSucc) (seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₁ (length j) ↔
      c₁ ≤ (objective seedC seedD (seedPoint j.castSucc) - objective seedC seedD (seedPoint j.succ)) /
        (-dot (SeedOrbit.gradient seedC seedD j) (seedStep j)) := by
  have hd : dot (SeedOrbit.gradient seedC seedD j) (seedStep j) < 0 := by
    rw [seedStep_eq, source_direction]
    exact (source_accepted_certificate j).descent
  have hstep : length j • seedDir j = seedStep j := by
    rw [seedDir_eq, seedStep_eq, source_direction]
  have hpt : seedPoint j.castSucc + length j • seedDir j = seedPoint j.succ := by
    rw [hstep]
    fin_cases j <;> rfl
  unfold NonStrictLineSearch.Armijo
  rw [hpt, le_div_iff₀ (by linarith), mul_assoc, ← dot_smul_right, hstep]
  constructor <;> intro h <;> linarith

/-- The Armijo ratios $r_j$ of `accepted_armijo_iff` at the three accepted trials:
$0.76657<r_0<0.76658$, $0.39319<r_1<0.39320$ and $0.37520<r_2<0.37521$. The accepted row
$(2,1/16)$ of Table `art:trial_table` therefore passes Armijo for $c_1\le1/3$ and fails it
for $c_1\ge0.37521$. -/
theorem accepted_armijo_ratios :
    (0.76657 : ℝ) < (objective seedC seedD (seedPoint 0) - objective seedC seedD (seedPoint 1)) /
        (-dot (SeedOrbit.gradient seedC seedD 0) (seedStep 0)) ∧
      (objective seedC seedD (seedPoint 0) - objective seedC seedD (seedPoint 1)) /
        (-dot (SeedOrbit.gradient seedC seedD 0) (seedStep 0)) < 0.76658 ∧
    (0.39319 : ℝ) < (objective seedC seedD (seedPoint 1) - objective seedC seedD (seedPoint 2)) /
        (-dot (SeedOrbit.gradient seedC seedD 1) (seedStep 1)) ∧
      (objective seedC seedD (seedPoint 1) - objective seedC seedD (seedPoint 2)) /
        (-dot (SeedOrbit.gradient seedC seedD 1) (seedStep 1)) < 0.39320 ∧
    (0.37520 : ℝ) < (objective seedC seedD (seedPoint 2) - objective seedC seedD (seedPoint 3)) /
        (-dot (SeedOrbit.gradient seedC seedD 2) (seedStep 2)) ∧
      (objective seedC seedD (seedPoint 2) - objective seedC seedD (seedPoint 3)) /
        (-dot (SeedOrbit.gradient seedC seedD 2) (seedStep 2)) < 0.37521 := by
  have e0 := accepted_armijo_ratio_eq 0
  have e1 := accepted_armijo_ratio_eq 1
  have e2 := accepted_armijo_ratio_eq 2
  have b0 := DDisplayPrecision.actual_bounds 21
  have b1 := DDisplayPrecision.actual_bounds 23
  have b2 := DDisplayPrecision.actual_bounds 25
  change IntervalBounds.Bounds _ (DDisplayActual.armijoRatio 0) _ at b0
  change IntervalBounds.Bounds _ (DDisplayActual.armijoRatio 1) _ at b1
  change IntervalBounds.Bounds _ (DDisplayActual.armijoRatio 2) _ at b2
  unfold IntervalBounds.Bounds at b0 b1 b2
  simp only [DDisplayRaw.lower, DDisplayRaw.upper, Matrix.cons_val] at b0 b1 b2
  change (objective seedC seedD (seedPoint 0) - objective seedC seedD (seedPoint 1)) /
        (-dot (SeedOrbit.gradient seedC seedD 0) (seedStep 0)) = _ at e0
  change (objective seedC seedD (seedPoint 1) - objective seedC seedD (seedPoint 2)) /
        (-dot (SeedOrbit.gradient seedC seedD 1) (seedStep 1)) = _ at e1
  change (objective seedC seedD (seedPoint 2) - objective seedC seedD (seedPoint 3)) /
        (-dot (SeedOrbit.gradient seedC seedD 2) (seedStep 2)) = _ at e2
  rw [e0, e1, e2]
  norm_num at b0 b1 b2 ⊢
  exact ⟨by linarith [b0.1], by linarith [b0.2], by linarith [b1.1], by linarith [b1.2],
    by linarith [b2.1], by linarith [b2.2]⟩

/-- A successful output of the search has a nonempty trial list. -/
theorem search_ne_nil {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ : ℝ} {fuel : ℕ} {l : ℝ}
    {h : Option ℝ} {a b : ℝ} {L : List ℝ}
    (hs : NonStrictLineSearch.search F x p g c₁ c₂ fuel l h a = (some b, L)) : L ≠ [] := by
  cases fuel with
  | zero => simp [NonStrictLineSearch.search] at hs
  | succ fuel =>
    by_cases hA : NonStrictLineSearch.Armijo F x p g c₁ a
    · by_cases hW : NonStrictLineSearch.Wolfe F x p g c₂ a
      · rw [NonStrictLineSearch.search_accept fuel hA hW] at hs
        have hL : L = [a] := (congrArg Prod.snd hs).symm
        rw [hL]
        exact List.cons_ne_nil _ _
      · rw [NonStrictLineSearch.search, if_pos hA, if_neg hW] at hs
        have hL : L = a :: (NonStrictLineSearch.search F x p g c₁ c₂ fuel a h
            (NonStrictLineSearch.nextTrial a h)).2 := (congrArg Prod.snd hs).symm
        rw [hL]
        exact List.cons_ne_nil _ _
    · rw [NonStrictLineSearch.search_armijo_reject fuel hA] at hs
      have hL : L = a :: (NonStrictLineSearch.search F x p g c₁ c₂ fuel l (some a)
          ((l + a) / 2)).2 := (congrArg Prod.snd hs).symm
      rw [hL]
      exact List.cons_ne_nil _ _

/-- An Armijo rejection at the first trial of a search with a known successful output: the
rest of the output is the output of the bisected search. -/
theorem search_reject_step {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ : ℝ} {N : ℕ}
    {l a b : ℝ} {h : Option ℝ} {L : List ℝ} (hA : ¬ NonStrictLineSearch.Armijo F x p g c₁ a)
    (hs : NonStrictLineSearch.search F x p g c₁ c₂ N l h a = (some b, a :: L)) :
    ∃ N', NonStrictLineSearch.search F x p g c₁ c₂ N' l (some a) ((l + a) / 2) = (some b, L) := by
  cases N with
  | zero => simp [NonStrictLineSearch.search] at hs
  | succ N =>
    rw [NonStrictLineSearch.search_armijo_reject N hA] at hs
    refine ⟨N, ?_⟩
    simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hs
    exact Prod.ext hs.1 hs.2

/-- Counterexample to Lemma `art:seed_cycle` and Table `art:trial_table` without a parameter
range ("the entire line-search query list is Table `art:trial_table`"): for $c_1=0.38$ and
$c_2=1/2$ (so $0<c_1<c_2<1$, while $c_1>1/3$) the accepted trial $1/16$ of phase 2 fails
Armijo, and for no trial budget does the specified search from $(z_2,M_2)$ return the
table's phase-2 output $(1/16,[1,1/2,1/4,1/8,1/16])$. -/
theorem seed_cycle_range_counterexample :
    (0 : ℝ) < 38/100 ∧ (38/100 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 ∧ (1/3 : ℝ) < 38/100 ∧
    ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint 2) (seedDir 2)
      (SeedOrbit.gradient seedC seedD 2) (38/100) (1/16) ∧
    ∀ N : ℕ, NonStrictLineSearch.fromMetric (objective seedC seedD) (seedPoint 2)
      (metric seedC seedD 2) (38/100) (1/2) N ≠ (some (1/16), [1, 1/2, 1/4, 1/8, 1/16]) := by
  have h5 : ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint 2) (seedDir 2)
      (SeedOrbit.gradient seedC seedD 2) (38/100) (1/16) := by
    intro hA
    have h := (accepted_armijo_iff 2 (38/100)).mp hA
    have hr := accepted_armijo_ratios.2.2.2.2.2
    change (38/100 : ℝ) ≤ (objective seedC seedD (seedPoint 2) - objective seedC seedD (seedPoint 3)) /
        (-dot (SeedOrbit.gradient seedC seedD 2) (seedStep 2)) at h
    norm_num at hr
    linarith
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, h5, fun N hN => ?_⟩
  have hg : coordinateGradient (objective seedC seedD) (seedPoint 2) = SeedOrbit.gradient seedC seedD 2 := by
    have h := seedPoint_castSucc 2
    change seedPoint 2 = _ at h
    rw [h]
    exact DeterministicLineSearch.actual_coordinateGradient (source_base_hasGradient 2)
  have hp : bfgsStep (metric seedC seedD 2) (SeedOrbit.gradient seedC seedD 2) 1 = seedDir 2 := by
    simp [seedDir, bfgsStep]
  unfold NonStrictLineSearch.fromMetric at hN
  rw [hg, hp] at hN
  have r1 : ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint 2) (seedDir 2)
      (SeedOrbit.gradient seedC seedD 2) (38/100) 1 := table_reject (by norm_num) 4 rfl
  have r2 : ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint 2) (seedDir 2)
      (SeedOrbit.gradient seedC seedD 2) (38/100) (1/2) := table_reject (by norm_num) 5 rfl
  have r3 : ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint 2) (seedDir 2)
      (SeedOrbit.gradient seedC seedD 2) (38/100) (1/4) := table_reject (by norm_num) 6 rfl
  have r4 : ¬ NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint 2) (seedDir 2)
      (SeedOrbit.gradient seedC seedD 2) (38/100) (1/8) := table_reject (by norm_num) 7 rfl
  obtain ⟨N1, h1⟩ := search_reject_step r1 hN
  rw [show ((0 : ℝ) + 1) / 2 = 1/2 by norm_num] at h1
  obtain ⟨N2, h2⟩ := search_reject_step r2 h1
  rw [show ((0 : ℝ) + 1/2) / 2 = 1/4 by norm_num] at h2
  obtain ⟨N3, h3⟩ := search_reject_step r3 h2
  rw [show ((0 : ℝ) + 1/4) / 2 = 1/8 by norm_num] at h3
  obtain ⟨N4, h4⟩ := search_reject_step r4 h3
  rw [show ((0 : ℝ) + 1/8) / 2 = 1/16 by norm_num] at h4
  obtain ⟨N5, h5'⟩ := search_reject_step h5 h4
  exact search_ne_nil h5' rfl

/-! ### The infinite run through homogeneity -/

/-- $G$ is positively homogeneous: $G(tz)=tG(z)$ for $t\ge0$. -/
theorem seed_objective_homogeneous {t : ℝ} (ht : 0 ≤ t) (z : Vec 2) :
    objective seedC seedD (t • z) = t * objective seedC seedD z := by
  rw [seed_slopes.2.2.2.2.2.2, seed_slopes.2.2.2.2.2.2, dot_smul_right, dot_smul_right,
    dot_smul_right, mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht]

/-- The full update commutes with scaling of the matrix: $\mathcal B(tH,g,g^+,\alpha)=
t\,\mathcal B(H,g,g^+,\alpha)$ for $t\ne0$. -/
theorem fullUpdate_scale {n : ℕ} (H : Mat n) (g gplus : Vec n) (α : ℝ) {t : ℝ} (ht : t ≠ 0) :
    fullUpdate (t • H) g gplus α = t • fullUpdate H g gplus α := by
  rw [fullUpdate, bfgsStep_scale_matrix, inverseBFGS_scale _ _ _ ht]
  rfl

/-- Item `A/failure/prose/026` (`paper/sections/failure.tex:185-187`) and
Item `A/failure/prose/027` (`paper/sections/failure.tex:192-196`):
"A smaller copy has the same active slopes, and its inverse matrix produces proportionally
smaller steps. Both sides of every line-search comparison have the same scale. [...] Each
query in phase $j$ is $\rho^m$ times its base query. Gradients are unchanged, function
differences and gradient--step products scale by $\rho^m$, and `art:failure_update` scales
the updated matrix by $\rho^m$. Thus every branch choice and every rejection is preserved, as
well as acceptance."

For the iterate $k=3m+j$ of the seed run (`orbitPoint k` $=\rho^mz_j$, `orbitMetric k`
$=\rho^mM_j$) and every row $q$ of phase $j$ of Table `art:trial_table`: the query is $\rho^m$
times the base query $z_j+\alpha p_j$; the gradients at the scaled point and query are the
base ones; the function difference, the gradient--step products and the step scale by
$\rho^m$; the update scales by $\rho^m$; and both tests decide as at the base point, for
all constants. -/
theorem cone_orbit_scaling (m : ℕ) (j : Fin 3) (q : Fin 9) (hq : trialPhase q = j)
    (c₁ c₂ : ℝ) (gplus : Vec 2) :
    orbitPoint (3 * m + j) = seedRatio ^ m • seedPoint j.castSucc ∧
    orbitMetric (3 * m + j) = seedRatio ^ m • metric seedC seedD j ∧
    orbitPoint (3 * m + j) + trialLength q •
        bfgsStep (orbitMetric (3 * m + j)) (orbitGradient (3 * m + j)) 1 =
      seedRatio ^ m • (seedPoint j.castSucc + trialLength q • seedDir j) ∧
    HasFDerivAt (objective seedC seedD) (gradientFunctional (SeedOrbit.gradient seedC seedD j))
      (seedRatio ^ m • seedPoint j.castSucc) ∧
    HasFDerivAt (objective seedC seedD)
      (gradientFunctional (SeedOrbit.gradient seedC seedD (trialActive q)))
      (seedRatio ^ m • (seedPoint j.castSucc + trialLength q • seedDir j)) ∧
    objective seedC seedD (seedRatio ^ m • (seedPoint j.castSucc + trialLength q • seedDir j)) -
        objective seedC seedD (seedRatio ^ m • seedPoint j.castSucc) =
      seedRatio ^ m * (objective seedC seedD (seedPoint j.castSucc + trialLength q • seedDir j) -
        objective seedC seedD (seedPoint j.castSucc)) ∧
    (∀ i : Fin 3, dot (SeedOrbit.gradient seedC seedD i) (seedRatio ^ m • seedDir j) =
      seedRatio ^ m * dot (SeedOrbit.gradient seedC seedD i) (seedDir j)) ∧
    bfgsStep (seedRatio ^ m • metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) 1 =
      seedRatio ^ m • seedDir j ∧
    fullUpdate (seedRatio ^ m • metric seedC seedD j) (SeedOrbit.gradient seedC seedD j) gplus
        (length j) = seedRatio ^ m • fullUpdate (metric seedC seedD j) (SeedOrbit.gradient seedC seedD j)
        gplus (length j) ∧
    (NonStrictLineSearch.Armijo (objective seedC seedD) (seedRatio ^ m • seedPoint j.castSucc)
        (seedRatio ^ m • seedDir j) (SeedOrbit.gradient seedC seedD j) c₁ (trialLength q) ↔
      NonStrictLineSearch.Armijo (objective seedC seedD) (seedPoint j.castSucc) (seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₁ (trialLength q)) ∧
    (NonStrictLineSearch.Wolfe (objective seedC seedD) (seedRatio ^ m • seedPoint j.castSucc)
        (seedRatio ^ m • seedDir j) (SeedOrbit.gradient seedC seedD j) c₂ (trialLength q) ↔
      NonStrictLineSearch.Wolfe (objective seedC seedD) (seedPoint j.castSucc) (seedDir j)
        (SeedOrbit.gradient seedC seedD j) c₂ (trialLength q)) := by
  subst hq
  have hρ : 0 < seedRatio ^ m := pow_pos source_ratio_pos_lt_one.1 m
  obtain ⟨hx, hH, hg, -⟩ := orbit_phase_parameters m (trialPhase q)
  have hdir : bfgsStep (metric seedC seedD (trialPhase q)) (SeedOrbit.gradient seedC seedD (trialPhase q)) 1 =
      seedDir (trialPhase q) := by
    simp [seedDir, bfgsStep]
  have hquery : seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q) =
      trial seedC seedD seedRatio (trialPhase q) (trialLength q) := seed_query_eq q
  have hbaseA := (source_base_certificate (trialPhase q)).active
  have htrialA := (source_trial_certificate q).active
  have hbase : HasFDerivAt (objective seedC seedD)
      (gradientFunctional (SeedOrbit.gradient seedC seedD (trialPhase q)))
      (seedRatio ^ m • seedPoint (trialPhase q).castSucc) := by
    rw [seedPoint_castSucc]
    exact hasGradient_of_active (hbaseA.scale hρ)
  have htrial : HasFDerivAt (objective seedC seedD)
      (gradientFunctional (SeedOrbit.gradient seedC seedD (trialActive q)))
      (seedRatio ^ m • (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))) := by
    rw [hquery]
    exact hasGradient_of_active (htrialA.scale hρ)
  have hstep : bfgsStep (seedRatio ^ m • metric seedC seedD (trialPhase q))
      (SeedOrbit.gradient seedC seedD (trialPhase q)) 1 = seedRatio ^ m • seedDir (trialPhase q) := by
    rw [bfgsStep_scale_matrix, hdir]
  refine ⟨by rw [hx, seedPoint_castSucc], hH, ?_, hbase, htrial, ?_, fun i => dot_smul_right _ _ _,
    hstep, fullUpdate_scale _ _ _ _ hρ.ne', ?_, ?_⟩
  · rw [hx, hH, hg, hstep, seedPoint_castSucc, smul_comm (trialLength q) (seedRatio ^ m), ← smul_add]
  · rw [seed_objective_homogeneous hρ.le, seed_objective_homogeneous hρ.le]
    ring
  · unfold NonStrictLineSearch.Armijo
    rw [SeedOrbit.scaled_trial, seed_objective_homogeneous hρ.le, seed_objective_homogeneous hρ.le,
      dot_smul_right]
    constructor
    · intro h
      have h' : seedRatio ^ m * objective seedC seedD
          (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) ≤
          seedRatio ^ m * (objective seedC seedD (seedPoint (trialPhase q).castSucc) +
            c₁ * trialLength q * dot (SeedOrbit.gradient seedC seedD (trialPhase q))
              (seedDir (trialPhase q))) := by linarith
      exact le_of_mul_le_mul_left h' hρ
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hρ.le]
  · unfold NonStrictLineSearch.Wolfe
    rw [SeedOrbit.scaled_trial, DeterministicLineSearch.actual_coordinateGradient htrial,
      dot_smul_right, dot_smul_right]
    have hq' : coordinateGradient (objective seedC seedD)
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) =
        SeedOrbit.gradient seedC seedD (trialActive q) := by
      rw [hquery]
      exact DeterministicLineSearch.actual_coordinateGradient (hasGradient_of_active htrialA)
    rw [hq']
    constructor
    · intro h
      have h' : seedRatio ^ m * (c₂ * dot (SeedOrbit.gradient seedC seedD (trialPhase q))
          (seedDir (trialPhase q))) ≤ seedRatio ^ m * dot (SeedOrbit.gradient seedC seedD (trialActive q))
          (seedDir (trialPhase q)) := by linarith
      exact le_of_mul_le_mul_left h' hρ
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hρ.le]

/-- $z_0$ is the first iterate `orbitPoint 0` of the library's seed run `SeedOrbit.run`
(iterates `orbitPoint`, matrices `orbitMetric`). -/
theorem seedPoint_zero_eq : seedPoint 0 = orbitPoint 0 := by
  have h := (orbit_phase_parameters 0 0).1
  simp only [mul_zero, zero_add, pow_zero, one_smul, Fin.val_zero] at h
  rw [h]
  exact seedPoint_castSucc 0

/-- Item `A/failure/disp/010` (`paper/sections/failure.tex:189-191`), equation `art:cone_orbit`:
\[ x_{3m+j}=\rho^mz_j,\qquad H_{3m+j}=\rho^mM_j,\qquad j=0,1,2. \]
For every $0<c_1\le1/3$, $c_1<c_2<1$, the run produced on $G$ by the specified implementation
from $x_0=z_0$, $H_0=I$ (any trial budget $N\ge5$ in each search) is unique, is the library's
seed run (`orbitPoint`, `orbitMetric`), and satisfies the display. -/
theorem cone_orbit (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 (objective seedC seedD),
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = seedPoint 0 ∧ R.H 0 = 1 ∧
      R.x = orbitPoint ∧ R.H = orbitMetric ∧
      (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ N =
        (some (R.α k), trialHistory (phase k))) ∧
      (∀ R' : AdmissibleBFGSRun 2 (objective seedC seedD), R'.x 0 = seedPoint 0 → R'.H 0 = 1 →
        (∀ k, ∃ N L, NonStrictLineSearch.fromMetric (objective seedC seedD) (R'.x k) (R'.H k) c₁ c₂ N =
          (some (R'.α k), L)) → R'.x = R.x ∧ R'.H = R.H) ∧
      ∀ (m : ℕ) (j : Fin 3), R.x (3 * m + j) = seedRatio ^ m • seedPoint j.castSucc ∧
        R.H (3 * m + j) = seedRatio ^ m • metric seedC seedD j := by
  have hH0 : (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 :=
    (actual_run_failure hc₁ hc₁' hc hc₂).1
  have hs : ∀ k, NonStrictLineSearch.fromMetric (objective seedC seedD)
      ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).x k) ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5 =
      (some ((SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂).α k), trialHistory (phase k)) :=
    fun k => DNonStrictObjectives.seed_fromMetric hc₁ hc₁' (hc₁.trans hc) k
  refine ⟨SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, seedPoint_zero_eq.symm, hH0, rfl, rfl,
    fun k N hN => fromMetric_fuel_mono (hs k) hN, ?_, fun m j => ?_⟩
  · intro R' hx' hH' hs'
    obtain ⟨h1, h2, -, -⟩ := implemented_run_unique R' (SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂)
      (hx'.trans seedPoint_zero_eq) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, hs k⟩)
    exact ⟨h1, h2⟩
  · obtain ⟨hx, hH, -, -⟩ := orbit_phase_parameters m j
    exact ⟨hx.trans (by rw [seedPoint_castSucc]), hH⟩

/-- Item `A/failure/disp/011` (`paper/sections/failure.tex:198-200`): the direction
$w=(-1,16)^T$ satisfies
\[ g_0^Tw=g_1^Tw=-1,\qquad g_2^Tw=-c_\circ+16d_\circ<-1. \] -/
theorem downhill_direction :
    dot g0 ![-1, 16] = -1 ∧ dot g1 ![-1, 16] = -1 ∧
      dot (g2 seedC seedD) ![-1, 16] = -seedC + 16 * seedD ∧ -seedC + 16 * seedD < -1 := by
  obtain ⟨h1, h2, h3, h4⟩ := AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1
  refine ⟨by norm_num [dot, g0, Fin.sum_univ_two], by norm_num [dot, g1, Fin.sum_univ_two],
    by simp [dot, g2, Fin.sum_univ_two]; ring, by linarith⟩

/-- Item `A/failure/prose/028` (`paper/sections/failure.tex:196-201`): "The iterates converge
to zero, but the direction $w=(-1,16)^T$ satisfies [display]. Hence $G(tw)=-t$ for $t\ge0$,
so this limit is nonstationary." The iterates `orbitPoint` are those of the run of
`cone_orbit`. -/
theorem cone_limit_nonstationary :
    Tendsto orbitPoint atTop (𝓝 0) ∧
    (∀ t : ℝ, 0 ≤ t → objective seedC seedD (t • ![-1, 16]) = -t) ∧
    objective seedC seedD 0 = 0 ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 :=
  ⟨orbitPoint_tendsto, fun _ ht => objective_downhill_ray ht, SeedOrbit.objective_zero _ _,
    limit_not_stationary⟩

/-! ### Corollary `art:failure_polyhedral` -/

/-- Item `A/failure/corollary/art:failure_polyhedral` (`paper/sections/failure.tex:203-210`),
Corollary `art:failure_polyhedral` (Coercive polyhedral global failure), including its display
Item `A/failure/disp/012` (`paper/sections/failure.tex:205-207`).

"The same deterministic run, with $H_0=I$, fails for
\[ \overline G(u,v)=\max\{u,-u-v/8,c_\circ u+d_\circ v,v-17\}. \]
This function is coercive and has unique minimizer $(-1,16)$, with value $-1$, while the run
converges to the nonstationary origin with value zero."

$\overline G$ is a variable with its defining equation `hGbar` ($u$ = `x 0`, $v$ = `x 1`).
"The same deterministic run": for every $0<c_1\le1/3$, $c_1<c_2<1$, the run produced on
$\overline G$ by the specified implementation from $z_0$ with $H_0=I$ is unique and has the
iterates and matrices of the run on $G$ (`orbitPoint`, `orbitMetric`, equation
`art:cone_orbit`). Coercive: $\overline G\to\infty$ along the cocompact filter. -/
theorem failure_polyhedral (Gbar : Vec 2 → ℝ)
    (hGbar : ∀ x : Vec 2, Gbar x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (seedC * x 0 + seedD * x 1) (x 1 - 17))) :
    Tendsto Gbar (cocompact (Vec 2)) atTop ∧
    Gbar ![-1, 16] = -1 ∧ (∀ x, Gbar ![-1, 16] ≤ Gbar x) ∧ (∀ x, Gbar x = Gbar ![-1, 16] → x = ![-1, 16]) ∧
    Gbar 0 = 0 ∧ (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential Gbar 0 ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
      ∃ R : AdmissibleBFGSRun 2 Gbar,
        R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = seedPoint 0 ∧ R.H 0 = 1 ∧
        R.x = orbitPoint ∧ R.H = orbitMetric ∧
        (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric Gbar (R.x k) (R.H k) c₁ c₂ N =
          (some (R.α k), trialHistory (phase k))) ∧
        (∀ R' : AdmissibleBFGSRun 2 Gbar, R'.x 0 = seedPoint 0 → R'.H 0 = 1 →
          (∀ k, ∃ N L, NonStrictLineSearch.fromMetric Gbar (R'.x k) (R'.H k) c₁ c₂ N =
            (some (R'.α k), L)) → R'.x = R.x ∧ R'.H = R.H) ∧
        Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => Gbar (R.x k)) atTop (𝓝 (Gbar 0)) := by
  have hG : Gbar = coerciveObjective := by
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
  subst hG
  have hopt : coerciveOptimizer = ![-1, 16] := rfl
  rw [← hopt]
  refine ⟨?_, coercive_minimum_value, fun x => by rw [coercive_minimum_value]; exact coercive_lower_bound x,
    fun x hx => coercive_unique_optimizer (hx.trans coercive_minimum_value), coercive_zero_value,
    coercive_limit_not_stationary, ?_⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [(coercive_sublevels_compact b).compl_mem_cocompact] with x hx
    simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
    exact hx.le
  · intro c₁ c₂ hc₁ hc₁' hc hc₂
    have hH0 : (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).H 0 = 1 :=
      (actual_coercive_deterministic_failure hc₁ hc₁' hc hc₂).2.2.2.2.1
    have hs : ∀ k, NonStrictLineSearch.fromMetric coerciveObjective
        ((coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).x k) ((coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).H k) c₁ c₂ 5 =
        (some ((coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).α k), trialHistory (phase k)) :=
      fun k => DNonStrictObjectives.coercive_fromMetric hc₁ hc₁' (hc₁.trans hc) k
    refine ⟨coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, seedPoint_zero_eq.symm, hH0, rfl, rfl,
      fun k N hN => fromMetric_fuel_mono (hs k) hN, ?_, orbitPoint_tendsto, ?_⟩
    · intro R' hx' hH' hs'
      obtain ⟨h1, h2, -, -⟩ := implemented_run_unique R' (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂)
        (hx'.trans seedPoint_zero_eq) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, hs k⟩)
      exact ⟨h1, h2⟩
    · rw [coercive_zero_value]
      exact coercive_orbit_values_tendsto

/-! ### Matching the spatial scale, objective scale and initial matrix -/

/-- A positive multiple of a positive definite matrix is positive definite. -/
theorem posDef_smul {n : ℕ} {H : Mat n} (hH : H.PosDef) {r : ℝ} (hr : 0 < r) : (r • H).PosDef := by
  constructor
  · change (r • H)ᴴ = r • H
    rw [Matrix.conjTranspose_smul, star_trivial, hH.1.eq]
  · intro v hv
    simpa only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul, star_trivial] using
      mul_pos hr (hH.2 v hv)

/-- Chain rule for a matched local model: if $F(\bar x+\lambda y)=C+\sigma\mathcal G(y)$ on an
open set containing $z$ and $\mathcal G$ has gradient $g$ at $z$, then $F$ has gradient
$(\sigma/\lambda)g$ at $\bar x+\lambda z$. -/
theorem matched_hasGradient {n : ℕ} {F 𝒢 : Vec n → ℝ} {xbar : Vec n} {C lam σ : ℝ}
    (hlam : lam ≠ 0) {U : Set (Vec n)} (hU : IsOpen U)
    (hmodel : ∀ y ∈ U, F (xbar + lam • y) = C + σ * 𝒢 y)
    {z g : Vec n} (hz : z ∈ U) (hg : HasFDerivAt 𝒢 (gradientFunctional g) z) :
    HasFDerivAt F (gradientFunctional ((σ / lam) • g)) (xbar + lam • z) := by
  let invmap : Vec n → Vec n := fun w => lam⁻¹ • (w - xbar)
  have hi : invmap (xbar + lam • z) = z := by simp [invmap, smul_smul, hlam]
  have hid : HasFDerivAt invmap (lam⁻¹ • ContinuousLinearMap.id ℝ (Vec n)) (xbar + lam • z) :=
    ((hasFDerivAt_id (xbar + lam • z)).sub_const xbar).const_smul lam⁻¹
  have hg1 : HasFDerivAt 𝒢 (gradientFunctional g) (invmap (xbar + lam • z)) := hi.symm ▸ hg
  have hcomp := hg1.comp (xbar + lam • z) hid
  have hf : HasFDerivAt (fun w => C + σ * 𝒢 (invmap w))
      (gradientFunctional ((σ / lam) • g)) (xbar + lam • z) := by
    convert (hcomp.const_mul σ).const_add C using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, gradientFunctional_apply,
      dot_smul_right, DEmbedding.gradientFunctional_smul]
    field_simp
  apply hf.congr_of_eventuallyEq
  have hnear : ∀ᶠ w in 𝓝 (xbar + lam • z), invmap w ∈ U := by
    have hc : Continuous invmap := continuous_const.smul (continuous_id.sub continuous_const)
    apply hc.continuousAt.eventually
    rw [hi]
    exact hU.mem_nhds hz
  filter_upwards [hnear] with w hw
  have hm := hmodel (invmap w) hw
  have he : xbar + lam • invmap w = w := by simp [invmap, smul_smul, hlam]
  rw [he] at hm
  exact hm

/-- Item `A/failure/disp/014` (`paper/sections/failure.tex:236-239`), equation
`art:matched-scaling`, with its hypothesis
Item `A/failure/disp/013` (`paper/sections/failure.tex:231-233`) (equation
`art:matched-local-model`) and the preceding claim
Item `A/failure/prose/032` (`paper/sections/failure.tex:234`): "Differentiation gives
$g_F=(\sigma/\lambda)g_{\mathcal G}$."

Suppose $F(\bar x+\lambda z)=C+\sigma\mathcal G(z)$, $\lambda,\sigma>0$, on an open set $U$
(near the current and queried points), and $\mathcal G$ has gradient $g_{\mathcal G}$ at
$z\in U$. Then $F$ has gradient $g_F=(\sigma/\lambda)g_{\mathcal G}$ at $\bar x+\lambda z$, and
for the same candidate length $\alpha$ the corresponding inverse matrix
$H_F=(\lambda^2/\sigma)H_{\mathcal G}$ gives
\[ p_F=\lambda p_{\mathcal G},\qquad s_F=\lambda s_{\mathcal G}, \]
with $p=-Hg$ and $s=\alpha p=-\alpha Hg$. -/
theorem matched_scaling {n : ℕ} (F 𝒢 : Vec n → ℝ) (xbar : Vec n) (C lam σ : ℝ) (hlam : 0 < lam)
    (hσ : 0 < σ) (U : Set (Vec n)) (hU : IsOpen U)
    (hmodel : ∀ z ∈ U, F (xbar + lam • z) = C + σ * 𝒢 z)
    (z : Vec n) (hz : z ∈ U) (g𝒢 : Vec n) (hg : HasFDerivAt 𝒢 (gradientFunctional g𝒢) z)
    (gF : Vec n) (hgF : gF = (σ / lam) • g𝒢) (H𝒢 HF : Mat n) (hHF : HF = (lam ^ 2 / σ) • H𝒢)
    (α : ℝ) :
    HasFDerivAt F (gradientFunctional gF) (xbar + lam • z) ∧
    -(HF *ᵥ gF) = lam • -(H𝒢 *ᵥ g𝒢) ∧ -α • (HF *ᵥ gF) = lam • (-α • (H𝒢 *ᵥ g𝒢)) := by
  subst hgF hHF
  have hc : (lam ^ 2 / σ) * (σ / lam) = lam := by field_simp; ring
  have hp : ((lam ^ 2 / σ) • H𝒢) *ᵥ ((σ / lam) • g𝒢) = lam • (H𝒢 *ᵥ g𝒢) := by
    rw [Matrix.smul_mulVec_assoc, Matrix.mulVec_smul, smul_smul, hc]
  refine ⟨matched_hasGradient hlam.ne' hU hmodel hz hg, ?_, ?_⟩
  · rw [hp, smul_neg]
  · rw [hp, smul_comm]

/-- Item `A/failure/prose/033` (`paper/sections/failure.tex:240-244`): "At an accepted pair
$y_F=(\sigma/\lambda)y_{\mathcal G}$. Thus $y_F^Ts_F=\sigma y_{\mathcal G}^Ts_{\mathcal G}$;
the two projection factors in the inverse update are identical, and its rank-one term is
multiplied by $\lambda^2/\sigma$. This proves the matrix relation in `art:matched-scaling`
again after the update." With $g_F=(\sigma/\lambda)g_{\mathcal G}$,
$g_F^+=(\sigma/\lambda)g_{\mathcal G}^+$ and $H_F=(\lambda^2/\sigma)H_{\mathcal G}$ (no
condition on $y^Ts$ is needed): -/
theorem matched_update {n : ℕ} (lam σ : ℝ) (hlam : 0 < lam) (hσ : 0 < σ) (H𝒢 : Mat n)
    (g𝒢 g𝒢' : Vec n) (α : ℝ) (s y sF yF : Vec n) (hs : s = -α • (H𝒢 *ᵥ g𝒢)) (hy : y = g𝒢' - g𝒢)
    (hsF : sF = -α • (((lam ^ 2 / σ) • H𝒢) *ᵥ ((σ / lam) • g𝒢)))
    (hyF : yF = (σ / lam) • g𝒢' - (σ / lam) • g𝒢) :
    yF = (σ / lam) • y ∧ sF = lam • s ∧ dot yF sF = σ * dot y s ∧
    (dot yF sF)⁻¹ • outer sF yF = (dot y s)⁻¹ • outer s y ∧
    (dot yF sF)⁻¹ • outer yF sF = (dot y s)⁻¹ • outer y s ∧
    (dot yF sF)⁻¹ • outer sF sF = (lam ^ 2 / σ) • ((dot y s)⁻¹ • outer s s) ∧
    fullUpdate ((lam ^ 2 / σ) • H𝒢) ((σ / lam) • g𝒢) ((σ / lam) • g𝒢') α =
      (lam ^ 2 / σ) • fullUpdate H𝒢 g𝒢 g𝒢' α := by
  have hc : (lam ^ 2 / σ) * (σ / lam) = lam := by field_simp; ring
  have hp : ((lam ^ 2 / σ) • H𝒢) *ᵥ ((σ / lam) • g𝒢) = lam • (H𝒢 *ᵥ g𝒢) := by
    rw [Matrix.smul_mulVec_assoc, Matrix.mulVec_smul, smul_smul, hc]
  have hyF' : yF = (σ / lam) • y := by rw [hyF, hy, smul_sub]
  have hsF' : sF = lam • s := by
    rw [hsF, hs, hp, smul_comm]
  have hdot : dot yF sF = σ * dot y s := by
    rw [hyF', hsF', dot_smul_right, PlanarUpdate.dot_scale_left]
    field_simp
  have hσ' : σ ≠ 0 := hσ.ne'
  have hlam' : lam ≠ 0 := hlam.ne'
  refine ⟨hyF', hsF', hdot, ?_, ?_, ?_, ?_⟩
  · rw [hdot, hsF', hyF', outer_scale_left, outer_scale_right, smul_smul, smul_smul]
    congr 1
    by_cases h0 : dot y s = 0
    · simp [h0]
    · field_simp
      ring
  · rw [hdot, hsF', hyF', outer_scale_left, outer_scale_right, smul_smul, smul_smul]
    congr 1
    by_cases h0 : dot y s = 0
    · simp [h0]
    · field_simp
      ring
  · rw [hdot, hsF', outer_scale_left, outer_scale_right, smul_smul, smul_smul, smul_smul]
    congr 1
    by_cases h0 : dot y s = 0
    · simp [h0]
    · field_simp
      ring
  · have hr : lam ^ 2 / σ ≠ 0 := by positivity
    have hq : σ / lam ≠ 0 := by positivity
    rw [fullUpdate, fullUpdate, bfgsStep_scale_matrix, bfgsStep_scale_gradient,
      ← smul_sub, inverseBFGS_scale _ _ _ hr, inverseBFGS_scale_secant_pair _ _ _ hq]

/-- Item `A/failure/prose/034` (`paper/sections/failure.tex:244-246`): "Function differences
and all gradient--step products are multiplied by $\sigma>0$, so the Armijo and weak-Wolfe
comparisons, including their strict signs, agree." Under the local model on $U$, for a point
$z$ and a trial point $z+\alpha p$ in $U$ where $\mathcal G$ is differentiable, with
$p_F=\lambda p$ and $g_F=(\sigma/\lambda)g$: the function difference and every
gradient--step product are multiplied by $\sigma$, and the non-strict and strict Armijo and
weak Wolfe tests of $F$ at $\bar x+\lambda z$ hold exactly when those of $\mathcal G$ at $z$
hold. -/
theorem matched_comparisons {n : ℕ} (F 𝒢 : Vec n → ℝ) (xbar : Vec n) (C lam σ : ℝ)
    (hlam : 0 < lam) (hσ : 0 < σ) (U : Set (Vec n)) (hU : IsOpen U)
    (hmodel : ∀ z ∈ U, F (xbar + lam • z) = C + σ * 𝒢 z)
    (z p g : Vec n) (α c₁ c₂ : ℝ) (hz : z ∈ U) (hzα : z + α • p ∈ U)
    (hd : DifferentiableAt ℝ 𝒢 (z + α • p)) :
    F (xbar + lam • z + α • (lam • p)) - F (xbar + lam • z) = σ * (𝒢 (z + α • p) - 𝒢 z) ∧
    (∀ v : Vec n, dot ((σ / lam) • v) (lam • p) = σ * dot v p) ∧
    (NonStrictLineSearch.Armijo F (xbar + lam • z) (lam • p) ((σ / lam) • g) c₁ α ↔
      NonStrictLineSearch.Armijo 𝒢 z p g c₁ α) ∧
    (DeterministicLineSearch.Armijo F (xbar + lam • z) (lam • p) ((σ / lam) • g) c₁ α ↔
      DeterministicLineSearch.Armijo 𝒢 z p g c₁ α) ∧
    (NonStrictLineSearch.Wolfe F (xbar + lam • z) (lam • p) ((σ / lam) • g) c₂ α ↔
      NonStrictLineSearch.Wolfe 𝒢 z p g c₂ α) ∧
    (DeterministicLineSearch.Wolfe F (xbar + lam • z) (lam • p) ((σ / lam) • g) c₂ α ↔
      DeterministicLineSearch.Wolfe 𝒢 z p g c₂ α) := by
  have htrial : xbar + lam • z + α • (lam • p) = xbar + lam • (z + α • p) := by
    rw [smul_add, smul_comm α lam p, add_assoc]
  have hdot : ∀ v : Vec n, dot ((σ / lam) • v) (lam • p) = σ * dot v p := by
    intro v
    rw [dot_smul_right, PlanarUpdate.dot_scale_left]
    field_simp
  have hgrad : coordinateGradient F (xbar + lam • (z + α • p)) =
      (σ / lam) • coordinateGradient 𝒢 (z + α • p) :=
    DeterministicLineSearch.actual_coordinateGradient
      (matched_hasGradient hlam.ne' hU hmodel hzα (hasFDerivAt_coordinateGradient hd))
  have hv1 := hmodel z hz
  have hv2 := hmodel (z + α • p) hzα
  refine ⟨by rw [htrial, hv1, hv2]; ring, hdot, ?_, ?_, ?_, ?_⟩
  · unfold NonStrictLineSearch.Armijo
    rw [htrial, hv1, hv2, hdot]
    constructor
    · intro h
      have h' : σ * 𝒢 (z + α • p) ≤ σ * (𝒢 z + c₁ * α * dot g p) := by linarith
      exact le_of_mul_le_mul_left h' hσ
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hσ.le]
  · unfold DeterministicLineSearch.Armijo
    rw [htrial, hv1, hv2, hdot]
    constructor
    · intro h
      have h' : σ * 𝒢 (z + α • p) < σ * (𝒢 z + c₁ * α * dot g p) := by linarith
      exact lt_of_mul_lt_mul_left h' hσ.le
    · intro h
      nlinarith [mul_lt_mul_of_pos_left h hσ]
  · unfold NonStrictLineSearch.Wolfe
    rw [htrial, hgrad, hdot, hdot]
    constructor
    · intro h
      have h' : σ * (c₂ * dot g p) ≤ σ * dot (coordinateGradient 𝒢 (z + α • p)) p := by linarith
      exact le_of_mul_le_mul_left h' hσ
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hσ.le]
  · unfold DeterministicLineSearch.Wolfe
    rw [htrial, hgrad, hdot, hdot]
    constructor
    · intro h
      have h' : σ * (c₂ * dot g p) < σ * dot (coordinateGradient 𝒢 (z + α • p)) p := by linarith
      exact lt_of_mul_lt_mul_left h' hσ.le
    · intro h
      nlinarith [mul_lt_mul_of_pos_left h hσ]

/-- Item `A/failure/prose/036` (`paper/sections/failure.tex:249-252`), first part: "To
transfer a particular run, the local model must cover the current point and every candidate
the search actually visits. Under that containment, induction on the bracket decisions
transfers the full trial tree". If the local model holds on an open $U$ that contains the
current point $z$ and every candidate $z+ap$ that the specified search on $\mathcal G$ from
$(z,H)$ visits, where $\mathcal G$ is differentiable, then the specified search on $F$ from
$(\bar x+\lambda z,(\lambda^2/\sigma)H)$ returns the same accepted length and the same trial
list (for the same budget). -/
theorem matched_search_transfer {n : ℕ} (F 𝒢 : Vec n → ℝ) (xbar : Vec n) (C lam σ : ℝ)
    (hlam : 0 < lam) (hσ : 0 < σ) (U : Set (Vec n)) (hU : IsOpen U)
    (hmodel : ∀ z ∈ U, F (xbar + lam • z) = C + σ * 𝒢 z)
    (z g : Vec n) (hz : z ∈ U) (hg : HasFDerivAt 𝒢 (gradientFunctional g) z) (H : Mat n)
    (c₁ c₂ : ℝ) (N : ℕ)
    (hq : ∀ a ∈ (NonStrictLineSearch.fromMetric 𝒢 z H c₁ c₂ N).2,
      z + a • bfgsStep H g 1 ∈ U ∧ DifferentiableAt ℝ 𝒢 (z + a • bfgsStep H g 1)) :
    NonStrictLineSearch.fromMetric F (xbar + lam • z) ((lam ^ 2 / σ) • H) c₁ c₂ N =
      NonStrictLineSearch.fromMetric 𝒢 z H c₁ c₂ N := by
  have hgF := matched_hasGradient hlam.ne' hU hmodel hz hg
  have hcg := DeterministicLineSearch.actual_coordinateGradient hg
  have hcf := DeterministicLineSearch.actual_coordinateGradient hgF
  have hc : (lam ^ 2 / σ) * (σ / lam) = lam := by field_simp; ring
  have hstep : bfgsStep ((lam ^ 2 / σ) • H) ((σ / lam) • g) 1 = lam • bfgsStep H g 1 := by
    rw [bfgsStep_scale_matrix, bfgsStep_scale_gradient, smul_smul, hc]
  unfold NonStrictLineSearch.fromMetric at hq ⊢
  rw [hcg] at hq ⊢
  rw [hcf, hstep]
  apply NonStrictLineSearch.search_history_congr
  intro b hb
  obtain ⟨hzb, hdb⟩ := hq b hb
  obtain ⟨-, -, hA, -, hW, -⟩ := matched_comparisons F 𝒢 xbar C lam σ hlam hσ U hU hmodel z
    (bfgsStep H g 1) g b c₁ c₂ hz hzb hdb
  exact ⟨hA, hW⟩

/-- Item `A/failure/prose/036` (`paper/sections/failure.tex:249-252`), second part: "and
induction on accepted steps transfers the matrices." If an implemented run on $\mathcal G$
(an `AdmissibleBFGSRun` whose lengths are outputs of the specified search) has all its
points and all visited candidates in $U$ (candidates where $\mathcal G$ is differentiable),
and $F$ is convex, then $\bar x+\lambda x_k$, $(\lambda^2/\sigma)H_k$,
$(\sigma/\lambda)g_k$, $\alpha_k$ form an implemented run on $F$ with the same trial lists. -/
theorem matched_run_transfer {n : ℕ} (F 𝒢 : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xbar : Vec n)
    (C lam σ : ℝ) (hlam : 0 < lam) (hσ : 0 < σ) (U : Set (Vec n)) (hU : IsOpen U)
    (hmodel : ∀ z ∈ U, F (xbar + lam • z) = C + σ * 𝒢 z)
    (R : AdmissibleBFGSRun n 𝒢) (N : ℕ) (hist : ℕ → List ℝ)
    (hs : ∀ k, NonStrictLineSearch.fromMetric 𝒢 (R.x k) (R.H k) R.c₁ R.c₂ N = (some (R.α k), hist k))
    (hx : ∀ k, R.x k ∈ U)
    (hq : ∀ k, ∀ a ∈ hist k, R.x k + a • bfgsStep (R.H k) (R.g k) 1 ∈ U ∧
      DifferentiableAt ℝ 𝒢 (R.x k + a • bfgsStep (R.H k) (R.g k) 1)) :
    ∃ R' : AdmissibleBFGSRun n F, R'.c₁ = R.c₁ ∧ R'.c₂ = R.c₂ ∧
      (∀ k, R'.x k = xbar + lam • R.x k ∧ R'.H k = (lam ^ 2 / σ) • R.H k ∧
        R'.g k = (σ / lam) • R.g k ∧ R'.α k = R.α k) ∧
      ∀ k, NonStrictLineSearch.fromMetric F (R'.x k) (R'.H k) R.c₁ R.c₂ N = (some (R'.α k), hist k) := by
  have hc : (lam ^ 2 / σ) * (σ / lam) = lam := by field_simp; ring
  have hstep : ∀ k a, bfgsStep ((lam ^ 2 / σ) • R.H k) ((σ / lam) • R.g k) a =
      lam • bfgsStep (R.H k) (R.g k) a := by
    intro k a
    rw [bfgsStep_scale_matrix, bfgsStep_scale_gradient, smul_smul, hc]
  have hdot : ∀ v w : Vec n, dot ((σ / lam) • v) (lam • w) = σ * dot v w := by
    intro v w
    rw [dot_smul_right, PlanarUpdate.dot_scale_left]
    field_simp
  let R' : AdmissibleBFGSRun n F :=
    { convex := hF
      x := fun k => xbar + lam • R.x k
      H := fun k => (lam ^ 2 / σ) • R.H k
      g := fun k => (σ / lam) • R.g k
      α := R.α
      c₁ := R.c₁
      c₂ := R.c₂
      c₁_pos := R.c₁_pos
      c₁_lt_c₂ := R.c₁_lt_c₂
      c₂_lt_one := R.c₂_lt_one
      initial_posDef := posDef_smul R.initial_posDef (by positivity)
      alpha_pos := R.alpha_pos
      gradient_nonzero := fun k => smul_ne_zero (by positivity) (R.gradient_nonzero k)
      hasGradient := fun k => matched_hasGradient hlam.ne' hU hmodel (hx k) (R.hasGradient k)
      step := fun k => by
        rw [hstep, R.step, smul_add, add_assoc]
      update := fun k => by
        rw [R.update]
        exact ((matched_update lam σ hlam hσ (R.H k) (R.g k) (R.g (k + 1)) (R.α k) _ _ _ _ rfl rfl
          rfl rfl).2.2.2.2.2.2).symm
      armijo := fun k => by
        rw [hmodel _ (hx (k + 1)), hmodel _ (hx k), hstep, hdot]
        nlinarith [mul_le_mul_of_nonneg_left (R.armijo k) hσ.le]
      weak_wolfe := fun k => by
        rw [hstep, hdot, hdot]
        nlinarith [mul_le_mul_of_nonneg_left (R.weak_wolfe k) hσ.le] }
  refine ⟨R', rfl, rfl, fun k => ⟨rfl, rfl, rfl, rfl⟩, fun k => ?_⟩
  have h := matched_search_transfer F 𝒢 xbar C lam σ hlam hσ U hU hmodel (R.x k) (R.g k) (hx k)
    (R.hasGradient k) (R.H k) R.c₁ R.c₂ N (by rw [hs k]; exact hq k)
  exact h.trans (hs k)

/-- Item `A/failure/prose/037` (`paper/sections/failure.tex:255-256`): "The choice
$\sigma=\lambda^2$ is decisive: it leaves the initial matrix unchanged":
$H_F=(\lambda^2/\sigma)H_{\mathcal G}=H_{\mathcal G}$. -/
theorem matched_identity_matrix {n : ℕ} (lam σ : ℝ) (hlam : lam ≠ 0) (hσ : σ = lam ^ 2)
    (H : Mat n) : (lam ^ 2 / σ) • H = H := by
  rw [hσ, div_self (pow_ne_zero 2 hlam), one_smul]

/-! ### The scalar interpolation -/

open DScalarGeometric in
/-- Item `A/failure/prose/042` (`paper/sections/failure.tex:272-273`): "Let $\theta=1/16$,
$a_\ell=\theta^\ell$, $\varepsilon=1/128$, and $b_*=2c_\circ-32d_\circ\in(33,34)$." The
library's $\theta$ (`DScalarGeometric.theta`, `DScalarRamp.theta`), $a_\ell$ (`scale ℓ`),
$\varepsilon$ (`DScalarRamp.epsilon`) and $b_*$ (`DEmbedding.bStar`) have these values, and
$33<b_*<34$. -/
theorem scalar_constants :
    DScalarGeometric.theta = 1/16 ∧ DScalarRamp.theta = 1/16 ∧
    (∀ ℓ : ℕ, scale ℓ = DScalarGeometric.theta ^ ℓ) ∧ DScalarRamp.epsilon = 1/128 ∧
    DEmbedding.bStar = 2 * seedC - 32 * seedD ∧ 33 < DEmbedding.bStar ∧ DEmbedding.bStar < 34 :=
  ⟨rfl, rfl, fun _ => rfl, rfl, rfl, DEmbedding.bStar_bounds.1, DEmbedding.bStar_bounds.2⟩

theorem scalar_parameter_bounds {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) : 2 ≤ b ∧ b ≤ 34 := by
  rcases hb with rfl | rfl
  · norm_num
  · exact ⟨by linarith [DEmbedding.bStar_bounds.1], DEmbedding.bStar_bounds.2.le⟩

/-- Item `A/failure/disp/015` (`paper/sections/failure.tex:274-277`): for $b\in\{2,b_*\}$,
\[ t_b=\frac{1-(1+\theta+\theta^2)/b}{1-\theta^2},\qquad v=\frac{\xi-t_b+\varepsilon}{2\varepsilon}. \]
The library's `DScalarRamp.center b` is $t_b$ and `DScalarRamp.rampCoordinate b ξ` is $v$. -/
theorem ramp_center_coordinate (b ξ : ℝ) :
    DScalarRamp.center b =
      (1 - (1 + DScalarGeometric.theta + DScalarGeometric.theta ^ 2) / b) / (1 - DScalarGeometric.theta ^ 2) ∧
    DScalarRamp.rampCoordinate b ξ =
      (ξ - DScalarRamp.center b + DScalarRamp.epsilon) / (2 * DScalarRamp.epsilon) :=
  ⟨rfl, rfl⟩

/-- Item `A/failure/disp/016` (`paper/sections/failure.tex:278-286`): for $b\in\{2,b_*\}$,
\[ P_b(\xi)=\begin{cases}0&\xi\le t_b-\varepsilon,\\ 3v^2-2v^3&|\xi-t_b|<\varepsilon,\\
   1&\xi\ge t_b+\varepsilon,\end{cases}\qquad J_b(\xi)=\int_0^\xi P_b(t)\,dt. \]
The library's `DScalarRamp.ramp b` is $P_b$ and `DScalarRamp.primitive b` is $J_b$. -/
theorem ramp_primitive {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (ξ : ℝ) :
    (ξ ≤ DScalarRamp.center b - DScalarRamp.epsilon → DScalarRamp.ramp b ξ = 0) ∧
    (|ξ - DScalarRamp.center b| < DScalarRamp.epsilon →
      DScalarRamp.ramp b ξ = 3 * (DScalarRamp.rampCoordinate b ξ) ^ 2 - 2 * (DScalarRamp.rampCoordinate b ξ) ^ 3) ∧
    (DScalarRamp.center b + DScalarRamp.epsilon ≤ ξ → DScalarRamp.ramp b ξ = 1) ∧
    DScalarRamp.primitive b ξ = ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  refine ⟨DScalarRamp.ramp_eq_zero, fun h => ?_, DScalarRamp.ramp_eq_one,
    DScalarRamp.primitive_eq_integral hl hr ξ⟩
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  exact DScalarRamp.ramp_eq_cubic (by linarith) (by linarith)

/-- Item `A/failure/prose/043` (`paper/sections/failure.tex:287-288`): "The middle formula
for $J_b$ is $2\varepsilon(v^3-v^4/2)$; its outer formulas are zero and $\xi-t_b$." -/
theorem primitive_formulas {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (ξ : ℝ) :
    (ξ ≤ DScalarRamp.center b - DScalarRamp.epsilon → ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t = 0) ∧
    (|ξ - DScalarRamp.center b| < DScalarRamp.epsilon →
      ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t = 2 * DScalarRamp.epsilon *
        ((DScalarRamp.rampCoordinate b ξ) ^ 3 - (DScalarRamp.rampCoordinate b ξ) ^ 4 / 2)) ∧
    (DScalarRamp.center b + DScalarRamp.epsilon ≤ ξ →
      ∫ t in (0 : ℝ)..ξ, DScalarRamp.ramp b t = ξ - DScalarRamp.center b) := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  rw [← DScalarRamp.primitive_eq_integral hl hr ξ]
  refine ⟨DScalarRamp.primitive_eq_zero, fun h => ?_, DScalarRamp.primitive_eq_affine⟩
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  exact DScalarRamp.primitive_eq_quartic (by linarith) (by linarith)

open DScalarGeometric in
/-- Item `A/failure/disp/017` (`paper/sections/failure.tex:290-295`), equation
`art:upper_scalar`, and Item `A/failure/disp/018` (`paper/sections/failure.tex:297-304`): the definition of
$\varphi_b$, $b\in\{2,b_*\}$. For $b\theta a_\ell\le x\le ba_\ell$,
\[ \varphi_b(x)=(\theta a_\ell)^3+ba_\ell^3(1-\theta)\{\theta^2\xi+(1-\theta^2)J_b(\xi)\},\qquad
   \xi=\frac{x/(ba_\ell)-\theta}{1-\theta}, \]
and $\varphi_b(x)=1-3(x+1)+3(x+1)^2$ ($x<-1$), $-x^3$ ($-1\le x\le0$), $1+x-b$ ($x\ge b$).
The library's `DScalar.phi b` satisfies these formulas; by `phi_unique` they determine it. -/
theorem phi_formulas {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    (∀ (ℓ : ℕ) (x : ℝ), b * theta * scale ℓ ≤ x → x ≤ b * scale ℓ →
      DScalar.phi b x = (theta * scale ℓ) ^ 3 + b * (scale ℓ) ^ 3 * (1 - theta) *
        (theta ^ 2 * ((x / (b * scale ℓ) - theta) / (1 - theta)) +
          (1 - theta ^ 2) * DScalarRamp.primitive b ((x / (b * scale ℓ) - theta) / (1 - theta)))) ∧
    (∀ x : ℝ, x < -1 → DScalar.phi b x = 1 - 3 * (x + 1) + 3 * (x + 1) ^ 2) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 0 → DScalar.phi b x = -x ^ 3) ∧
    (∀ x : ℝ, b ≤ x → DScalar.phi b x = 1 + x - b) := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  exact ⟨fun ℓ x h1 h2 => DScalar.phi_interval hl hr ℓ h1 h2,
    fun x hx => DScalar.phi_eq_negative_quadratic hl hr hx.le,
    fun x h1 h2 => DScalar.phi_eq_negative_cubic hl hr h1 h2,
    fun x hx => DScalar.phi_eq_outer hl hr hx⟩

open DScalarGeometric in
/-- Item `A/failure/prose/041` (`paper/sections/failure.tex:269-270`): "The following
formulas fix the construction completely." Every function satisfying the defining formulas
`art:upper_scalar` and the completion of $\varphi_b$ is `DScalar.phi b`. -/
theorem phi_unique {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (ψ : ℝ → ℝ)
    (h1 : ∀ (ℓ : ℕ) (x : ℝ), b * theta * scale ℓ ≤ x → x ≤ b * scale ℓ →
      ψ x = (theta * scale ℓ) ^ 3 + b * (scale ℓ) ^ 3 * (1 - theta) *
        (theta ^ 2 * ((x / (b * scale ℓ) - theta) / (1 - theta)) +
          (1 - theta ^ 2) * DScalarRamp.primitive b ((x / (b * scale ℓ) - theta) / (1 - theta))))
    (h2 : ∀ x : ℝ, x < -1 → ψ x = 1 - 3 * (x + 1) + 3 * (x + 1) ^ 2)
    (h3 : ∀ x : ℝ, -1 ≤ x → x ≤ 0 → ψ x = -x ^ 3)
    (h4 : ∀ x : ℝ, b ≤ x → ψ x = 1 + x - b) :
    ψ = DScalar.phi b := by
  obtain ⟨f1, f2, f3, f4⟩ := phi_formulas hb
  obtain ⟨hl, _⟩ := scalar_parameter_bounds hb
  have hb0 : 0 < b := by linarith
  funext x
  rcases lt_or_le x (-1) with hx | hx
  · rw [h2 x hx, f2 x hx]
  rcases le_or_lt x 0 with hx0 | hx0
  · rw [h3 x hx hx0, f3 x hx hx0]
  rcases le_or_lt b x with hxb | hxb
  · rw [h4 x hxb, f4 x hxb]
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := positive_interval_cover hb0 hx0 hxb.le
  rw [h1 ℓ x hℓ1.le hℓ2, f1 ℓ x hℓ1.le hℓ2]

open DScalarGeometric in
/-- Item `A/failure/lemma/art:upper_scalar_lemma` (`paper/sections/failure.tex:306-318`), Lemma
`art:upper_scalar_lemma` (Scalar interpolation), including its displays
Item `A/failure/disp/019` (`paper/sections/failure.tex:309-313`) (equations
`art:scalar_curvature` and `art:scalar_plateau`) and
Item `A/failure/disp/020` (`paper/sections/failure.tex:315-317`).

"The functions $\varphi_b$ are convex, coercive and globally $C^{2,1}$, are nonnegative, and
vanish only at zero. They satisfy
\[ 0\le\varphi_b''\le\max\{6,102/b\},\qquad
   \varphi_b(ba_\ell+h)=a_\ell^3+a_\ell^2h\quad(|h|\le a_\ell/2). \]
Their second derivatives are globally Lipschitz with constant
$L_b=\max\{6,139264/(5b^2)\}$."

Here $b\in\{2,b_*\}$, $\varphi_b$ is `DScalar.phi b`, $\varphi_b''$ is
`deriv (deriv (DScalar.phi b))` and coercive means $\varphi_b\to\infty$ along the cocompact
filter of $\mathbb R$; $C^{2,1}$ is `ContDiff ℝ 2` together with the Lipschitz bound. -/
theorem upper_scalar_lemma {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    ConvexOn ℝ univ (DScalar.phi b) ∧ Tendsto (DScalar.phi b) (cocompact ℝ) atTop ∧
    ContDiff ℝ 2 (DScalar.phi b) ∧
    (∀ x, 0 ≤ DScalar.phi b x) ∧ (∀ x, DScalar.phi b x = 0 ↔ x = 0) ∧
    (∀ x, 0 ≤ deriv (deriv (DScalar.phi b)) x ∧ deriv (deriv (DScalar.phi b)) x ≤ max 6 (102 / b)) ∧
    (∀ (ℓ : ℕ) (h : ℝ), |h| ≤ scale ℓ / 2 →
      DScalar.phi b (b * scale ℓ + h) = (scale ℓ) ^ 3 + (scale ℓ) ^ 2 * h) ∧
    ∀ x y : ℝ, |deriv (deriv (DScalar.phi b)) x - deriv (deriv (DScalar.phi b)) y| ≤
      max 6 (139264 / (5 * b ^ 2)) * |x - y| := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  obtain ⟨hC, hconv, hnn, hzero, hcoer, -, -, -, hsec, hlip, -, hplat, -⟩ :=
    DScalar.scalar_function_contract hl hr
  refine ⟨hconv, hcoer, hC, hnn, hzero, hsec, fun ℓ h hh => hplat ℓ h hh, fun x y => ?_⟩
  have h := hlip.dist_le_mul x y
  simpa only [Real.dist_eq, NNReal.coe_mk] using h

open DScalarGeometric in
/-- Item `A/failure/disp/021` (`paper/sections/failure.tex:322-325`), in the proof of Lemma
`art:upper_scalar_lemma`: on a positive interval $b\theta a_\ell\le x\le ba_\ell$, with
$\xi=(x/(ba_\ell)-\theta)/(1-\theta)$,
\[ \varphi_b'=a_\ell^2\{\theta^2+(1-\theta^2)P_b(\xi)\},\qquad
   \varphi_b''=\frac{a_\ell(1+\theta)}bP_b'(\xi). \] -/
theorem positive_interval_derivatives {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (ℓ : ℕ) (x : ℝ)
    (hx1 : b * theta * scale ℓ ≤ x) (hx2 : x ≤ b * scale ℓ) :
    deriv (DScalar.phi b) x = (scale ℓ) ^ 2 *
        (theta ^ 2 + (1 - theta ^ 2) * DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta))) ∧
    deriv (deriv (DScalar.phi b)) x =
      scale ℓ * (1 + theta) / b * deriv (DScalarRamp.ramp b) ((x / (b * scale ℓ) - theta) / (1 - theta)) := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  have hx0 : 0 ≤ x := le_trans (by have := scale_pos ℓ; have := theta_pos; positivity) hx1
  rw [DScalar.deriv_phi hl hr, DScalar.deriv_phiFirst hl]
  refine ⟨?_, ?_⟩
  · rw [DScalar.phiFirst, DScalarNegative.first_eq_zero hx0, add_zero,
      DScalar.positiveSlope_interval hl hr ℓ hx1 hx2]
    rfl
  · rw [DScalar.phiSecond, DScalarNegative.second_eq_zero hx0, add_zero,
      DScalar.positiveCurvature_interval hl hr ℓ hx1 hx2, DScalar.curvatureComponent,
      (DScalarRamp.ramp_hasDerivAt b _).deriv]
    rfl

/-- $P_b(\xi)=1$ exactly when $\xi\ge t_b+\varepsilon$. -/
theorem ramp_eq_one_iff (b ξ : ℝ) :
    DScalarRamp.ramp b ξ = 1 ↔ DScalarRamp.center b + DScalarRamp.epsilon ≤ ξ := by
  refine ⟨fun h => ?_, DScalarRamp.ramp_eq_one⟩
  by_contra hlt
  push_neg at hlt
  rcases le_or_lt ξ (DScalarRamp.center b - DScalarRamp.epsilon) with h0 | h0
  · rw [DScalarRamp.ramp_eq_zero h0] at h
    norm_num at h
  · rw [DScalarRamp.ramp_eq_cubic h0 hlt] at h
    have hv0 : 0 < DScalarRamp.rampCoordinate b ξ := by
      simp only [DScalarRamp.rampCoordinate, DScalarRamp.epsilon] at *
      apply div_pos _ (by norm_num)
      linarith
    have hv1 : DScalarRamp.rampCoordinate b ξ < 1 := by
      simp only [DScalarRamp.rampCoordinate, DScalarRamp.epsilon] at *
      rw [div_lt_one (by norm_num)]
      linarith
    simp only [DScalarRamp.cubic] at h
    nlinarith [mul_pos (mul_pos (sub_pos.mpr hv1) (sub_pos.mpr hv1)) (by linarith : (0 : ℝ) < 1 + 2 * DScalarRamp.rampCoordinate b ξ)]

/-- $P_b(\xi)=0$ exactly when $\xi\le t_b-\varepsilon$. -/
theorem ramp_eq_zero_iff (b ξ : ℝ) :
    DScalarRamp.ramp b ξ = 0 ↔ ξ ≤ DScalarRamp.center b - DScalarRamp.epsilon := by
  refine ⟨fun h => ?_, DScalarRamp.ramp_eq_zero⟩
  by_contra hlt
  push_neg at hlt
  rcases le_or_lt (DScalarRamp.center b + DScalarRamp.epsilon) ξ with h1 | h1
  · rw [DScalarRamp.ramp_eq_one h1] at h
    norm_num at h
  · rw [DScalarRamp.ramp_eq_cubic hlt h1] at h
    have hv0 : 0 < DScalarRamp.rampCoordinate b ξ := by
      simp only [DScalarRamp.rampCoordinate, DScalarRamp.epsilon] at *
      apply div_pos _ (by norm_num)
      linarith
    have hv1 : DScalarRamp.rampCoordinate b ξ < 1 := by
      simp only [DScalarRamp.rampCoordinate, DScalarRamp.epsilon] at *
      rw [div_lt_one (by norm_num)]
      linarith
    simp only [DScalarRamp.cubic] at h
    nlinarith [mul_pos (mul_pos hv0 hv0) (by linarith : (0 : ℝ) < 3 - 2 * DScalarRamp.rampCoordinate b ξ)]

open DScalarGeometric in
/-- Item `A/failure/disp/022` (`paper/sections/failure.tex:342-345`), in the proof of Lemma
`art:upper_scalar_lemma`: "The constant-derivative lengths below and above $ba_\ell$,
divided by $a_\ell$, are
\[ b(1-\theta)(1-t_b-\varepsilon),\qquad \frac{b(1-\theta)(t_b-\varepsilon)}\theta." \]
Below the node $ba_\ell$: on its interval $[b\theta a_\ell,ba_\ell]$ the derivative equals
the node slope $a_\ell^2$ exactly on $[ba_\ell-a_\ell\,b(1-\theta)(1-t_b-\varepsilon),ba_\ell]$.
Above the node $ba_{\ell+1}$: on the interval $[ba_{\ell+1},ba_\ell]$ the derivative equals
$a_{\ell+1}^2$ exactly on
$[ba_{\ell+1},ba_{\ell+1}+a_{\ell+1}\,b(1-\theta)(t_b-\varepsilon)/\theta]$. (For the node
$ba_0=b$ the upper side is the affine extension.) -/
theorem constant_derivative_lengths {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) (ℓ : ℕ) :
    (∀ x, b * theta * scale ℓ ≤ x → x ≤ b * scale ℓ →
      (deriv (DScalar.phi b) x = (scale ℓ) ^ 2 ↔
        b * scale ℓ - scale ℓ * (b * (1 - theta) * (1 - DScalarRamp.center b - DScalarRamp.epsilon)) ≤ x)) ∧
    (∀ x, b * scale (ℓ + 1) ≤ x → x ≤ b * scale ℓ →
      (deriv (DScalar.phi b) x = (scale (ℓ + 1)) ^ 2 ↔
        x ≤ b * scale (ℓ + 1) + scale (ℓ + 1) * (b * (1 - theta) * (DScalarRamp.center b - DScalarRamp.epsilon) / theta))) := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  have hb0 : 0 < b := by linarith
  have ha := scale_pos ℓ
  have ha2 : (scale ℓ) ^ 2 ≠ 0 := (pow_pos ha 2).ne'
  have hθ : (1 : ℝ) - theta ^ 2 ≠ 0 := by norm_num [theta]
  refine ⟨fun x hx1 hx2 => ?_, fun x hx1 hx2 => ?_⟩
  · rw [(positive_interval_derivatives hb ℓ x hx1 hx2).1]
    have hiff : (scale ℓ) ^ 2 * (theta ^ 2 + (1 - theta ^ 2) *
        DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta))) = (scale ℓ) ^ 2 ↔
        DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta)) = 1 := by
      constructor
      · intro h
        have h' : (scale ℓ) ^ 2 * (1 - theta ^ 2) *
            (DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta)) - 1) = 0 := by
          linear_combination h
        rcases mul_eq_zero.mp h' with h0 | h0
        · rcases mul_eq_zero.mp h0 with h00 | h00
          · exact absurd h00 ha2
          · exact absurd h00 hθ
        · linarith
      · intro h
        rw [h]
        ring
    rw [hiff, ramp_eq_one_iff]
    change _ ≤ DScalarGeometric.coordinate b (scale ℓ) x ↔ _
    have hL : DScalarRamp.lowerLength b =
        b * (1 - theta) * (1 - DScalarRamp.center b - DScalarRamp.epsilon) := rfl
    have heq : (b - DScalarRamp.lowerLength b) * scale ℓ =
        b * scale ℓ - scale ℓ * (b * (1 - theta) * (1 - DScalarRamp.center b - DScalarRamp.epsilon)) := by
      rw [hL]
      ring
    rw [DScalar.coordinate_ge_iff hb0 ha, DScalar.lower_threshold_identity, heq]
  · have hs1 : scale (ℓ + 1) = theta * scale ℓ := scale_succ ℓ
    have hx1' : b * theta * scale ℓ ≤ x := by
      rw [hs1, ← mul_assoc] at hx1
      exact hx1
    rw [(positive_interval_derivatives hb ℓ x hx1' hx2).1]
    have hiff : (scale ℓ) ^ 2 * (theta ^ 2 + (1 - theta ^ 2) *
        DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta))) = (scale (ℓ + 1)) ^ 2 ↔
        DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta)) = 0 := by
      rw [hs1]
      constructor
      · intro h
        have h' : (scale ℓ) ^ 2 * (1 - theta ^ 2) *
            DScalarRamp.ramp b ((x / (b * scale ℓ) - theta) / (1 - theta)) = 0 := by
          linear_combination h
        rcases mul_eq_zero.mp h' with h0 | h0
        · rcases mul_eq_zero.mp h0 with h00 | h00
          · exact absurd h00 ha2
          · exact absurd h00 hθ
        · exact h0
      · intro h
        rw [h]
        ring
    rw [hiff, ramp_eq_zero_iff]
    change DScalarGeometric.coordinate b (scale ℓ) x ≤ _ ↔ _
    have hU : DScalarRamp.upperLength b =
        b * (1 - theta) * (DScalarRamp.center b - DScalarRamp.epsilon) / theta := rfl
    have heq : (b + DScalarRamp.upperLength b) * scale (ℓ + 1) =
        b * scale (ℓ + 1) + scale (ℓ + 1) * (b * (1 - theta) * (DScalarRamp.center b - DScalarRamp.epsilon) / theta) := by
      rw [hU]
      ring
    rw [DScalar.coordinate_le_iff hb0 ha, DScalar.upper_threshold_identity, heq]

open DScalarGeometric in
/-- Item `A/failure/prose/039` (`paper/sections/failure.tex:264-266`): "Their node values are
$a_\ell^3$ and their node slopes are $a_\ell^2$. A monotone derivative connects neighboring
nodes and is constant on a neighborhood of each node." For $b\in\{2,b_*\}$ and every $\ell$:
$\varphi_b(ba_\ell)=a_\ell^3$, $\varphi_b'(ba_\ell)=a_\ell^2$, $\varphi_b'$ is monotone, and
$\varphi_b'=a_\ell^2$ on $|x-ba_\ell|<a_\ell/2$. -/
theorem scalar_nodes {b : ℝ} (hb : b = 2 ∨ b = DEmbedding.bStar) :
    (∀ ℓ : ℕ, DScalar.phi b (b * scale ℓ) = (scale ℓ) ^ 3 ∧
      HasDerivAt (DScalar.phi b) ((scale ℓ) ^ 2) (b * scale ℓ)) ∧
    Monotone (deriv (DScalar.phi b)) ∧
    ∀ (ℓ : ℕ) (h : ℝ), |h| < scale ℓ / 2 → deriv (DScalar.phi b) (b * scale ℓ + h) = (scale ℓ) ^ 2 := by
  obtain ⟨hl, hr⟩ := scalar_parameter_bounds hb
  refine ⟨fun ℓ => ⟨DScalar.phi_node hl hr ℓ, DScalar.phi_node_hasDerivAt hl hr ℓ⟩, ?_, ?_⟩
  · rw [DScalar.deriv_phi hl hr]
    exact monotone_of_hasDerivAt_nonneg (DScalar.phiFirst_hasDerivAt hl)
      (fun x => (DScalar.phiSecond_bounds hl hr x).1)
  · intro ℓ h hh
    rw [DScalar.deriv_phi hl hr]
    exact DScalar.phiFirst_plateau hl hr ℓ hh

/-! ### One objective and the local model -/

/-- Item `A/failure/disp/023` (`paper/sections/failure.tex:359-362`), equation
`art:upper_objective`:
\[ F(u,v)=\max\{\varphi_2(u),\varphi_2(-u-v/8),\varphi_{b_*}(c_\circ u+d_\circ v),v\}. \]
The library's `DEmbedding.objective` is the maximum of the four branches
`DEmbedding.branch i` ($u$ = `x 0`, $v$ = `x 1`). -/
theorem upper_objective (x : Vec 2) :
    DEmbedding.objective x = max (max (DScalar.phi 2 (x 0)) (DScalar.phi 2 (-x 0 - x 1 / 8)))
      (max (DScalar.phi DEmbedding.bStar (seedC * x 0 + seedD * x 1)) (x 1)) ∧
    DEmbedding.objective x = Finset.univ.sup' Finset.univ_nonempty (fun i => DEmbedding.branch i x) ∧
    DEmbedding.branch 0 x = DScalar.phi 2 (x 0) ∧ DEmbedding.branch 1 x = DScalar.phi 2 (-x 0 - x 1 / 8) ∧
    DEmbedding.branch 2 x = DScalar.phi DEmbedding.bStar (seedC * x 0 + seedD * x 1) ∧
    DEmbedding.branch 3 x = x 1 := by
  refine ⟨DEmbedding.objective_literal x, rfl, ?_, ?_, ?_, rfl⟩
  · change DScalar.phi 2 (dot g0 x) = _
    simp [dot, g0, Fin.sum_univ_two]
  · change DScalar.phi 2 (dot g1 x) = _
    congr 1
    simp [dot, g1, Fin.sum_univ_two]
    ring
  · change DScalar.phi DEmbedding.bStar (dot (g2 seedC seedD) x) = _
    simp [dot, g2, Fin.sum_univ_two]

/-- The second derivative of $\varphi_b$ vanishes on the open plateaus $|x-ba_\ell|<a_\ell/2$. -/
theorem phiSecond_plateau {b h : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| < DScalarGeometric.scale m / 2) : DScalar.phiSecond b (b * DScalarGeometric.scale m + h) = 0 := by
  have hc : Continuous (fun y : ℝ => |y - b * DScalarGeometric.scale m|) :=
    (continuous_id.sub continuous_const).abs
  have hx : |b * DScalarGeometric.scale m + h - b * DScalarGeometric.scale m| < DScalarGeometric.scale m / 2 := by
    simpa only [add_sub_cancel_left] using hh
  have heq : DScalar.phiFirst b =ᶠ[𝓝 (b * DScalarGeometric.scale m + h)]
      (fun _ => (DScalarGeometric.scale m) ^ 2) := by
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with y hy
    have he : b * DScalarGeometric.scale m + (y - b * DScalarGeometric.scale m) = y := by abel
    simpa only [he] using DScalar.phiFirst_plateau hl hr m hy
  exact (DScalar.phiFirst_hasDerivAt hl _).unique ((hasDerivAt_const _ _).congr_of_eventuallyEq heq)

/-- Item `A/failure/prose/044` (`paper/sections/failure.tex:363-368`): "The Hessian of each of
the first three branches is a nonnegative scalar multiple of $g_ig_i^T$. Equation
`art:scalar_curvature` gives the upper bounds $51$, $51(65/64)<52$, and $12$, respectively, on
their operator norms; the last branch has zero Hessian. Their Hessians are globally Lipschitz
because $\varphi_b''$ is Lipschitz and the arguments are linear." (Euclidean operator norms;
Lipschitz constant $60000$.) -/
theorem objective_branch_hessians :
    (∀ (i : Fin 3) (x : Vec 2), ∃ t : ℝ, 0 ≤ t ∧
      RadialHessian.matrix (DEmbedding.branch i.castSucc) x =
        t • outer (SeedOrbit.gradient seedC seedD i) (SeedOrbit.gradient seedC seedD i)) ∧
    (∀ x : Vec 2, FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch 0) x) ≤ 51 ∧
      FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch 1) x) ≤ 51 * (65/64) ∧
      (51 : ℝ) * (65/64) < 52 ∧
      FrameNorms.euclideanOpNorm (RadialHessian.matrix (DEmbedding.branch 2) x) ≤ 12 ∧
      RadialHessian.matrix (DEmbedding.branch 3) x = 0) ∧
    ∀ (i : Fin 4) (x y : Vec 2), FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (DEmbedding.branch i) x - RadialHessian.matrix (DEmbedding.branch i) y) ≤
        60000 * ‖euclideanVector (x - y)‖ := by
  refine ⟨fun i x => ⟨_, (DScalar.phiSecond_bounds (DEmbedding.parameter_bounds i).1
    (DEmbedding.parameter_bounds i).2 _).1, DEmbedding.branch_old_hessian i x⟩, fun x => ?_,
    DEmbedding.branch_hessian_lipschitz⟩
  obtain ⟨h0, h1, -, h2, h3⟩ := DEmbedding.branch_individual_hessian_bounds x
  exact ⟨h0, h1, by norm_num, h2.le, h3⟩

/-- Item `A/failure/prose/045` (`paper/sections/failure.tex:368-372`): "The first two scalar
arguments are independent, so their coercivity makes every sublevel of $F$ compact.
Nonnegativity and their unique scalar zeros show $F(x)=0$ exactly at $x=0$. At zero the first
three gradients vanish and the last is $(0,1)^T$, giving $F'(0;h)=\max\{0,h_2\}$; thus the
minimizer is nonsmooth." -/
theorem objective_minimizer :
    (∀ a : ℝ, IsCompact {x | DEmbedding.objective x ≤ a}) ∧
    (∀ x, 0 ≤ DEmbedding.objective x) ∧ (∀ x, DEmbedding.objective x = 0 ↔ x = 0) ∧
    (∀ i : Fin 3, HasFDerivAt (DEmbedding.branch i.castSucc) (gradientFunctional 0) 0) ∧
    HasFDerivAt (DEmbedding.branch 3) (gradientFunctional ![0, 1]) 0 ∧
    (∀ h : Vec 2, Tendsto (fun t : ℝ => (DEmbedding.objective (t • h) - DEmbedding.objective 0) / t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1)))) ∧
    ¬ DifferentiableAt ℝ DEmbedding.objective (0 : Vec 2) := by
  refine ⟨DEmbedding.objective_sublevels_compact, DEmbedding.objective_nonnegative,
    DEmbedding.objective_unique_minimum.2.2, fun i => ?_, DEmbedding.branch_last_hasGradient 0,
    DEmbedding.objective_directional_derivative_zero, DEmbedding.objective_not_differentiable_zero⟩
  have h := DEmbedding.branch_old_hasGradient i 0
  have hz : DEmbedding.ridgeGradient (DEmbedding.parameter i) (SeedOrbit.gradient seedC seedD i) 0 = 0 := by
    simp [DEmbedding.ridgeGradient, dot, DEmbedding.phiFirst_zero (DEmbedding.parameter_bounds i).1
      (DEmbedding.parameter_bounds i).2]
  rwa [hz] at h

open DScalarGeometric in
/-- Item `A/failure/prose/046` (`paper/sections/failure.tex:374-375`): "Let
$\bar x_\ell=a_\ell(2,-32)^T$. The first two scalar arguments at $\bar x_\ell$ equal $2a_\ell$,
and the third equals $b_*a_\ell$." -/
theorem center_arguments (ℓ : ℕ) :
    DEmbedding.center ℓ = scale ℓ • ![2, -32] ∧
    dot g0 (DEmbedding.center ℓ) = 2 * scale ℓ ∧ dot g1 (DEmbedding.center ℓ) = 2 * scale ℓ ∧
    dot (g2 seedC seedD) (DEmbedding.center ℓ) = DEmbedding.bStar * scale ℓ :=
  ⟨rfl, DEmbedding.center_argument ℓ 0, DEmbedding.center_argument ℓ 1, DEmbedding.center_argument ℓ 2⟩

open DScalarGeometric in
/-- Item `A/failure/disp/024` (`paper/sections/failure.tex:376-379`), equation
`art:upper_local_model`:
\[ F(\bar x_\ell+h)=a_\ell^3+a_\ell^2G(h)\quad\text{if }|g_i^Th|\le a_\ell/2\quad(i=0,1,2). \] -/
theorem upper_local_model (ℓ : ℕ) (h : Vec 2)
    (hh : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale ℓ / 2) :
    DEmbedding.objective (DEmbedding.center ℓ + h) = (scale ℓ) ^ 3 + (scale ℓ) ^ 2 * objective seedC seedD h :=
  DEmbedding.local_cone ℓ hh

open DScalarGeometric in
/-- Item `A/failure/prose/047` (`paper/sections/failure.tex:380-382`): "Indeed, the first three
branches are on their affine regions and each has value at least $a_\ell^3/2$. The first two
slab inequalities imply $|h_1|\le a_\ell/2$ and $|h_2|\le8a_\ell$, so the fourth branch is
negative." ($h_1$ = `h 0`, $h_2$ = `h 1`.) -/
theorem local_model_branches (ℓ : ℕ) (h : Vec 2)
    (hh : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale ℓ / 2) :
    (∀ i : Fin 3, DEmbedding.branch i.castSucc (DEmbedding.center ℓ + h) =
        (scale ℓ) ^ 3 + (scale ℓ) ^ 2 * dot (SeedOrbit.gradient seedC seedD i) h ∧
      (scale ℓ) ^ 3 / 2 ≤ DEmbedding.branch i.castSucc (DEmbedding.center ℓ + h)) ∧
    |h 0| ≤ scale ℓ / 2 ∧ |h 1| ≤ 8 * scale ℓ ∧ DEmbedding.branch 3 (DEmbedding.center ℓ + h) < 0 :=
  ⟨fun i => ⟨DEmbedding.branch_plateau ℓ i (hh i), DEmbedding.branch_plateau_lower_bound ℓ i (hh i)⟩,
    DEmbedding.slab_horizontal ℓ hh, DEmbedding.slab_vertical ℓ hh, DEmbedding.last_branch_negative ℓ hh⟩

open DScalarGeometric in
/-- Item `A/failure/prose/048` (`paper/sections/failure.tex:383-384`): "In particular
$F(\bar x_\ell)=a_\ell^3$ and $F'(\bar x_\ell;(-1,16)^T)=-a_\ell^2<0$." -/
theorem center_value_slope (ℓ : ℕ) :
    DEmbedding.objective (DEmbedding.center ℓ) = (scale ℓ) ^ 3 ∧
    Tendsto (fun t : ℝ => (DEmbedding.objective (DEmbedding.center ℓ + t • ![-1, 16]) -
      DEmbedding.objective (DEmbedding.center ℓ)) / t) (𝓝[>] 0) (𝓝 (-(scale ℓ) ^ 2)) ∧
    -(scale ℓ) ^ 2 < 0 := by
  refine ⟨DEmbedding.center_value ℓ, ?_, by have := scale_pos ℓ; nlinarith⟩
  have h := DEmbedding.center_directional_derivative ℓ
  simpa [DEmbedding.descentDirection, neg_sq] using h

/-! ### The proof of Theorem `art:local-failure` -/

theorem seedPoint_eq_orbit (m : ℕ) (j : Fin 3) :
    seedRatio ^ m • seedPoint j.castSucc = orbitPoint (3 * m + j) := by
  rw [(orbit_phase_parameters m j).1, seedPoint_castSucc]

open DScalarGeometric in
/-- Item `A/failure/disp/025` (`paper/sections/failure.tex:388-391`), equation `art:upper_orbit`,
in the proof of Theorem `art:local-failure`. For $\ell\ge1$, every $0<c_1\le1/3$,
$c_1<c_2<1$, with $F$ the objective `art:upper_objective`, $x_0^{(\ell)}=\bar x_\ell+a_\ell^2z_0$
and $H_0=I$: the run produced by the specified implementation is unique, and
\[ x_{3m+j}^{(\ell)}=\bar x_\ell+a_\ell^2\rho^mz_j,\qquad H_{3m+j}^{(\ell)}=\rho^mM_j,\qquad j=0,1,2. \] -/
theorem upper_orbit (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 DEmbedding.objective,
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0 ∧ R.H 0 = 1 ∧
      (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ N =
        (some (R.α k), trialHistory (phase k))) ∧
      (∀ R' : AdmissibleBFGSRun 2 DEmbedding.objective,
        R'.x 0 = DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0 → R'.H 0 = 1 →
        (∀ k, ∃ N L, NonStrictLineSearch.fromMetric DEmbedding.objective (R'.x k) (R'.H k) c₁ c₂ N =
          (some (R'.α k), L)) → R'.x = R.x ∧ R'.H = R.H) ∧
      ∀ (m : ℕ) (j : Fin 3),
        R.x (3 * m + j) = DEmbedding.center ℓ + ((scale ℓ) ^ 2 * seedRatio ^ m) • seedPoint j.castSucc ∧
        R.H (3 * m + j) = seedRatio ^ m • metric seedC seedD j := by
  have hx0 : (DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x 0 =
      DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0 := by
    change DEmbedding.center ℓ + (scale ℓ) ^ 2 • orbitPoint 0 = _
    rw [seedPoint_zero_eq]
  have hH0 := DEmbedding.run_initial_matrix hℓ hc₁ hc₁' hc hc₂
  have hs : ∀ k, NonStrictLineSearch.fromMetric DEmbedding.objective
      ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k) ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).H k)
      c₁ c₂ 5 = (some ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).α k), trialHistory (phase k)) :=
    fun k => DNonStrictObjectives.embedding_fromMetric hℓ hc₁ hc₁' hc hc₂ k
  refine ⟨DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂, rfl, rfl, hx0, hH0,
    fun k N hN => fromMetric_fuel_mono (hs k) hN, ?_, fun m j => ?_⟩
  · intro R' hx' hH' hs'
    obtain ⟨h1, h2, -, -⟩ := implemented_run_unique R' (DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂)
      (hx'.trans hx0.symm) (hH'.trans hH0.symm) hs' (fun k => ⟨5, _, hs k⟩)
    exact ⟨h1, h2⟩
  · obtain ⟨hx, hH, -, -⟩ := DEmbedding.run_phase_parameters hℓ hc₁ hc₁' hc hc₂ m j
    refine ⟨hx.trans ?_, hH⟩
    rw [seedPoint_castSucc, smul_smul]

open DScalarGeometric in
/-- Item `A/failure/disp/026` (`paper/sections/failure.tex:396-399`), in the proof of Theorem
`art:local-failure`: for $\ell\ge1$, $m\ge0$, every base query
$z_{\rm trial}=z_j+\alpha p_j$ (a row of Table `art:trial_table`) and $i=0,1,2$,
\[ |g_i^T(a_\ell^2\rho^mz_{\rm trial})|<3a_\ell^2\le3a_\ell/16<a_\ell/2. \] -/
theorem query_slab (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℕ) (q : Fin 9) (i : Fin 3) :
    |dot (SeedOrbit.gradient seedC seedD i) (((scale ℓ) ^ 2 * seedRatio ^ m) •
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)))| < 3 * (scale ℓ) ^ 2 ∧
      3 * (scale ℓ) ^ 2 ≤ 3 * scale ℓ / 16 ∧ 3 * scale ℓ / 16 < scale ℓ / 2 := by
  have ha := scale_pos ℓ
  have ha16 := DEmbedding.scale_le_sixteenth hℓ
  have hρ := pow_pos source_ratio_pos_lt_one.1 m
  have hρ1 : seedRatio ^ m ≤ 1 := pow_le_one₀ source_ratio_pos_lt_one.1.le source_ratio_pos_lt_one.2.le
  have hb := (seed_query_bounds _ (Or.inr ⟨q, rfl⟩)).2.1 i
  refine ⟨?_, by nlinarith, by linarith⟩
  rw [dot_smul_right, abs_mul, abs_of_pos (mul_pos (pow_pos ha 2) hρ)]
  calc (scale ℓ) ^ 2 * seedRatio ^ m * |dot (SeedOrbit.gradient seedC seedD i)
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))|
      ≤ (scale ℓ) ^ 2 * |dot (SeedOrbit.gradient seedC seedD i)
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))| :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg (scale ℓ)) hρ1) (abs_nonneg _)
    _ < (scale ℓ) ^ 2 * 3 := mul_lt_mul_of_pos_left hb (pow_pos ha 2)
    _ = 3 * (scale ℓ) ^ 2 := by ring

open DScalarGeometric in
/-- Item `A/failure/disp/027` (`paper/sections/failure.tex:402-406`), in the proof of Theorem
`art:local-failure`: for $\ell\ge1$, $m\ge0$ and every base query $z_{\rm trial}$ with active
index $i$ (`trialActive`),
\[ F(\bar x_\ell+a_\ell^2\rho^mz_{\rm trial})=a_\ell^3+a_\ell^4\rho^mG(z_{\rm trial}),\qquad
   \nabla F=a_\ell^2g_{\rm active}. \] -/
theorem query_values (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℕ) (q : Fin 9) :
    DEmbedding.objective (DEmbedding.center ℓ + ((scale ℓ) ^ 2 * seedRatio ^ m) •
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))) =
      (scale ℓ) ^ 3 + (scale ℓ) ^ 4 * seedRatio ^ m * objective seedC seedD
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q)) ∧
    HasFDerivAt DEmbedding.objective
      (gradientFunctional ((scale ℓ) ^ 2 • SeedOrbit.gradient seedC seedD (trialActive q)))
      (DEmbedding.center ℓ + ((scale ℓ) ^ 2 * seedRatio ^ m) •
        (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))) := by
  have hρ := pow_pos source_ratio_pos_lt_one.1 m
  have hρ1 : seedRatio ^ m ≤ 1 := pow_le_one₀ source_ratio_pos_lt_one.1.le source_ratio_pos_lt_one.2.le
  have hc := (source_trial_certificate q).toPointCertificate.scale hρ hρ1
  rw [seed_query_eq, ← smul_smul]
  refine ⟨?_, DEmbedding.certified_hasGradient hℓ hc⟩
  rw [DEmbedding.certified_value hℓ hc, objective_scale_at_active (source_trial_certificate q).active hρ]
  ring

/-- The maximum of the Euclidean norms of the three base points $z_0,z_1,z_2$ and the nine
base queries of Table `art:trial_table`. -/
def baseQueryMax : ℝ :=
  max (Finset.univ.sup' Finset.univ_nonempty (fun j : Fin 3 => ‖euclideanVector (seedPoint j.castSucc)‖))
    (Finset.univ.sup' Finset.univ_nonempty (fun q : Fin 9 =>
      ‖euclideanVector (seedPoint (trialPhase q).castSucc + trialLength q • seedDir (trialPhase q))‖))

open DScalarGeometric in
/-- Item `A/failure/disp/028` (`paper/sections/failure.tex:421-423`), in the proof of Theorem
`art:local-failure`: "Since the base query set is finite, the norm of every query is bounded
by
\[ a_\ell\|(2,-32)\|+a_\ell^2\max_{\text{base points and queries}}\|z\|, \]
which tends to zero." For $\ell\ge1$ and every admissible pair, every accepted point and every
query of the $\ell$th run (`DEmbedding.run`, the run of `upper_orbit`) has Euclidean norm at
most this bound, and the bound tends to zero as $\ell\to\infty$. -/
theorem query_norm_bound :
    (∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ),
      ‖euclideanVector ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k)‖ ≤
          scale ℓ * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale ℓ) ^ 2 * baseQueryMax ∧
      ∀ a ∈ trialHistory (phase k),
        ‖euclideanVector ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k + a •
          bfgsStep ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1)‖ ≤
          scale ℓ * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale ℓ) ^ 2 * baseQueryMax) ∧
    Tendsto (fun ℓ => scale ℓ * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale ℓ) ^ 2 * baseQueryMax)
      atTop (𝓝 0) := by
  have hmax : DEuclideanLocality.maxTrialNorm ≤ baseQueryMax := by
    apply le_max_of_le_right
    apply Finset.sup'_le
    intro q _
    have h := Finset.le_sup' (fun q : Fin 9 => ‖euclideanVector (seedPoint (trialPhase q).castSucc +
      trialLength q • seedDir (trialPhase q))‖) (Finset.mem_univ q)
    rw [seed_query_eq] at h
    exact h
  have hbound : ∀ (ℓ : ℕ) (z : Vec 2), ‖euclideanVector z‖ ≤ DEuclideanLocality.maxTrialNorm →
      ‖euclideanVector (DEmbedding.center ℓ + (scale ℓ) ^ 2 • z)‖ ≤
        scale ℓ * ‖euclideanVector (![2, -32] : Vec 2)‖ + (scale ℓ) ^ 2 * baseQueryMax := by
    intro ℓ z hz
    have h := DEuclideanLocality.translated_bound ℓ hz
    simp only [DEuclideanLocality.sourceBound] at h
    have := mul_le_mul_of_nonneg_left hmax (sq_nonneg (scale ℓ))
    linarith
  refine ⟨fun ℓ hℓ c₁ c₂ hc₁ hc₁' hc hc₂ k => ⟨?_, fun a ha => ?_⟩, ?_⟩
  · exact hbound ℓ _ (DEuclideanLocality.orbit_le_max k)
  · obtain ⟨q, hq, rfl⟩ := mem_trialHistory ha
    change ‖euclideanVector (SeedEmbedding.point (DEmbedding.center ℓ) ((scale ℓ) ^ 2) k +
      trialLength q • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale ℓ) ^ 2) k) 1)‖ ≤ _
    rw [SeedEmbedding.translated_trial]
    exact hbound ℓ _ (DEuclideanLocality.actual_trial_le_max k q hq)
  · have h := ((DEmbedding.scale_tendsto.mul_const ‖euclideanVector (![2, -32] : Vec 2)‖).add
      ((DEmbedding.scale_tendsto.pow 2).mul_const baseQueryMax))
    simpa only [zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] using h

/-! ### Scales of the first embedding -/

open DScalarGeometric in
/-- Item `A/failure/prose/038` (`paper/sections/failure.tex:256-261`): "In the first
embedding, the corner's objective height is $a_\ell^3$ and its affine slopes are
$a_\ell^2g_i$. Taking spatial scale $\lambda=a_\ell^2$ gives $\sigma=a_\ell^4=\lambda^2$, so
every copy starts with $I$. Its affine neighborhood has width proportional to $a_\ell$, much
larger than the entire copied trial tree, whose width is proportional to $a_\ell^2$."

For $\ell\ge1$: $F(\bar x_\ell)=a_\ell^3$; at a point $\bar x_\ell+h$ of the open slab
$|g_j^Th|<a_\ell/2$ with strictly active $g_i$ the gradient is $a_\ell^2g_i$; the local model
`art:matched-local-model` holds with $\lambda=a_\ell^2$, $\sigma=a_\ell^4=\lambda^2$,
$C=a_\ell^3$ and $\mathcal G=G$ on the slab $|g_i^T(\lambda z)|\le a_\ell/2$, so
$\lambda^2/\sigma=1$; and every accepted point and query of the copied trial tree of the
$\ell$th run lies in $|g_i^T(x-\bar x_\ell)|<3a_\ell^2<a_\ell/2$. -/
theorem first_embedding_scales (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    DEmbedding.objective (DEmbedding.center ℓ) = (scale ℓ) ^ 3 ∧
    (∀ h : Vec 2, (∀ j : Fin 3, |dot (SeedOrbit.gradient seedC seedD j) h| < scale ℓ / 2) →
      ∀ i : Fin 3, StrictActive seedC seedD h i →
        HasFDerivAt DEmbedding.objective
          (gradientFunctional ((scale ℓ) ^ 2 • SeedOrbit.gradient seedC seedD i)) (DEmbedding.center ℓ + h)) ∧
    (∀ z : Vec 2, (∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) ((scale ℓ) ^ 2 • z)| ≤ scale ℓ / 2) →
      DEmbedding.objective (DEmbedding.center ℓ + (scale ℓ) ^ 2 • z) =
        (scale ℓ) ^ 3 + (scale ℓ) ^ 4 * objective seedC seedD z) ∧
    (scale ℓ) ^ 4 = ((scale ℓ) ^ 2) ^ 2 ∧ ((scale ℓ) ^ 2) ^ 2 / (scale ℓ) ^ 4 = 1 ∧
    (∀ (k : ℕ) (i : Fin 3), |dot (SeedOrbit.gradient seedC seedD i) ((scale ℓ) ^ 2 • orbitPoint k)| <
      3 * (scale ℓ) ^ 2) ∧
    (∀ (k : ℕ) (q : Fin 9), trialPhase q = phase k → ∀ i : Fin 3,
      |dot (SeedOrbit.gradient seedC seedD i) ((scale ℓ) ^ 2 • SeedEmbedding.trialPoint k q)| <
        3 * (scale ℓ) ^ 2) ∧
    3 * (scale ℓ) ^ 2 < scale ℓ / 2 := by
  have ha := scale_pos ℓ
  have ha16 := DEmbedding.scale_le_sixteenth hℓ
  have hbound : ∀ (z : Vec 2) (i : Fin 3), |dot (SeedOrbit.gradient seedC seedD i) z| < 3 →
      |dot (SeedOrbit.gradient seedC seedD i) ((scale ℓ) ^ 2 • z)| < 3 * (scale ℓ) ^ 2 := by
    intro z i hz
    rw [dot_smul_right, abs_mul, abs_of_pos (pow_pos ha 2)]
    nlinarith [pow_pos ha 2]
  refine ⟨DEmbedding.center_value ℓ, fun h hh i hi => DEmbedding.objective_hasGradient_plateau hh hi,
    fun z hz => ?_, by ring, by rw [div_eq_one_iff_eq (by positivity)]; ring, fun k i => hbound _ i ((DEmbedding.orbit_certificate k).branch_bounds i),
    fun k q hq i => hbound _ i ((orbit_trial_point_certificate k q hq).branch_bounds i), by nlinarith⟩
  rw [DEmbedding.local_cone ℓ hz, seed_objective_homogeneous (sq_nonneg _)]
  ring

/-! ### Figure `art:shrinking-scales` -/

open DScalarGeometric in
/-- Item `A/failure/prose/050` (`paper/sections/failure.tex:437-440`), the factual claims of
the caption of Figure `art:shrinking-scales`: "In one fixed objective, bad centers
$\bar x_\ell\to x_*$ have affine-model neighborhoods of width $O(a_\ell)$. Each complete copied
query orbit fits inside a region of size $O(a_\ell^2)$ and converges to $\bar x_\ell$."
Here $x_*=0$; the affine model `art:upper_local_model` holds on the slab
$|g_i^Th|\le a_\ell/2$, which lies in the box $|h_1|\le a_\ell/2$, $|h_2|\le8a_\ell$ and
contains the box $\|h\|_\infty\le a_\ell/6$; for $\ell\ge1$ every accepted point and every
query of the $\ell$th run is within Euclidean distance $a_\ell^2\max_q\|z_q\|$ of
$\bar x_\ell$, and the run converges to $\bar x_\ell$. -/
theorem shrinking_scales :
    Tendsto DEmbedding.center atTop (𝓝 0) ∧
    (∀ (ℓ : ℕ) (h : Vec 2), (∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale ℓ / 2) →
      DEmbedding.objective (DEmbedding.center ℓ + h) = (scale ℓ) ^ 3 + (scale ℓ) ^ 2 * objective seedC seedD h ∧
      |h 0| ≤ scale ℓ / 2 ∧ |h 1| ≤ 8 * scale ℓ) ∧
    (∀ (ℓ : ℕ) (h : Vec 2), ‖h‖ ≤ scale ℓ / 6 →
      ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale ℓ / 2) ∧
    ∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1),
      (∀ k, ‖euclideanVector ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k - DEmbedding.center ℓ)‖ ≤
        (scale ℓ) ^ 2 * DEuclideanLocality.maxTrialNorm) ∧
      (∀ k, ∀ a ∈ trialHistory (phase k),
        ‖euclideanVector ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x k + a •
          bfgsStep ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).H k)
            ((DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).g k) 1 - DEmbedding.center ℓ)‖ ≤
          (scale ℓ) ^ 2 * DEuclideanLocality.maxTrialNorm) ∧
      Tendsto (DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc hc₂).x atTop (𝓝 (DEmbedding.center ℓ)) := by
  have hsc : ∀ (ℓ : ℕ) (z : Vec 2), ‖euclideanVector z‖ ≤ DEuclideanLocality.maxTrialNorm →
      ‖euclideanVector (DEmbedding.center ℓ + (scale ℓ) ^ 2 • z - DEmbedding.center ℓ)‖ ≤
        (scale ℓ) ^ 2 * DEuclideanLocality.maxTrialNorm := by
    intro ℓ z hz
    rw [add_sub_cancel_left, DEuclideanLocality.euclidean_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hz (sq_nonneg _)
  refine ⟨DEmbedding.center_tendsto, fun ℓ h hh => ⟨DEmbedding.local_cone ℓ hh,
    DEmbedding.slab_horizontal ℓ hh, DEmbedding.slab_vertical ℓ hh⟩, fun ℓ h hh i => ?_,
    fun ℓ hℓ c₁ c₂ hc₁ hc₁' hc hc₂ => ⟨fun k => hsc ℓ _ (DEuclideanLocality.orbit_le_max k),
      fun k a ha => ?_, DEmbedding.run_point_tendsto hℓ hc₁ hc₁' hc hc₂⟩⟩
  · have h0 : |h 0| ≤ scale ℓ / 6 := (norm_le_pi_norm h 0).trans hh
    have h1 : |h 1| ≤ scale ℓ / 6 := (norm_le_pi_norm h 1).trans hh
    obtain ⟨c1, c2, d1, d2⟩ := AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1
    have ha := scale_pos ℓ
    rw [abs_le] at h0 h1 ⊢
    fin_cases i <;> simp [SeedOrbit.gradient, g0, g1, g2, dot, Fin.sum_univ_two] <;>
      constructor <;> nlinarith
  · obtain ⟨q, hq, rfl⟩ := mem_trialHistory ha
    change ‖euclideanVector (SeedEmbedding.point (DEmbedding.center ℓ) ((scale ℓ) ^ 2) k +
      trialLength q • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale ℓ) ^ 2) k) 1 -
        DEmbedding.center ℓ)‖ ≤ _
    rw [SeedEmbedding.translated_trial]
    exact hsc ℓ _ (DEuclideanLocality.actual_trial_le_max k q hq)

/-! ### Remarks on Theorem `art:local-failure` -/

open DScalarGeometric in
/-- Item `A/failure/prose/009` (`paper/sections/failure.tex:52-53`): "The failure set supplied by
the theorem is a sequence of starts; it is not a positive-measure basin." The starts
$x_0^{(\ell)}=\bar x_\ell+a_\ell^2z_0$, $\ell\ge1$, of Theorem `art:local-failure` form a
countable set of Lebesgue measure zero. -/
theorem failure_starts_null :
    {x : Vec 2 | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ x = DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0}.Countable ∧
    MeasureTheory.volume
      {x : Vec 2 | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ x = DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0} = 0 := by
  have hc : {x : Vec 2 | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ x = DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0}.Countable :=
    (Set.countable_range fun ℓ : ℕ => DEmbedding.center ℓ + (scale ℓ) ^ 2 • seedPoint 0).mono
      (by
        rintro x ⟨ℓ, -, hx⟩
        exact ⟨ℓ, hx.symm⟩)
  exact ⟨hc, hc.measure_zero _⟩

/-! ### What changes when positive lower curvature is required -/

/-- Item `A/failure/prose/010` (`paper/sections/failure.tex:53-54`) and
Item `A/failure/prose/052` (`paper/sections/failure.tex:450-451`): "There is no uniform positive lower curvature
requirement on these branches." / "The flat affine regions in the first construction explain
why its convex branches have no uniform positive lower curvature." The four branches of
Theorem `art:local-failure` have zero Hessian on the flat affine regions (the open plateaus
around the nodes $\bar x_\ell$, and everywhere for the last branch) and at the minimizer, so no
branch satisfies $\nabla^2f_i\succeq\mu I$ with $\mu>0$. -/
theorem no_uniform_lower_curvature :
    (∀ (ℓ : ℕ) (h : Vec 2), (∀ j : Fin 3, |dot (SeedOrbit.gradient seedC seedD j) h| < DScalarGeometric.scale ℓ / 2) →
      ∀ i : Fin 4, RadialHessian.matrix (DEmbedding.branch i) (DEmbedding.center ℓ + h) = 0) ∧
    (∀ i : Fin 4, RadialHessian.matrix (DEmbedding.branch i) 0 = 0) ∧
    ∀ i : Fin 4, ¬ ∃ μ : ℝ, 0 < μ ∧ ∀ x : Vec 2,
      (RadialHessian.matrix (DEmbedding.branch i) x - μ • (1 : Mat 2)).PosSemidef := by
  have hzero : ∀ i : Fin 4, RadialHessian.matrix (DEmbedding.branch i) 0 = 0 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact DEmbedding.branch_last_hessian 0
    · rw [DEmbedding.branch_old_hessian]
      have hp := DEmbedding.parameter_bounds j
      have h0 : DScalar.phiSecond (DEmbedding.parameter j) (dot (SeedOrbit.gradient seedC seedD j) 0) = 0 := by
        simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        rw [DScalar.phiSecond, DScalar.positiveCurvature_nonpos hp.1 hp.2 le_rfl,
          DScalarNegative.second_eq_zero le_rfl, add_zero]
      rw [h0, zero_smul]
  refine ⟨fun ℓ h hh i => ?_, hzero, fun i ⟨μ, hμ, hpsd⟩ => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · exact DEmbedding.branch_last_hessian _
    · rw [DEmbedding.branch_old_hessian, DEmbedding.translated_argument]
      have hp := DEmbedding.parameter_bounds j
      rw [phiSecond_plateau hp.1 hp.2 ℓ (hh j), zero_smul]
  · have h := (hpsd 0).2 (Pi.single 0 1)
    rw [hzero i, zero_sub] at h
    simp [Matrix.neg_mulVec, Pi.single_apply] at h
    linarith

/-- Item `A/failure/prose/053` (`paper/sections/failure.tex:451-452`): "Adding the same positive
quadratic to each branch restores that curvature": for every $\mu>0$ each branch plus
$\frac\mu2\|x\|^2$ is $\mu$-strongly convex (`FixedNormal.EuclideanStrongConvexOn`:
$f-\frac\mu2\|\cdot\|^2$ is convex). -/
theorem quadratic_restores_curvature (μ : ℝ) (i : Fin 4) :
    FixedNormal.EuclideanStrongConvexOn univ μ (fun x => DEmbedding.branch i x + μ / 2 * sqNorm x) := by
  unfold FixedNormal.EuclideanStrongConvexOn
  simpa only [add_sub_cancel_right] using DEmbedding.branch_convex i

/-- Item `A/failure/prose/054` (`paper/sections/failure.tex:452-453`): "[...] but changes the
dynamics. The old exact cycle can no longer be copied without adjustment." For every $\mu>0$,
the objective $Q_\mu=\frac\mu2\|x\|^2+G$ has gradient $g_0+\mu z_0$ at $z_0$, and no step of
the form $-\alpha(g_0+\mu z_0)$ from $z_0$ (with $H_0=I$) reaches the seed point $z_1$. -/
theorem quadratic_changes_dynamics (μ : ℝ) (hμ : 0 < μ) :
    HasFDerivAt (LQuadraticSeed.objective μ) (gradientFunctional (g0 + μ • seedPoint 0)) (seedPoint 0) ∧
    ∀ α : ℝ, seedPoint 0 + bfgsStep 1 (g0 + μ • seedPoint 0) α ≠ seedPoint 1 := by
  have hz : HasFDerivAt (objective seedC seedD) (gradientFunctional g0) (seedPoint 0) := by
    rw [seedPoint_zero_eq]
    exact orbit_hasGradient 0
  have hq := LQuadraticSeed.quadratic_hasGradient μ (seedPoint 0)
  have h2 : seedPoint 0 1 < 0 := by
    have hρ := source_ratio_pos_lt_one
    obtain ⟨-, -, -, hd⟩ := AlgebraicSeed.box_coarse AlgebraicSeed.root_spec.1
    have hpos : 0 < 1 / (1 - seedRatio) := by
      apply div_pos one_pos
      linarith [hρ.2]
    change (1 / (1 - seedRatio)) * (seedRatio * seedD - 1/64) < 0
    have : seedRatio * seedD < 0 := mul_neg_of_pos_of_neg hρ.1 (by linarith)
    nlinarith
  refine ⟨?_, fun α hα => ?_⟩
  · have h := hq.add hz
    convert h using 1
    ext v
    simp only [gradientFunctional_apply, ContinuousLinearMap.add_apply, dot, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    ring
  · have h1' : seedPoint 1 = seedPoint 0 + seedStep 0 := rfl
    rw [h1'] at hα
    have hs := add_left_cancel hα
    have e0 := congrFun hs 0
    have e1 := congrFun hs 1
    have hb : ∀ i, bfgsStep 1 (g0 + μ • seedPoint 0) α i = -α * (g0 i + μ * seedPoint 0 i) := by
      intro i
      simp [bfgsStep]
    rw [hb] at e0 e1
    have g00 : g0 0 = 1 := rfl
    have g01 : g0 1 = 0 := rfl
    have s00 : seedStep 0 0 = -1 := rfl
    have s01 : seedStep 0 1 = 0 := rfl
    rw [g00, s00] at e0
    rw [g01, s01] at e1
    have hα0 : α = 0 := by
      have : α * (μ * seedPoint 0 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (mul_ne_zero hμ.ne' h2.ne)
    rw [hα0] at e0
    norm_num at e0

/-- Item `A/failure/prose/059` (`paper/sections/failure.tex:485-487`): "Here a classical
Hessian is the derivative of the gradient map, with that map defined in a neighborhood of the
point. A pointwise second-order expansion alone is not the convention."

Convention: $F$ has a classical Hessian at $x$ ($x$ is a twice-differentiable point) when $F$
is differentiable on a neighborhood of $x$ and its derivative map is differentiable at $x$:
`(∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) ∧ DifferentiableAt ℝ (fderiv ℝ F) x`, the form of
"twice-differentiable point" in Theorem `art:local-failure-lower`
(`NegativeLower.local_failure_lower`). Under the neighborhood condition: near $x$ the
gradient map is `coordinateGradient F` ($F$ has gradient `coordinateGradient F z` at every
such $z$); differentiability of the derivative map at $x$ is differentiability of the
gradient map at $x$; and then the Hessian `RadialHessian.matrix F x`, with entries
`fderiv ℝ (fderiv ℝ F) x eᵢ eⱼ`, is symmetric and is the derivative of the gradient map at
$x$. The neighborhood condition is part of the convention: `fderiv` is $0$ wherever $F$ is not
differentiable, so differentiability of `fderiv ℝ F` at $x$ alone gives no gradient map near
$x$. -/
theorem classical_hessian {n : ℕ} (F : Vec n → ℝ) (x : Vec n)
    (hF : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) :
    (∀ᶠ z in 𝓝 x, HasFDerivAt F (gradientFunctional (coordinateGradient F z)) z) ∧
    (DifferentiableAt ℝ (fderiv ℝ F) x ↔ DifferentiableAt ℝ (coordinateGradient F) x) ∧
    (DifferentiableAt ℝ (fderiv ℝ F) x →
      (∀ i j, RadialHessian.matrix F x i j =
        fderiv ℝ (fderiv ℝ F) x (Pi.single i 1) (Pi.single j 1)) ∧
      (RadialHessian.matrix F x).IsSymm ∧
      ∃ L : Vec n →L[ℝ] Vec n, HasFDerivAt (coordinateGradient F) L x ∧
        ∀ v, L v = RadialHessian.matrix F x *ᵥ v) := by
  let E : (Vec n →L[ℝ] ℝ) →L[ℝ] Vec n :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)
  have hcg : coordinateGradient F = fun z => E (fderiv ℝ F z) := by
    funext z
    rfl
  have hfd : fderiv ℝ F = fun z => gradientFunctional (coordinateGradient F z) := by
    funext z
    exact (gradientFunctional_coordinates (fderiv ℝ F z)).symm
  refine ⟨hF.mono fun z hz => hasFDerivAt_coordinateGradient hz, ⟨fun h => ?_, fun h => ?_⟩,
    fun hF2 => ?_⟩
  · rw [hcg]
    exact E.differentiableAt.comp x h
  · rw [hfd]
    have hi : ∀ i, DifferentiableAt ℝ (fun z => coordinateGradient F z i) x :=
      fun i => differentiableAt_pi.1 h i
    simp only [gradientFunctional]
    exact DifferentiableAt.sum fun i _ => (hi i).smul_const _
  have hsymm : ∀ v w : Vec n, fderiv ℝ (fderiv ℝ F) x v w = fderiv ℝ (fderiv ℝ F) x w v :=
    second_derivative_symmetric_of_eventually_of_real (hF.mono fun y hy => hy.hasFDerivAt)
      hF2.hasFDerivAt
  refine ⟨fun i j => rfl, ?_, E.comp (fderiv ℝ (fderiv ℝ F) x), ?_, fun v => ?_⟩
  · ext i j
    exact hsymm _ _
  · rw [hcg]
    exact E.hasFDerivAt.comp x hF2.hasFDerivAt
  · ext i
    have h := AffineWhitening.bilinearMatrix_pairing (fderiv ℝ (fderiv ℝ F) x) (Pi.single i 1) v
    have hd : dot (Pi.single i 1) (RadialHessian.bilinearMatrix (fderiv ℝ (fderiv ℝ F) x) *ᵥ v) =
        (RadialHessian.bilinearMatrix (fderiv ℝ (fderiv ℝ F) x) *ᵥ v) i := by
      simp [dot, Pi.single_apply]
    change fderiv ℝ (fderiv ℝ F) x v (Pi.single i 1) =
      (RadialHessian.bilinearMatrix (fderiv ℝ (fderiv ℝ F) x) *ᵥ v) i
    rw [← hd, h, hsymm]

/-- Item `A/failure/prose/056` (`paper/sections/failure.tex:468-470`): the first row of
Table `art:regularity-map`. "Four convex $C^{2,1}$ branches | $0\preceq\nabla^2f_i\preceq64I$
globally | All branch Hessians exist and are Lipschitz; no uniform positive lower bound." The
accumulation point is the minimizer $0$. -/
theorem regularity_map_first_row :
    (∀ i : Fin 4, ConvexOn ℝ univ (DEmbedding.branch i) ∧ ContDiff ℝ 2 (DEmbedding.branch i)) ∧
    (∀ (i : Fin 4) (x : Vec 2), (RadialHessian.matrix (DEmbedding.branch i) x).PosSemidef ∧
      ((64 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (DEmbedding.branch i) x).PosSemidef) ∧
    (∀ i : Fin 4, DifferentiableAt ℝ (fderiv ℝ (DEmbedding.branch i)) (0 : Vec 2)) ∧
    (∀ (i : Fin 4) (x y : Vec 2), FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (DEmbedding.branch i) x - RadialHessian.matrix (DEmbedding.branch i) y) ≤
        60000 * ‖euclideanVector (x - y)‖) ∧
    ∀ i : Fin 4, ¬ ∃ μ : ℝ, 0 < μ ∧ ∀ x : Vec 2,
      (RadialHessian.matrix (DEmbedding.branch i) x - μ • (1 : Mat 2)).PosSemidef :=
  ⟨fun i => ⟨DEmbedding.branch_convex i, DEmbedding.branch_contDiff i⟩, DEmbedding.branch_hessian_bounds,
    fun i => ((DEmbedding.branch_contDiff i).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) 0, DEmbedding.branch_hessian_lipschitz, no_uniform_lower_curvature.2.2⟩

/-- Item `A/failure/prose/012` (`paper/sections/failure.tex:66`): "The target lengths
$1,1/4,1/16$ fit the bisections of the unit-first search." Starting from $\alpha=1$ with
$\alpha_{\rm lo}=0$, successive Armijo rejections bisect: the $k$th trial is $2^{-k}$, and
$1,1/4,1/16$ are the trials $k=0,2,4$. -/
theorem target_lengths_bisections :
    (∀ k : ℕ, (fun a => NonStrictLineSearch.nextTrial 0 (some a))^[k] 1 = (1/2 : ℝ) ^ k) ∧
    (1 : ℝ) = (1/2) ^ 0 ∧ (1/4 : ℝ) = (1/2) ^ 2 ∧ (1/16 : ℝ) = (1/2) ^ 4 := by
  refine ⟨fun k => ?_, by norm_num, by norm_num, by norm_num⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [NonStrictLineSearch.nextTrial, pow_succ]
    ring

/-! ### Non-vacuity -/

/-- The standing assumptions of this file can all hold at once: the parameter range
$0<c_1\le1/3$, $c_1<c_2<1$ is not empty ($c_1=1/4$, $c_2=1/2$), $b\in\{2,b_*\}$ is satisfied by
$b=2$, the local model of `matched_scaling` holds for $F=\mathcal G=G$, $\bar x=0$, $C=0$,
$\lambda=\sigma=1$ on $U=\mathbb R^2$ with $z=z_0$, $\ell=1\ge1$, and the hypotheses of
`classical_hessian` hold for $F(z)=\|z\|^2$ at $x=0$. -/
example : (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ 1/3 ∧ c₁ < c₂ ∧ c₂ < 1) ∧
    ((2 : ℝ) = 2 ∨ (2 : ℝ) = DEmbedding.bStar) ∧
    (∀ z ∈ (univ : Set (Vec 2)), objective seedC seedD ((0 : Vec 2) + (1 : ℝ) • z) =
      0 + 1 * objective seedC seedD z) ∧
    HasFDerivAt (objective seedC seedD) (gradientFunctional g0) (seedPoint 0) ∧ 1 ≤ 1 ∧
    (∀ᶠ z in 𝓝 (0 : Vec 2), DifferentiableAt ℝ (fun z : Vec 2 => sqNorm z) z) ∧
    DifferentiableAt ℝ (fderiv ℝ (fun z : Vec 2 => sqNorm z)) 0 := by
  have hs : ContDiff ℝ 2 (fun z : Vec 2 => sqNorm z) := by
    unfold sqNorm
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2
  refine ⟨⟨1/4, 1/2, by norm_num, by norm_num, by norm_num, by norm_num⟩, Or.inl rfl,
    fun z _ => by simp, ?_, le_rfl, Eventually.of_forall fun z => (hs.differentiable (by norm_num)) z,
    (hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) 0⟩
  rw [seedPoint_zero_eq]
  exact orbit_hasGradient 0

end BfgsCoverage.Article.Failure
