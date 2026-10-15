import BfgsVerification.DNonStrictObjectives
import BfgsVerification.DEuclideanLocality

/-!
# Lean coverage: `paper/statements/negative_upper.tex`

Theorem `art:local-failure` ("Local failure with globally smooth convex branches"),
included in Section `art:failure` (`paper/sections/failure.tex:51`). Register:
`editorial/lean_coverage/register/A_negative_upper.json`. Its proof
(`failure.tex:394-434`) and the construction it uses are covered in
`BfgsArticle.Coverage.Article.Failure`.

## The specified implementation

The theorem is about "the deterministic unit-first bracketing implementation of
Section `art:failure`" (`failure.tex:22-46`). In Lean it is
`NonStrictLineSearch.fromMetric F x H c₁ c₂ N`: at a differentiable point `x` it uses
`g = coordinateGradient F x` ($=\nabla F(x)$) and $p=-Hg$ (`bfgsStep H g 1`), starts with
$\alpha_{\rm lo}=0$, $\alpha_{\rm hi}=+\infty$ (`none`) and trial length $\alpha=1$, tests
the non-strict Armijo inequality first and the non-strict weak Wolfe inequality second
(`NonStrictLineSearch.Armijo`, `NonStrictLineSearch.Wolfe`, display `art:failure_tests`),
sets $\alpha_{\rm hi}=\alpha$ after an Armijo rejection and $\alpha_{\rm lo}=\alpha$ after a
Wolfe rejection, and tries $(\alpha_{\rm lo}+\alpha_{\rm hi})/2$, or $2\alpha_{\rm lo}$
while $\alpha_{\rm hi}=\infty$. It returns `(some α, trials)`: the accepted length and the
list of all trial lengths in order. `N` only bounds the number of trials; by
`fromMetric_fuel_mono` a successful output is the same for every larger `N`.

A run produced by the implementation is an `AdmissibleBFGSRun 2 F` (iterates `x k`,
matrices `H k`, gradients `g k` with `HasFDerivAt F (gradientFunctional (g k)) (x k)`,
lengths `α k`, the step $x_{k+1}=x_k-\alpha_kH_kg_k$ and the full inverse update
`art:failure_update` at every `k`) whose length `α k` is the output of the search at
`(x k, H k)` for every `k`. `implemented_run_unique` shows that such a run is determined
by `(x 0, H 0)`: the implementation is deterministic.

## Notation

`Vec 2 = Fin 2 → ℝ` carries the sup norm; the theorem's norms are Euclidean,
`‖euclideanVector z‖`. `RadialHessian.matrix f x` is the matrix of `fderiv ℝ (fderiv ℝ f) x`;
for the $C^2$ branches $f_i$ (differentiable everywhere, with a differentiable derivative map)
it is the classical Hessian of `failure.tex:493-496`, the derivative of the gradient map
(`BfgsCoverage.Article.Failure.classical_hessian`). $A\succeq0$ is `A.PosSemidef`.
`FrameNorms.euclideanOpNorm` is the Euclidean operator norm.
`ConvexSubdifferential.subdifferential F x` is
$\partial F(x)=\{v:\ F(z)\ge F(x)+v^T(z-x)\ \forall z\}$.

## Items

| Item | Lines | Lean |
|---|---|---|
| `theorem/art:local-failure` (with `disp/001`-`disp/003`) | 1-25 | `local_failure` |

The witnesses are the library's construction: the branches `DEmbedding.branch`, the
objective `DEmbedding.objective` (equation `art:upper_objective`), the centers
`DEmbedding.center ℓ` $=\bar x_\ell=a_\ell(2,-32)^T$ with $a_\ell=16^{-\ell}$, the starts
$x_0^{(\ell)}=\bar x_\ell+a_\ell^2z_0$ and the runs `DEmbedding.run`.
-/

noncomputable section
open Set Filter Matrix BfgsVerification
open scoped Topology

namespace BfgsCoverage.Article.NegativeUpper

open SeedOrbit DScalarGeometric

/-! ### The implementation: trial budget and determinism -/

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

/-- The trial budget `fuel` only bounds the number of trials: a successful output of the
specified search (accepted length and complete trial list) is the output for every larger
budget. -/
theorem fromMetric_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x : Vec n} {H : Mat n} {c₁ c₂ : ℝ}
    {fuel N : ℕ} {b : ℝ} {L : List ℝ}
    (hs : NonStrictLineSearch.fromMetric F x H c₁ c₂ fuel = (some b, L)) (hN : fuel ≤ N) :
    NonStrictLineSearch.fromMetric F x H c₁ c₂ N = (some b, L) := by
  unfold NonStrictLineSearch.fromMetric at hs ⊢
  induction N, hN using Nat.le_induction with
  | base => exact hs
  | succ N _ ih => exact search_fuel_succ N 0 none 1 b L ih

/-- The implementation is deterministic: two full-BFGS runs on the same objective with
the same initial point and matrix whose lengths are the outputs of the specified search
(with any trial budgets) have the same iterates, matrices, gradients and lengths. -/
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

/-! ### Helpers for the construction -/

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

/-! ### Theorem `art:local-failure` -/

/-- Item `A/negative_upper/theorem/art:local-failure` (`paper/statements/negative_upper.tex:1-25`),
Theorem `art:local-failure` (Local failure with globally smooth convex branches), including its
displays Item `A/negative_upper/disp/001` (`paper/statements/negative_upper.tex:4-6`),
Item `A/negative_upper/disp/002` (`paper/statements/negative_upper.tex:10-12`) and
Item `A/negative_upper/disp/003` (`paper/statements/negative_upper.tex:14-18`).

"There are four globally convex functions $f_i\in C^{2,1}(\mathbb R^2)$ such that
\[ 0\preceq\nabla^2f_i(x)\preceq64I\qquad(i=0,1,2,3;\ x\in\mathbb R^2) \]
and $F=\max_if_i$ has compact sublevel sets and a unique nonsmooth minimizer at zero. For
this one objective there are fixed starting points $x_0^{(\ell)}\to0$, all with $H_0=I$,
such that, for every fixed pair $0<c_1\le\frac13$, $c_1<c_2<1$, the deterministic
unit-first bracketing implementation of Section `art:failure` produces infinite full-BFGS
runs satisfying
\[ x_k^{(\ell)}\to\bar x_\ell\ne0,\qquad F(x_k^{(\ell)})\downarrow F(\bar x_\ell)>F(0)=0,
   \qquad 0\notin\partial F(\bar x_\ell). \]
Every queried point is differentiable. Each line search takes at most five trials, and its
accepted lengths repeat $1,1/4,1/16$. The objective, initial points, initial matrix and
complete decision tree are the same throughout the displayed parameter range. The
supremum of the norms of all accepted and rejected query points in the $\ell$th run tends
to zero as $\ell\to\infty$."

Lean form. $C^{2,1}$: `ContDiff ℝ 2` with a globally Lipschitz Hessian (Euclidean operator
norm against the Euclidean distance). $F$ is introduced with its defining equation `hF`.
The runs are indexed by $\ell\ge1$ (as in the proof). The iterates `x ℓ k`, matrices
`H ℓ k`, gradients `g ℓ k`, accepted lengths `α ℓ k`, trial lists `hist ℓ k` (the lengths
of all trials of the `k`th search, in order; the last one is accepted, the others
rejected, so the list is the decision tree of the bracketing search) and the limits
`xbar ℓ` are chosen before $(c_1,c_2)$; for every admissible pair the run
`R : AdmissibleBFGSRun 2 F` with these data is produced by the specified search with
constants $(c_1,c_2)$ and any trial budget $N\ge5$. The queried points of search `k` are
`x ℓ k + a • bfgsStep (H ℓ k) (g ℓ k) 1` $=x_k-aH_kg_k$ for `a ∈ hist ℓ k`; the accepted
one is $x_{k+1}$. "$F(x_k)\downarrow$" is read as strictly decreasing values. The
supremum of the query norms is `sSup` of the set of these Euclidean norms, which is
bounded above. -/
theorem local_failure :
    ∃ f : Fin 4 → Vec 2 → ℝ,
      (∀ i, ConvexOn ℝ univ (f i) ∧ ContDiff ℝ 2 (f i) ∧
        ∃ L : ℝ, ∀ x y : Vec 2, FrameNorms.euclideanOpNorm
          (RadialHessian.matrix (f i) x - RadialHessian.matrix (f i) y) ≤
            L * ‖euclideanVector (x - y)‖) ∧
      (∀ i x, (RadialHessian.matrix (f i) x).PosSemidef ∧
        ((64 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (f i) x).PosSemidef) ∧
      ∀ F : Vec 2 → ℝ, (∀ x, F x = Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)) →
        (∀ a : ℝ, IsCompact {x | F x ≤ a}) ∧
        (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F (0 : Vec 2) ∧
        ∃ (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (g : ℕ → ℕ → Vec 2) (α : ℕ → ℕ → ℝ)
          (hist : ℕ → ℕ → List ℝ) (xbar : ℕ → Vec 2),
          Tendsto (fun ℓ => x ℓ 0) atTop (𝓝 0) ∧ (∀ ℓ, H ℓ 0 = 1) ∧
          (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 → ∀ ℓ, 1 ≤ ℓ →
            ∃ R : AdmissibleBFGSRun 2 F, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
              R.x = x ℓ ∧ R.H = H ℓ ∧ R.g = g ℓ ∧ R.α = α ℓ ∧
              ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric F (x ℓ k) (H ℓ k) c₁ c₂ N =
                (some (α ℓ k), hist ℓ k)) ∧
          (∀ ℓ, 1 ≤ ℓ →
            Tendsto (x ℓ) atTop (𝓝 (xbar ℓ)) ∧ xbar ℓ ≠ 0 ∧
            (∀ k, F (x ℓ (k + 1)) < F (x ℓ k)) ∧
            Tendsto (fun k => F (x ℓ k)) atTop (𝓝 (F (xbar ℓ))) ∧
            F 0 < F (xbar ℓ) ∧ F 0 = 0 ∧
            (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (xbar ℓ) ∧
            (∀ k, ∀ a ∈ hist ℓ k, DifferentiableAt ℝ F (x ℓ k + a • bfgsStep (H ℓ k) (g ℓ k) 1)) ∧
            (∀ k, (hist ℓ k).length ≤ 5) ∧
            (∀ m, α ℓ (3 * m) = 1 ∧ α ℓ (3 * m + 1) = 1/4 ∧ α ℓ (3 * m + 2) = 1/16)) ∧
          (∀ ℓ, BddAbove {r : ℝ | ∃ k, ∃ a ∈ hist ℓ k,
            r = ‖euclideanVector (x ℓ k + a • bfgsStep (H ℓ k) (g ℓ k) 1)‖}) ∧
          Tendsto (fun ℓ => sSup {r : ℝ | ∃ k, ∃ a ∈ hist ℓ k,
            r = ‖euclideanVector (x ℓ k + a • bfgsStep (H ℓ k) (g ℓ k) 1)‖}) atTop (𝓝 0) := by
  refine ⟨DEmbedding.branch, fun i => ⟨DEmbedding.branch_convex i, DEmbedding.branch_contDiff i,
    60000, DEmbedding.branch_hessian_lipschitz i⟩, DEmbedding.branch_hessian_bounds, ?_⟩
  intro F hF
  have hFe : F = DEmbedding.objective := funext hF
  subst hFe
  -- the fixed admissible pair used for statements that do not involve the constants
  have hc : (0 : ℝ) < 1/4 ∧ (1/4 : ℝ) ≤ 1/3 ∧ (1/4 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := by norm_num
  refine ⟨DEmbedding.objective_sublevels_compact, fun x => ?_, fun x hx => ?_,
    DEmbedding.objective_not_differentiable_zero, ?_⟩
  · rw [DEmbedding.objective_zero]
    exact DEmbedding.objective_nonnegative x
  · rw [DEmbedding.objective_zero] at hx
    exact DEmbedding.objective_unique_zero hx
  refine ⟨fun ℓ k => SeedEmbedding.point (DEmbedding.center ℓ) ((scale ℓ) ^ 2) k,
    fun _ k => orbitMetric k, fun ℓ k => SeedEmbedding.gradient ((scale ℓ) ^ 2) k,
    fun _ k => orbitLength k, fun _ k => trialHistory (phase k), DEmbedding.center,
    DEmbedding.initial_points_tendsto, fun _ => ?_, ?_, ?_, ?_⟩
  · change (1 : ℝ) • (1 : Mat 2) = 1
    simp
  · intro c₁ c₂ hc₁ hc₁' hc₁₂ hc₂ ℓ hℓ
    refine ⟨DEmbedding.run hℓ c₁ c₂ hc₁ hc₁' hc₁₂ hc₂, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro k N hN
    exact fromMetric_fuel_mono
      (DNonStrictObjectives.embedding_fromMetric hℓ hc₁ hc₁' hc₁₂ hc₂ k) hN
  · intro ℓ hℓ
    refine ⟨SeedEmbedding.point_tendsto _ _, DEmbedding.center_ne_zero ℓ,
      DEmbedding.run_value_strict_decrease hℓ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2,
      DEmbedding.run_value_tendsto hℓ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2, ?_,
      DEmbedding.objective_zero, DEmbedding.center_nonstationary ℓ, ?_,
      fun k => trialHistory_length_le (phase k), fun m => ?_⟩
    · rw [DEmbedding.objective_zero]
      exact DEmbedding.center_positive ℓ
    · intro k a ha
      obtain ⟨q, hq, rfl⟩ := mem_trialHistory ha
      exact (DEmbedding.run_all_trials_differentiable hℓ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 k q
        hq).differentiableAt
    · obtain ⟨_, _, _, h0⟩ := orbit_phase_parameters m 0
      obtain ⟨_, _, _, h1⟩ := orbit_phase_parameters m 1
      obtain ⟨_, _, _, h2⟩ := orbit_phase_parameters m 2
      exact ⟨by simpa [length] using h0, by simpa [length] using h1, by simpa [length] using h2⟩
  -- the norms of all queries of the `ℓ`th run lie in `[0, sourceBound ℓ]`
  have hmem : ∀ ℓ, ∀ r ∈ {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector
      (SeedEmbedding.point (DEmbedding.center ℓ) ((scale ℓ) ^ 2) k +
        a • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale ℓ) ^ 2) k) 1)‖},
      0 ≤ r ∧ r ≤ DEuclideanLocality.sourceBound ℓ := by
    rintro ℓ r ⟨k, a, ha, rfl⟩
    obtain ⟨q, hq, rfl⟩ := mem_trialHistory ha
    refine ⟨norm_nonneg _, ?_⟩
    rw [SeedEmbedding.translated_trial]
    exact DEuclideanLocality.euclideanLocality.2.1 ℓ k q hq
  have hne : ∀ ℓ, ({r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector
      (SeedEmbedding.point (DEmbedding.center ℓ) ((scale ℓ) ^ 2) k +
        a • bfgsStep (orbitMetric k) (SeedEmbedding.gradient ((scale ℓ) ^ 2) k) 1)‖} :
        Set ℝ).Nonempty := fun ℓ => ⟨_, 0, 1, by simp [trialHistory, phase], rfl⟩
  refine ⟨fun ℓ => ⟨DEuclideanLocality.sourceBound ℓ, fun r hr => (hmem ℓ r hr).2⟩, ?_⟩
  apply squeeze_zero (fun ℓ => ?_) (fun ℓ => csSup_le (hne ℓ) (fun r hr => (hmem ℓ r hr).2))
    DEuclideanLocality.source_bound_tendsto
  obtain ⟨r, hr⟩ := hne ℓ
  exact (hmem ℓ r hr).1.trans (le_csSup ⟨_, fun r hr => (hmem ℓ r hr).2⟩ hr)

/-! ### Non-vacuity -/

/-- The parameter range of the theorem is not empty: $c_1=1/4$, $c_2=1/2$. -/
example : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ 1/3 ∧ c₁ < c₂ ∧ c₂ < 1 :=
  ⟨1/4, 1/2, by norm_num, by norm_num, by norm_num, by norm_num⟩

end BfgsCoverage.Article.NegativeUpper
