import BfgsArticle.LUniformLocal

/-!
# Lean coverage: `paper/statements/negative_lower.tex`

Theorem `art:local-failure-lower` ("Independent local failure with positive lower curvature"),
included in Section `art:failure` (`paper/sections/failure.tex:465`). Register:
`editorial/lean_coverage/register/A_negative_lower.json`.

## Reading of the statement

* `F : Vec 2 → ℝ` is a finite function on `ℝ²`. "Strongly convex" is
  `FixedNormal.EuclideanStrongConvexOn univ κ F` with `κ > 0`, i.e. `F - (κ/2)‖·‖²` is
  convex for the Euclidean norm (`sqNorm`).
* "The deterministic unit-first bracketing implementation of Section `art:failure`" is the
  search of `paper/sections/failure.tex:22-35` (non-strict Armijo `≤` first, weak Wolfe `≥`
  second, lower bracket `0`, upper bracket `+∞`, first trial `1`, bisection after a
  rejection), which is `NonStrictLineSearch.fromMetric F x H c₁ c₂ N`; its value is the
  accepted length and the list of all attempted lengths, `N` bounds the number of trials. A
  full-BFGS run is an `AdmissibleBFGSRun` (actual gradients, the full inverse update
  `inverseBFGS`, no reset). The run is produced by the implementation when every line search
  of the run returns the run's step length for every budget `N ≥ 5` (so the search stops
  within five trials and the budget plays no role, `fromMetric_fuel_mono`):
  `fromMetric F (x k) (H k) c₁ c₂ N = (some (α k), trialHistory (phase k))`, where
  `trialHistory` lists the attempted lengths `[1]`, `[1,1/2,1/4]`, `[1,1/2,1/4,1/8,1/16]`
  of the three phases (Table `art:trial_table`).
* The queries of the `k`th line search are the points `x_k + a p_k`, `p_k = -H_k g_k`
  (`bfgsStep (H k) g 1`), for the attempted lengths `a`; the accepted one is the next iterate.
* `‖·‖` is the Euclidean norm: `‖euclideanVector v‖`.
* A point is twice differentiable when `F` is differentiable near it and its derivative map
  is differentiable there (the convention of `paper/sections/failure.tex:493-496`); the Hessian
  is `RadialHessian.matrix F x`, the matrix of `fderiv ℝ (fderiv ℝ F) x`, and
  `μ I ⪯ ∇²F(x) ⪯ L I` is stated with its quadratic form on a symmetric matrix.

## Items

| Item | Lines | Lean |
|---|---|---|
| `theorem/art:local-failure-lower` (with `disp/001`) | 1-23 | `local_failure_lower` |

The proof assembles the article package theorem `LUniform.uniformSmoothLocalFailure`
(`BfgsArticle/LUniformLocal.lean`), whose objective is the whitened four-branch function
`LUniform.smoothObjective` of Appendix `art:lower_curvature`.
-/

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix BfgsVerification SeedOrbit

namespace BfgsCoverage.Article.NegativeLower

/-! ### Helpers -/

/-- The specified search does not depend on the trial budget once it succeeds: a success
within `fuel` trials is the same success with any larger budget. -/
theorem search_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ : ℝ} :
    ∀ (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a α : ℝ) (hist : List ℝ),
      NonStrictLineSearch.search F x p g c₁ c₂ fuel l h a = (some α, hist) →
      ∀ N, fuel ≤ N → NonStrictLineSearch.search F x p g c₁ c₂ N l h a = (some α, hist) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l h a α hist hs
    rw [NonStrictLineSearch.search] at hs
    exact absurd hs (by simp)
  | succ fuel ih =>
    intro l h a α hist hs N hN
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [NonStrictLineSearch.search] at hs ⊢
    by_cases hA : NonStrictLineSearch.Armijo F x p g c₁ a
    · by_cases hW : NonStrictLineSearch.Wolfe F x p g c₂ a
      · simp only [hA, hW, if_true] at hs ⊢
        exact hs
      · simp only [hA, hW, if_true, if_false] at hs ⊢
        obtain ⟨h1, h2⟩ := Prod.mk_inj.mp hs
        have hr : NonStrictLineSearch.search F x p g c₁ c₂ fuel a h (NonStrictLineSearch.nextTrial a h) =
            (some α, (NonStrictLineSearch.search F x p g c₁ c₂ fuel a h
              (NonStrictLineSearch.nextTrial a h)).2) := Prod.ext h1 rfl
        rw [ih _ _ _ _ _ hr N (by omega), ← h2, ← h1]
    · simp only [hA, if_false] at hs ⊢
      obtain ⟨h1, h2⟩ := Prod.mk_inj.mp hs
      have hr : NonStrictLineSearch.search F x p g c₁ c₂ fuel l (some a)
          (NonStrictLineSearch.nextTrial l (some a)) =
          (some α, (NonStrictLineSearch.search F x p g c₁ c₂ fuel l (some a)
            (NonStrictLineSearch.nextTrial l (some a))).2) := Prod.ext h1 rfl
      rw [ih _ _ _ _ _ hr N (by omega), ← h2, ← h1]

/-- `fromMetric` with any budget at least `fuel` returns a success obtained within `fuel`. -/
theorem fromMetric_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x : Vec n} {H : Mat n} {c₁ c₂ : ℝ}
    {fuel : ℕ} {α : ℝ} {hist : List ℝ}
    (hs : NonStrictLineSearch.fromMetric F x H c₁ c₂ fuel = (some α, hist)) (N : ℕ) (hN : fuel ≤ N) :
    NonStrictLineSearch.fromMetric F x H c₁ c₂ N = (some α, hist) :=
  search_fuel_mono fuel 0 none 1 α hist hs N hN

/-- A real sequence with `a (k+1) < a k` for all `k` is strictly decreasing. -/
theorem strictAnti_of_succ {a : ℕ → ℝ} (h : ∀ k, a (k + 1) < a k) : StrictAnti a :=
  strictAnti_nat_of_succ_lt h

/-- `‖euclideanVector v‖² = sqNorm v`. -/
theorem euclidean_norm_sq (v : Vec 2) : ‖euclideanVector v‖ ^ 2 = sqNorm v :=
  FrameNorms.euclidean_norm_sq (euclideanVector v)

/-- A squared Euclidean Lipschitz bound gives the Euclidean Lipschitz bound. -/
theorem norm_le_of_sqNorm_le {u v : Vec 2} {L : ℝ} (hL : 0 ≤ L)
    (h : sqNorm u ≤ L ^ 2 * sqNorm v) : ‖euclideanVector u‖ ≤ L * ‖euclideanVector v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  rw [mul_pow, euclidean_norm_sq, euclidean_norm_sq]
  exact h

/-- The attempted lengths of phase `j` are the trial lengths `trialLength q` of the queries
`q` of that phase in Table `art:trial_table`. -/
theorem mem_trialHistory_iff (j : Fin 3) (a : ℝ) :
    a ∈ trialHistory j ↔ ∃ q : Fin 9, trialPhase q = j ∧ trialLength q = a := by
  constructor
  · exact trial_history_witness j
  · rintro ⟨q, rfl, rfl⟩
    fin_cases q <;> simp [trialHistory, trialPhase, trialLength]

/-- A choice of a query of every phase: the query `q` in its own phase, the accepted query
elsewhere. -/
def querySelect (q : Fin 9) (k : ℕ) : Fin 9 :=
  if trialPhase q = phase k then q else LNormalizedOracle.acceptedQuery (phase k)

theorem querySelect_phase (q : Fin 9) (k : ℕ) : trialPhase (querySelect q k) = phase k := by
  unfold querySelect
  split_ifs with h
  · exact h
  · exact (LNormalizedOracle.acceptedQuery_spec (phase k)).1

theorem querySelect_self (q : Fin 9) {k : ℕ} (h : trialPhase q = phase k) : querySelect q k = q := by
  simp [querySelect, h]

/-- The value of the whitened four-branch objective at the `m`th center. -/
theorem smooth_center_value (m : ℕ) :
    LUniform.smoothObjective (LUniform.failureCenter m) =
      (LScalarGeometric.scale m) ^ 2 * LEmbedding.offset := by
  change LEmbedding.objective (LUniform.coordinateMatrix.mulVec
    (AffineWhitening.point LUniform.coordinateMatrix (LEmbedding.copyCenter m))) = _
  rw [AffineWhitening.map_point _ LUniform.coordinateMatrix_invertible, LEmbedding.center_value]

/-! ### Theorem `art:local-failure-lower` -/

/-- Item `A/negative_lower/theorem/art:local-failure-lower`, Theorem `art:local-failure-lower`
(`paper/statements/negative_lower.tex:1-23`), including its display
`A/negative_lower/disp/001` (lines 17-20).

"There is a finite strongly convex function $F:\R^2\to\R$ with compact sublevels and a unique
nonsmooth minimizer at zero, with fixed starting points $x_0^{(\ell)}\to0$, all with $H_0=I$,
such that for every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$ the deterministic unit-first
bracketing implementation of Section~\ref{art:failure} produces infinite full-BFGS runs, the
same for every such pair. They converge to nonstationary points $\bar x_\ell\ne0$, with $\bar x_\ell\to0$ and
$F(x_k^{(\ell)})\downarrow F(\bar x_\ell)>F(0)$. Every accepted and rejected query is
differentiable, the accepted lengths repeat $1,1/4,1/16$, and the supremum of all query norms
in the $\ell$th run tends to zero.

The objective can be a maximum of four globally $C^{1,1}$, uniformly strongly convex branches
with globally Lipschitz gradients. There are fixed $0<\underline\mu\le\overline L<\infty$ such
that \[ \underline\mu I\preceq\nabla^2F(x)\preceq\overline L I \quad\text{at every
twice-differentiable point}. \] The first three branches in this construction are not twice
differentiable at zero."

Quantifier order as in the TeX: the objective `F`, its branches `f`, the starts `x₀`, the
iterates `x`, the matrices `H` and the limits `x̄` are chosen first; then for every admissible
pair `(c₁,c₂)` the runs `R ℓ` of the implementation have exactly these iterates and matrices.
The queries of run `ℓ` at step `k` are `x ℓ k + a • p` with `p = -H g`,
`g = coordinateGradient F (x ℓ k)` the actual gradient, and `a` an attempted length; for every
pair the attempted lengths are `trialHistory (phase k)`. -/
theorem local_failure_lower :
    ∃ F : Vec 2 → ℝ,
      -- a finite strongly convex function with compact sublevels
      (∃ κ : ℝ, 0 < κ ∧ FixedNormal.EuclideanStrongConvexOn univ κ F) ∧
      (∀ a : ℝ, IsCompact {x | F x ≤ a}) ∧
      -- and a unique nonsmooth minimizer at zero
      (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F (0 : Vec 2) ∧
      -- fixed starting points `x₀ ℓ → 0`, all with `H₀ = I`, and the runs they produce
      (∃ (x₀ : ℕ → Vec 2) (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (xbar : ℕ → Vec 2),
        Tendsto x₀ atTop (𝓝 0) ∧ (∀ ℓ, x ℓ 0 = x₀ ℓ ∧ H ℓ 0 = 1) ∧
        -- the runs converge to nonstationary points `x̄ ℓ ≠ 0`, `x̄ ℓ → 0`
        (∀ ℓ, Tendsto (x ℓ) atTop (𝓝 (xbar ℓ))) ∧ (∀ ℓ, xbar ℓ ≠ 0) ∧
        (∀ ℓ, (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (xbar ℓ)) ∧
        Tendsto xbar atTop (𝓝 0) ∧
        -- `F(x_k^{(ℓ)}) ↓ F(x̄_ℓ) > F(0)`
        (∀ ℓ, StrictAnti (fun k => F (x ℓ k)) ∧
          Tendsto (fun k => F (x ℓ k)) atTop (𝓝 (F (xbar ℓ))) ∧ F 0 < F (xbar ℓ)) ∧
        -- every accepted and rejected query is differentiable
        (∀ ℓ k, ∀ a ∈ trialHistory (phase k),
          DifferentiableAt ℝ F (x ℓ k + a • bfgsStep (H ℓ k) (coordinateGradient F (x ℓ k)) 1)) ∧
        -- the supremum of all query norms in the `ℓ`th run tends to zero
        (∀ ℓ, BddAbove {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r =
          ‖euclideanVector (x ℓ k + a • bfgsStep (H ℓ k) (coordinateGradient F (x ℓ k)) 1)‖}) ∧
        Tendsto (fun ℓ => sSup {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r =
          ‖euclideanVector (x ℓ k + a • bfgsStep (H ℓ k) (coordinateGradient F (x ℓ k)) 1)‖})
          atTop (𝓝 0) ∧
        -- for every fixed admissible pair the implementation produces these same runs
        ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
          ∃ R : ℕ → AdmissibleBFGSRun 2 F, ∀ ℓ,
            (R ℓ).c₁ = c₁ ∧ (R ℓ).c₂ = c₂ ∧ (R ℓ).x = x ℓ ∧ (R ℓ).H = H ℓ ∧
            (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric F ((R ℓ).x k) ((R ℓ).H k) c₁ c₂ N =
              (some ((R ℓ).α k), trialHistory (phase k))) ∧
            -- the accepted lengths repeat `1, 1/4, 1/16`
            (∀ m, (R ℓ).α (3 * m) = 1 ∧ (R ℓ).α (3 * m + 1) = 1/4 ∧ (R ℓ).α (3 * m + 2) = 1/16)) ∧
      -- a maximum of four globally `C^{1,1}`, uniformly strongly convex branches with globally
      -- Lipschitz gradients, the first three not twice differentiable at zero
      (∃ f : Fin 4 → Vec 2 → ℝ,
        (∀ x, F x = Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)) ∧
        (∀ i, ContDiff ℝ 1 (f i)) ∧
        (∃ L : ℝ, ∀ i y z, ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) z)‖ ≤
          L * ‖euclideanVector (y - z)‖) ∧
        (∃ κ : ℝ, 0 < κ ∧ ∀ i, FixedNormal.EuclideanStrongConvexOn univ κ (f i)) ∧
        ∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (f i.castSucc)) (0 : Vec 2)) ∧
      -- fixed `0 < μ ≤ L < ∞` with `μ I ⪯ ∇²F(x) ⪯ L I` at every twice-differentiable point
      ∃ μl Lu : ℝ, 0 < μl ∧ μl ≤ Lu ∧ ∀ x : Vec 2,
        (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) → DifferentiableAt ℝ (fderiv ℝ F) x →
        (RadialHessian.matrix F x).IsSymm ∧ ∀ v,
          μl * sqNorm v ≤ dot v ((RadialHessian.matrix F x).mulVec v) ∧
          dot v ((RadialHessian.matrix F x).mulVec v) ≤ Lu * sqNorm v := by
  obtain ⟨hκ, horder, hgeom, hbranch, hmax, hhess, hnot2, htarget, hcenters⟩ :=
    LUniform.uniformSmoothLocalFailure
  obtain ⟨_hconv, hstrong, hF0, hlower, hzero, hcompact, _hcoercive, hnonsmooth⟩ := hgeom
  obtain ⟨x, H, g, hH0, hx0, hruns⟩ := htarget
  set F := LUniform.smoothObjective with hFdef
  -- one admissible pair, used to read off the pair-independent properties of `x`, `H`
  obtain ⟨R₀, hR₀, hloc₀⟩ := hruns (1/10000) (1/2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hmin : ∀ y, F 0 ≤ F y := by
    intro y
    rw [hF0]
    exact (mul_nonneg (div_nonneg hκ.le (by norm_num)) (sqNorm_nonneg y)).trans (hlower y)
  have hcenter (ℓ : ℕ) : F (LUniform.failureCenter ℓ) = (LScalarGeometric.scale ℓ) ^ 2 * LEmbedding.offset :=
    smooth_center_value ℓ
  have hcenter_pos (ℓ : ℕ) : 0 < (LScalarGeometric.scale ℓ) ^ 2 * LEmbedding.offset :=
    mul_pos (sq_pos_of_pos (LScalarGeometric.scale_pos ℓ)) LEmbedding.offset_pos
  -- the actual gradients of the run
  have hgrad (ℓ k : ℕ) : coordinateGradient F (x ℓ k) = g ℓ k := by
    obtain ⟨hx, -, hg, -⟩ := hR₀ ℓ
    rw [← hx, ← hg]
    exact DeterministicLineSearch.actual_coordinateGradient ((R₀ ℓ).hasGradient k)
  -- queries of every phase, through `trialHistory`
  have hquery (ℓ k : ℕ) (a : ℝ) (ha : a ∈ trialHistory (phase k)) :
      ∃ q : Fin 9, trialPhase q = phase k ∧ trialLength q = a :=
    (mem_trialHistory_iff (phase k) a).mp ha
  refine ⟨F, ⟨LUniform.lowerConstant, hκ, hstrong⟩, hcompact, hmin, ?_, hnonsmooth, ?_, ?_, ?_⟩
  · intro y hy
    rw [hF0] at hy
    exact hzero y hy
  · refine ⟨fun ℓ => x ℓ 0, x, H, LUniform.failureCenter, hx0, fun ℓ => ⟨rfl, hH0 ℓ⟩, ?_, ?_, ?_,
      hcenters, ?_, ?_, ?_, ?_, ?_⟩
    · intro ℓ
      obtain ⟨hx, -, -, hrun⟩ := hR₀ ℓ
      rw [← hx]
      exact hrun.2.2.1
    · intro ℓ hz
      have h := hcenter ℓ
      rw [hz, hF0] at h
      exact (hcenter_pos ℓ).ne' h.symm
    · intro ℓ
      obtain ⟨-, -, -, -, -, -, -, -, -, hnon, -⟩ := hR₀ ℓ
      exact hnon
    · intro ℓ
      obtain ⟨hx, -, -, hrun⟩ := hR₀ ℓ
      obtain ⟨-, -, -, -, hval, -, -, hstep, -, -⟩ := hrun
      refine ⟨?_, ?_, ?_⟩
      · rw [← hx]
        exact strictAnti_of_succ fun k => (hstep k).2.1
      · rw [← hx, hcenter ℓ]
        exact hval
      · rw [hcenter ℓ, hF0]
        exact hcenter_pos ℓ
    · intro ℓ k a ha
      obtain ⟨q, hq, rfl⟩ := hquery ℓ k a ha
      obtain ⟨hx, hH, hg, hrun⟩ := hR₀ ℓ
      have h := (hrun.2.2.2.2.2.2.2.2.1 k q hq).1
      rw [hx, hH, hg] at h
      rw [hgrad ℓ k]
      exact h
    · -- each run's queries are bounded: every query sequence converges
      intro ℓ
      obtain ⟨hx, hH, hg, hrun⟩ := hR₀ ℓ
      have hlim := hrun.2.2.2.2.2.2.2.2.2
      have hb (q : Fin 9) : ∃ B : ℝ, ∀ k, ‖euclideanVector (x ℓ k + trialLength (querySelect q k) •
          bfgsStep (H ℓ k) (g ℓ k) 1)‖ ≤ B := by
        have ht := hlim (querySelect q) (querySelect_phase q)
        rw [hx, hH, hg] at ht
        have hc : Tendsto (fun k => ‖euclideanVector (x ℓ k + trialLength (querySelect q k) •
            bfgsStep (H ℓ k) (g ℓ k) 1)‖) atTop
            (𝓝 ‖euclideanVector (LUniform.failureCenter ℓ)‖) :=
          ((PiLp.continuous_equiv_symm 2 _).tendsto _ |>.comp ht).norm
        obtain ⟨B, hB⟩ := hc.bddAbove_range
        exact ⟨B, fun k => hB ⟨k, rfl⟩⟩
      choose B hB using hb
      refine ⟨Finset.univ.sup' Finset.univ_nonempty B, ?_⟩
      rintro r ⟨k, a, ha, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hquery ℓ k a ha
      have h := hB q k
      rw [querySelect_self q hq] at h
      rw [hgrad ℓ k]
      exact h.trans (Finset.le_sup' B (Finset.mem_univ q))
    · -- uniform locality gives the limit of the suprema
      rw [Metric.tendsto_atTop]
      intro ε hε
      let U : Set (Vec 2) := {v | ‖euclideanVector v‖ < ε / 2}
      have hU : U ∈ 𝓝 (0 : Vec 2) := by
        apply IsOpen.mem_nhds
        · exact isOpen_lt ((PiLp.continuous_equiv_symm 2 _).norm) continuous_const
        · change ‖euclideanVector (0 : Vec 2)‖ < ε / 2
          rw [show euclideanVector (0 : Vec 2) = 0 from rfl, norm_zero]
          linarith
      obtain ⟨N, hN⟩ := hloc₀ U hU
      refine ⟨N, fun ℓ hℓ => ?_⟩
      obtain ⟨hx, hH, hg, -⟩ := hR₀ ℓ
      set S : Set ℝ := {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r =
        ‖euclideanVector (x ℓ k + a • bfgsStep (H ℓ k) (coordinateGradient F (x ℓ k)) 1)‖}
      have hmem : ∀ r ∈ S, 0 ≤ r ∧ r < ε / 2 := by
        rintro r ⟨k, a, ha, rfl⟩
        refine ⟨norm_nonneg _, ?_⟩
        obtain ⟨q, hq, rfl⟩ := hquery ℓ k a ha
        have h := (hN ℓ hℓ k).2 q hq
        rw [hx, hH, hg] at h
        rw [hgrad ℓ k]
        exact h
      have hne : S.Nonempty := ⟨_, 0, 1, by simp [trialHistory, phase], rfl⟩
      have hle : sSup S ≤ ε / 2 := csSup_le hne fun r hr => (hmem r hr).2.le
      have hge : 0 ≤ sSup S := by
        obtain ⟨r, hr⟩ := hne
        exact (hmem r hr).1.trans (le_csSup ⟨ε / 2, fun s hs => (hmem s hs).2.le⟩ hr)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hge]
      linarith
    · intro c₁ c₂ hc₁ hc₁' hc hc₂
      obtain ⟨R, hR, -⟩ := hruns c₁ c₂ hc₁ hc₁' hc hc₂
      refine ⟨R, fun ℓ => ?_⟩
      obtain ⟨hx, hH, -, hrun⟩ := hR ℓ
      obtain ⟨h1, h2, -, -, -, -, -, hstep, -, -⟩ := hrun
      refine ⟨h1, h2, hx, hH, fun k N hN => fromMetric_fuel_mono (hstep k).2.2.2.1 N hN, fun m => ?_⟩
      have hα (k : ℕ) := (hstep k).2.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hα]
        simp [phase, SeedOrbit.length, Nat.mul_mod_right]
      · rw [hα]
        have : (3 * m + 1) % 3 = 1 := by omega
        simp [phase, SeedOrbit.length, this]
      · rw [hα]
        have : (3 * m + 2) % 3 = 2 := by omega
        simp [phase, SeedOrbit.length, this]
  · refine ⟨LUniform.smoothBranch, hmax, fun i => (hbranch i).1, ?_,
      ⟨LUniform.lowerConstant, hκ, fun i => (hbranch i).2.1⟩, hnot2⟩
    refine ⟨LUniform.upperConstant, fun i y z => ?_⟩
    rw [DeterministicLineSearch.actual_coordinateGradient ((hbranch i).2.2.1 y),
      DeterministicLineSearch.actual_coordinateGradient ((hbranch i).2.2.1 z)]
    exact norm_le_of_sqNorm_le LUniform.upperConstant_pos.le ((hbranch i).2.2.2 y z)
  · exact ⟨LUniform.lowerConstant, LUniform.upperConstant, hκ, horder, hhess⟩

end BfgsCoverage.Article.NegativeLower
