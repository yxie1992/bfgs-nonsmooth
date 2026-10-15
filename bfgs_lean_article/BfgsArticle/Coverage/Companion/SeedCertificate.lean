import BfgsArticle.Coverage.Article.SeedCertificate
import BfgsVerification.DDisplayPrecision

/-!
# Lean coverage: `companion/appendices/seed_certificate.tex`

Appendix `comp:seed_certificate` of the companion ("The finite rational seed certificate").
Register: `editorial/lean_coverage/register/C_seed_certificate.json`.

The file is generated from the article's appendix `paper/appendices/seed_certificate.tex` by
`editorial/prepare_shared_appendix.py`: $c_\circ,d_\circ$ become $c,d$, the labels are renamed
(`art:` to `comp:`, `art:seed_rho` to `D:rho`, `art:seed_points` to `D:x0`,
`art:failure_update` to `D:bfgs`, `art:seed_matrices` to `D:closure`, `art:trial_table` to
`comp:trial_table`, `art:seed_query_bounds` to `D:trialbounds`), the subsections become sections,
and "Lemma art:seed_cycle" becomes "the seed and query assertions in Chapter D". A companion line
is the article line minus one. Since 15 October 2026 the script also makes five companion-only
replacements (M15, M16, W6, W9 of `TODO_MANUSCRIPT_REVIEW.md`). The items that state the
article's claims word for word are `SAME_AS` the article items in the register (their Lean
statements are in `BfgsCoverage.Article.SeedCertificate`). This module states the claims that
differ.

## Items

| Item | Lines | Lean |
|---|---|---|
| `lemma/comp:root_certificate` | 37-40 | `root_certificate` |
| `prose/008` | 144-145 | `positive_slope_wolfe` |
| `prose/009` | 145-147 | `increase_rejects_armijo` |
| `prose/006` (corrected discrepancy) | 190 | `table_enclosure_widths`, `query_box_too_coarse` |

* Lemma `comp:root_certificate` refers to `D:rho` (`companion/chapters/12_D.tex:99-102`),
  $\rho=129R/(V(U+129))\simeq0.060199206107543764815373666287$, instead of the article's
  `art:seed_rho` ($0.060<\rho<0.061$). "$\simeq$" is read as nearest rounding to the 30 printed
  digits; this holds at every point of the closed box. The printed proof derived only
  $0.060<\rho<0.061$ (a proof gap, not a discrepancy); since 15 October 2026 (wording point W6) it
  ends with "The same interval rules on the root box give the thirty digits in \eqref{D:rho}",
  the rational interval evaluation of $\rho$ on the root box
  (`DDisplayPrecision.raw_bounds_on_original_ball`).
* The search of Chapter D is strict (`DeterministicLineSearch`: $F(x+\alpha p)<F(x)+c_1\alpha g^Tp$,
  $\nabla F(x+\alpha p)^Tp>c_2g^Tp$, `companion/chapters/12_D.tex:41-44`), so prose items 008 and
  009 are stated for the strict tests (the article's versions use the non-strict ones).
* Prose item 006, "The same interval operations give the value enclosures in that table", was a
  discrepancy: the table of Section `comp:trial_table` lists twelve-digit decimals, not
  enclosures, and the query box cannot certify twelve digits (`query_box_too_coarse`; only the much
  smaller root box can). Corrected on 15 October 2026 (M15): "For each trial value
  $G(z_j+\alpha p_j)$ in the table of Section~\ref{comp:trial_table} and each current value
  $G(z_j)$ in the display after it, the same interval operations give a rational enclosure of width
  at most $4\cdot10^{-4}$; the twelve-digit decimals there are explanatory."
  (`table_enclosure_widths`, `BfgsCoverage.Article.SeedCertificate.table_value_enclosures`).
* Prose items 002 ("the next subsection", a section of the companion) and 024
  ("Table~\ref{comp:trial_table}", which prints the section number 12.3) were typos of the
  generator, corrected on 15 October 2026 (M16: "the next section", "the table in
  Section~\ref{comp:trial_table}"); their mathematics is the article's (`clearing_denominators`,
  `query_lower_bounds` in `BfgsCoverage.Article.SeedCertificate`). Prose item 017 says "the third
  gradient $g_2=(c,d)^T$" since the same day (wording point W9; before "the third slope").

## Notation

`Vec 2` carries the sup norm, so `‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30` is the closed
$\ell_\infty$ box of radius $10^{-30}$ around $\bar r$; `x 0`, `x 1` are $(c,d)$.
`AlgebraicSeed.U` … `AlgebraicSeed.Y` are $U,\dots,Y$ and `AlgebraicSeed.P` is $P$ of
`comp:seed_polynomials`. $G$ is `SeedOrbit.objective seedC seedD`, $z_j$ is
`SeedOrbit.point seedC seedD seedRatio j`, $p_j$ is `SeedOrbit.direction seedC seedD seedRatio j`,
the query of a row `q` of the table is `queryPoint seedC seedD seedRatio q` $=z_j+\alpha p_j$.
-/

noncomputable section
open Set Filter Matrix BfgsVerification
open scoped Topology

namespace BfgsCoverage.Companion.SeedCertificate

open AlgebraicSeed SeedCycle SeedOrbit IntervalBounds
open BfgsCoverage.Article.SeedCertificate (queryPoint currentValueExpr trialValueExpr tableCurrent
  tableTrial table_value_enclosures base_gradient query_gradient)

/-! ### Lemma `comp:root_certificate` -/

/-- Item `C/seed_certificate/lemma/comp:root_certificate` (`companion/appendices/seed_certificate.tex:37-40`),
Lemma `comp:root_certificate` (Rational root certificate).

"This closed box contains exactly one root. On the box all of $U,V,R,K,T,Y,U+129$ are positive,
and \eqref{D:rho} holds."

The closed box is $\{x:\|x-\bar r\|_\infty\le10^{-30}\}$ and a root is a zero of $P$.
Equation `D:rho` (`companion/chapters/12_D.tex:99-102`) is
$\rho=129R/(V(U+129))\simeq0.060199206107543764815373666287$; "holds on the box" is read as:
at every point of the box the denominator $V(U+129)$ is positive and $129R/(V(U+129))$ rounds to
the printed thirty digits, $|\rho-0.060199206107543764815373666287|<10^{-30}/2$. The proof
(`C/seed_certificate/proof/001`) ends, since 15 October 2026 (wording point W6), with "The same
interval rules on the root box give the thirty digits in \eqref{D:rho}". -/
theorem root_certificate :
    (∃! x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 ∧ P x = 0) ∧
      ∀ x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 →
        0 < U (x 0) (x 1) ∧ 0 < V (x 0) (x 1) ∧ 0 < R (x 0) (x 1) ∧ 0 < K (x 0) (x 1) ∧
        0 < T (x 0) (x 1) ∧ 0 < Y (x 0) (x 1) ∧ 0 < U (x 0) (x 1) + 129 ∧
        0 < V (x 0) (x 1) * (U (x 0) (x 1) + 129) ∧
        |129 * R (x 0) (x 1) / (V (x 0) (x 1) * (U (x 0) (x 1) + 129)) -
          0.060199206107543764815373666287| < 1 / 10 ^ 30 / 2 := by
  refine ⟨exists_unique_root, fun x hx => ?_⟩
  obtain ⟨hU, hV, hR, hK, hT, hY, hA, -, -⟩ := box_denominators_and_ratio hx
  have hraw := DDisplayPrecision.raw_bounds_on_original_ball hx 0
  have heq : DDisplayRaw.values (x 0) (x 1) 0 =
      129 * R (x 0) (x 1) / (V (x 0) (x 1) * (U (x 0) (x 1) + 129)) := by
    simp only [DDisplayRaw.values, Matrix.cons_val_zero, R, V, U, div_eq_mul_inv]
  rw [heq] at hraw
  have hcor := DDisplayPrecision.corrected_interval 0
  have e1 : DDisplayPrecision.corrected 0 = (0.060199206107543764815373666287 : ℝ) := by
    norm_num [DDisplayPrecision.corrected]
  have e2 : DDisplayPrecision.unit 0 = 1 / 10 ^ 30 := by
    simp [DDisplayPrecision.unit]
  rw [e1, e2] at hcor
  refine ⟨hU, hV, hR, hK, hT, hY, hA, mul_pos hV hA, ?_⟩
  rw [abs_lt]
  constructor <;> linarith [hraw.1, hraw.2, hcor.1, hcor.2]

/-! ### The decisions at the nine queries (strict tests of Chapter D) -/

/-- Item `C/seed_certificate/prose/008` (`companion/appendices/seed_certificate.tex:153-154`): "A
positive derivative at each accepted query supplies weak Wolfe for every permitted curvature
constant." At each accepted row the derivative of $G$ at the query along $p_j$ is positive, and
the strict weak Wolfe test of Chapter D, $\nabla G(z_j+\alpha p_j)^Tp_j>c_2g_j^Tp_j$
(`DeterministicLineSearch.Wolfe`), holds for every $c_2>0$, in particular for every permitted
$c_2\in(c_1,1)$. -/
theorem positive_slope_wolfe (q : Fin 9) (hq : trialAccept q = true) :
    0 < dot (coordinateGradient (SeedOrbit.objective seedC seedD) (queryPoint seedC seedD seedRatio q))
        (SeedOrbit.direction seedC seedD seedRatio (trialPhase q)) ∧
      ∀ c₂ : ℝ, 0 < c₂ → DeterministicLineSearch.Wolfe (SeedOrbit.objective seedC seedD)
        (SeedOrbit.point seedC seedD seedRatio (trialPhase q))
        (SeedOrbit.direction seedC seedD seedRatio (trialPhase q))
        (coordinateGradient (SeedOrbit.objective seedC seedD)
          (SeedOrbit.point seedC seedD seedRatio (trialPhase q))) c₂ (trialLength q) := by
  have h := source_trial_certificate q
  have hl := source_trial_length_pos q
  have hd := h.descent
  have hw := h.wolfe hq
  rw [dot_smul_right] at hd hw
  have hd' : dot (SeedOrbit.gradient seedC seedD (trialPhase q))
      (SeedOrbit.direction seedC seedD seedRatio (trialPhase q)) < 0 := by
    by_contra hc
    nlinarith
  have hw' : 0 < dot (SeedOrbit.gradient seedC seedD (trialActive q))
      (SeedOrbit.direction seedC seedD seedRatio (trialPhase q)) := by
    by_contra hc
    nlinarith
  rw [query_gradient]
  refine ⟨hw', fun c₂ hc₂ => ?_⟩
  unfold DeterministicLineSearch.Wolfe
  rw [base_gradient, show SeedOrbit.point seedC seedD seedRatio (trialPhase q) + trialLength q •
    SeedOrbit.direction seedC seedD seedRatio (trialPhase q) = queryPoint seedC seedD seedRatio q from rfl,
    query_gradient]
  nlinarith

/-- Item `C/seed_certificate/prose/009` (`companion/appendices/seed_certificate.tex:154-156`):
"Strict value increase at each rejected query makes Armijo fail, so the routine reaches exactly the
next displayed bisection." At each rejected row, $G$ at the query exceeds $G(z_j)$, the strict
Armijo test of Chapter D, $G(z_j+\alpha p_j)<G(z_j)+c_1\alpha g_j^Tp_j$
(`DeterministicLineSearch.Armijo`), fails for every $c_1>0$, and the search therefore records the
rejected length and continues with the upper bracket $\alpha$ and the bisection
$(\ell+\alpha)/2$ (`DeterministicLineSearch.search`, for any remaining budget and lower bracket
$\ell$). -/
theorem increase_rejects_armijo (q : Fin 9) (hq : trialAccept q = false) :
    SeedOrbit.objective seedC seedD (SeedOrbit.point seedC seedD seedRatio (trialPhase q)) <
        SeedOrbit.objective seedC seedD (queryPoint seedC seedD seedRatio q) ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ →
        ¬ DeterministicLineSearch.Armijo (SeedOrbit.objective seedC seedD)
          (SeedOrbit.point seedC seedD seedRatio (trialPhase q))
          (SeedOrbit.direction seedC seedD seedRatio (trialPhase q))
          (coordinateGradient (SeedOrbit.objective seedC seedD)
            (SeedOrbit.point seedC seedD seedRatio (trialPhase q))) c₁ (trialLength q) ∧
        ∀ (fuel : ℕ) (l : ℝ) (h : Option ℝ),
          DeterministicLineSearch.search (SeedOrbit.objective seedC seedD)
              (SeedOrbit.point seedC seedD seedRatio (trialPhase q))
              (SeedOrbit.direction seedC seedD seedRatio (trialPhase q))
              (coordinateGradient (SeedOrbit.objective seedC seedD)
                (SeedOrbit.point seedC seedD seedRatio (trialPhase q))) c₁ c₂ (fuel + 1) l h
              (trialLength q) =
            ((DeterministicLineSearch.search (SeedOrbit.objective seedC seedD)
              (SeedOrbit.point seedC seedD seedRatio (trialPhase q))
              (SeedOrbit.direction seedC seedD seedRatio (trialPhase q))
              (coordinateGradient (SeedOrbit.objective seedC seedD)
                (SeedOrbit.point seedC seedD seedRatio (trialPhase q))) c₁ c₂ fuel l
              (some (trialLength q)) ((l + trialLength q) / 2)).1,
              trialLength q :: (DeterministicLineSearch.search (SeedOrbit.objective seedC seedD)
              (SeedOrbit.point seedC seedD seedRatio (trialPhase q))
              (SeedOrbit.direction seedC seedD seedRatio (trialPhase q))
              (coordinateGradient (SeedOrbit.objective seedC seedD)
                (SeedOrbit.point seedC seedD seedRatio (trialPhase q))) c₁ c₂ fuel l
              (some (trialLength q)) ((l + trialLength q) / 2)).2) := by
  have h := source_trial_certificate q
  have hdec := h.decision
  rw [hq] at hdec
  simp only [Bool.false_eq_true, ite_false] at hdec
  have hbase := (source_base_certificate (trialPhase q)).active
  have hinc : SeedOrbit.objective seedC seedD (SeedOrbit.point seedC seedD seedRatio (trialPhase q)) <
      SeedOrbit.objective seedC seedD (queryPoint seedC seedD seedRatio q) := by
    rw [objective_of_active hbase, show queryPoint seedC seedD seedRatio q =
      SeedOrbit.trial seedC seedD seedRatio (trialPhase q) (trialLength q) from rfl,
      objective_of_active h.active]
    exact hdec
  have hd := h.descent
  rw [dot_smul_right] at hd
  refine ⟨hinc, fun c₁ c₂ hc₁ => ?_⟩
  have hna : ¬ DeterministicLineSearch.Armijo (SeedOrbit.objective seedC seedD)
      (SeedOrbit.point seedC seedD seedRatio (trialPhase q))
      (SeedOrbit.direction seedC seedD seedRatio (trialPhase q))
      (coordinateGradient (SeedOrbit.objective seedC seedD)
        (SeedOrbit.point seedC seedD seedRatio (trialPhase q))) c₁ (trialLength q) := by
    unfold DeterministicLineSearch.Armijo
    rw [base_gradient]
    intro ha
    have hneg : c₁ * trialLength q * dot (SeedOrbit.gradient seedC seedD (trialPhase q))
        (SeedOrbit.direction seedC seedD seedRatio (trialPhase q)) < 0 := by
      have := mul_neg_of_pos_of_neg hc₁ hd
      linarith [this]
    change SeedOrbit.objective seedC seedD (queryPoint seedC seedD seedRatio q) < _ at ha
    linarith
  exact ⟨hna, fun fuel l hh => DeterministicLineSearch.search_armijo_reject fuel hna⟩

/-! ### The value enclosures of the table (prose item 006, corrected on 15 October 2026) -/

/-- The value $G(z_0)=g_0^Tz_0$ of the first row ("current" value of phase 0) as a function of
the query-box parameters $(c,d,\rho)$, the article's `currentValueExpr c d r 0`, is
$(897/1024-\rho(1-c))/(1-\rho)$. -/
theorem currentValueExpr_zero (c d r : ℝ) :
    currentValueExpr c d r 0 = (897 / 1024 - r * (1 - c)) / (1 - r) := by
  simp [currentValueExpr, SeedOrbit.gradient, SeedOrbit.point, SeedOrbit.initialPoint, g0, dot,
    Fin.sum_univ_two, trialPhase]

/-- Counterexample to the literal reading of Item `C/seed_certificate/prose/006`
(`companion/appendices/seed_certificate.tex:201`) as printed before its correction of 15 October
2026 (M15): "The same interval operations give the value enclosures in that table." The table of
Section `comp:trial_table` (`companion/chapters/12_D.tex:205-222`) lists twelve-digit decimals
such as $G(z_0)\approx0.888432624149$. Every interval $[\ell,h]$ that encloses $G(z_0)=g_0^Tz_0$, as
a function of the parameters, on the whole query box `comp:query_box` (as any sound evaluation by
the interval rules on that box does) has width $h-\ell>10^{-6}$: the value changes by about
$4.4\cdot10^{-6}$ across the box. So the interval operations on the query box cannot give
twelve-digit enclosures. -/
theorem query_box_too_coarse (lo hi : ℝ)
    (h : ∀ c d r : ℝ, Bounds (318481 / 1000000) c (318482 / 1000000) →
      Bounds (-1025233 / 1000000) d (-1025232 / 1000000) → Bounds (6019 / 100000) r (6021 / 100000) →
      lo ≤ currentValueExpr c d r 0 ∧ currentValueExpr c d r 0 ≤ hi) :
    1 / 10 ^ 6 < hi - lo := by
  have h1 := h (318481 / 1000000) (-1025233 / 1000000) (6019 / 100000)
    ⟨le_rfl, by norm_num⟩ ⟨le_rfl, by norm_num⟩ ⟨le_rfl, by norm_num⟩
  have h2 := h (318481 / 1000000) (-1025233 / 1000000) (6021 / 100000)
    ⟨le_rfl, by norm_num⟩ ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  rw [currentValueExpr_zero] at h1 h2
  norm_num at h1 h2
  linarith [h1.1, h2.2]

/-- Item `C/seed_certificate/prose/006` (`companion/appendices/seed_certificate.tex:201`),
corrected on 15 October 2026 (M15): "For each trial value $G(z_j+\alpha p_j)$ in the table of
Section~\ref{comp:trial_table} and each current value $G(z_j)$ in the display after it, the same
interval operations give a rational enclosure of width at most $4\cdot10^{-4}$; the twelve-digit
decimals there are explanatory." The interval rules on the query box enclose
the values $G(z_j)$ and $G(z_j+\alpha p_j)$ of every row in rational intervals of width at most
$4\cdot10^{-4}$ (the article's enclosures of $10^4G$, `tableCurrent`, `tableTrial`, of widths
$1$ to $4$), and at the root these are the actual values. -/
theorem table_enclosure_widths :
    (∀ c d r : ℝ, Bounds (318481 / 1000000) c (318482 / 1000000) →
      Bounds (-1025233 / 1000000) d (-1025232 / 1000000) → Bounds (6019 / 100000) r (6021 / 100000) →
      ∀ q : Fin 9, (tableCurrent q).1 < 10 ^ 4 * currentValueExpr c d r q ∧
        10 ^ 4 * currentValueExpr c d r q < (tableCurrent q).2 ∧
        (tableTrial q).1 < 10 ^ 4 * trialValueExpr c d r q ∧
        10 ^ 4 * trialValueExpr c d r q < (tableTrial q).2) ∧
    (∀ q : Fin 9, (tableCurrent q).2 - (tableCurrent q).1 ≤ 4 ∧ (tableTrial q).2 - (tableTrial q).1 ≤ 4) ∧
    ∀ q : Fin 9,
      (tableCurrent q).1 < 10 ^ 4 * SeedOrbit.objective seedC seedD
          (SeedOrbit.point seedC seedD seedRatio (trialPhase q)) ∧
      10 ^ 4 * SeedOrbit.objective seedC seedD
          (SeedOrbit.point seedC seedD seedRatio (trialPhase q)) < (tableCurrent q).2 ∧
      (tableTrial q).1 < 10 ^ 4 * SeedOrbit.objective seedC seedD (queryPoint seedC seedD seedRatio q) ∧
      10 ^ 4 * SeedOrbit.objective seedC seedD (queryPoint seedC seedD seedRatio q) < (tableTrial q).2 := by
  refine ⟨table_value_enclosures.1, fun q => ?_, table_value_enclosures.2⟩
  fin_cases q <;> norm_num [tableCurrent, tableTrial]

/-! ### Non-vacuity -/

/-- The hypotheses of this file can hold: there are accepted and rejected rows, and the hypothesis
of `query_box_too_coarse` holds for the article's enclosure $[0.8884,0.8885]$ of $G(z_0)$. -/
example : trialAccept 0 = true ∧ trialAccept 1 = false ∧
    ∀ c d r : ℝ, Bounds (318481 / 1000000) c (318482 / 1000000) →
      Bounds (-1025233 / 1000000) d (-1025232 / 1000000) → Bounds (6019 / 100000) r (6021 / 100000) →
      (8884 / 10 ^ 4 : ℝ) ≤ currentValueExpr c d r 0 ∧ currentValueExpr c d r 0 ≤ 8885 / 10 ^ 4 := by
  refine ⟨rfl, rfl, fun c d r hc hd hr => ?_⟩
  have h := table_value_enclosures.1 c d r hc hd hr 0
  simp only [tableCurrent, Matrix.cons_val_zero] at h
  constructor
  · rw [div_le_iff₀ (by norm_num)]
    linarith [h.1]
  · rw [le_div_iff₀ (by norm_num)]
    linarith [h.2.1]

end BfgsCoverage.Companion.SeedCertificate
