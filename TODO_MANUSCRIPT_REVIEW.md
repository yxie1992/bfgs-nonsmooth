# TODO: Manuscript review

Review date: 13 October 2026. Reviewer: AI assistant (Claude), at the author's request.

Scope: notation, typesetting and claim wording in the article (`paper/`) and, from
M12 on and in the W items, in the companion (`companion/`). The seed
numerics were re-checked in the first reading and all matched. Unless an item says
otherwise, no mathematical statement and no Lean declaration changed.

**Status (15 October 2026):** M1 to M41 are resolved: M1 to M6 on 13 October; M7 to
M11 in the article and M12 to M29, with the companion's recurrences of M8, on 15
October, after the Lean coverage; M30 to M41, found by the line-by-line reading of the
article, also on 15 October. The companion's wording points W1 to W11 and W14 to W47
were applied on 15 October; W12 and W13 are left for the author. Open: the questions
for the author below (step 3 of the plan in `AGENTS.md`).

## Questions for the author (step 3)

Decisions the agents left to the author. Everything else found so far is corrected
(see "Resolved").

- [ ] **Q1: The AI-use statement (M37).** `companion/master.tex:63-64` and
  `editorial/AI_AND_AUTHOR_ACTIONS.md` now say that, from October 2026, Anthropic
  Claude (in OpenCode) assisted the work (the Lean review, the Lean coverage, the
  reviews and the corrections). Confirm or change the wording.
- [ ] **Q2: The coverage registers in the article (M36).** Section 7 now names the
  compiler, axiom and kernel-replay audits. Should it also say that every claim of the
  article is classified, with its Lean statement, in the coverage registers
  (`editorial/lean_coverage/`)?
- [ ] **Q3: Order of the article's reference list (M40).** Keep it, or sort it
  alphabetically.
- [ ] **Q4: Edition date.** Set on 15 October 2026 (step 2 of the release run) to the
  planned freeze date: both documents now print "Author-review edition, 15 October
  2026" (`paper/master.tex`, `companion/master.tex`, the companion's footers in
  `companion/preamble.tex`), as decision D1 of `editorial/release_plan_20261015/PLAN.md`
  proposed. The author may choose another date; if the freeze moves to another day,
  the date is changed again before the `--write` of `editorial/release_20261015/`.
- [ ] **Q5: W12 and W13.** The redundant compactness hypothesis of Theorem 11.1 and
  the gaps in the companion's section numbers were left as they are (see "Wording
  points in the companion").
- [ ] **Q6: Optional points not applied.** In the companion: `09_C.tex:451` "The
  radial numerator tends to …" (the chapter never names $N$; possible "The radial
  numerator $N=y^Tz$ tends to"); "structural region" at `research_story.tex:26` and
  `03_T.tex:178` (used consistently there); "noncritical" at `09_C.tex:398` and `463`
  (defined in context at 463). The uses of "every scale" (`13_L.tex:343`) and of
  "accumulation point" (`12_D.tex:380`, `13_L.tex:301`) are correct. In the article,
  reader points left with a reason (`editorial/line_by_line_reading_20261015/`): R-D-3
  (d) ($t$ as a level is the convention of Section 5.2 and Appendix B), R-D-3 (e) (the
  corner index $j$ does not occur in the secant paragraph), R-E-8 (e) (the inset of
  Figure 3 is schematic), R-E-9 (e) (the ramp coordinate lives in another subsection),
  and R-D-4 for Theorems 5 and 8 (the layout gets worse).
- [ ] **Q7: Typesetting points from the release visual review (15 October 2026).**
  Three visual-review agents looked at every page of the release PDFs, built at
  `2cfa27a` (the documents' text is unchanged at `8ca8bac`): V1 the article, V2 and V3
  the companion (PDF pages 1–56 and 57–108). They checked the edition date "15 October
  2026" on both title pages and in every footer of the companion, the page numbers,
  running heads and cross-references, and found no clipped or overfull text. None of
  the points below is blocking. They are left for a later edition: most fixes would
  change sources that the release checks pin (the receipt of
  `editorial/release_20261015/` and, through the coverage registers and the claim
  ledger, the Lean evidence of `2cfa27a`), so steps 4 to 6 of the release run
  (`editorial/release_20261015/README.md`, "Run order") would have to be repeated.
  Only the fixes for Figure 3 of the article (drawn by
  `paper/figures/generate_figures.py`) and for the companion's contents and
  bibliography touch files that have no register and are not in the receipt. For the
  two points on companion PDF page 94, the printed-count check of
  `editorial/verify_release_inputs.py` looks for the strings `checked <n> Lean names`
  and `(<m> modules;` literally, so "5,420" or a tie `783~modules` would need that
  check changed as well.
  - Article (V1; PDF pages):
    - p. 4, Figure 1(b): the vertical axis runs through the origin label 0, which
      reads like a slashed zero or a phi (already so on 13 September). Fix:
      `paper/figures/gradient_geometry.tex:22`, place the label as in panel (a), e.g.
      `\node[above left] at (0,0) {$0$};`, or end the vertical axis below the label.
    - p. 18, paragraph "For a concrete reduction", above (17): the inline set $I_0$
      breaks across lines after "$i:$" (already so on 13 September). Fix: keep it
      together, `\mbox{$I_0=\{i:x_{*,i}=0\}$}`, at `paper/sections/local.tex:119`.
    - p. 20, last display of the page, in the proof of Theorem 8
      ($E_{k+1}=\dots\le(1+Ld_k)(E_k-m/q_k)+C$): it runs from margin to margin, and
      the spaces around $+$ and $-$ shrink to nothing, though no box is overfull
      (already so on 13 September). Fix: `paper/sections/local.tex:264-269`, break
      it before the $\le$ with `aligned`.
    - p. 20, paragraph above that display, in wording edited in October: the line
      "Compactness implies $\operatorname{dist}(x_k,\Gamma)\to0$; with $s_k\to0$ and
      $d_k\to0$, these" is loose, with wide spaces between words. Fix:
      `paper/sections/local.tex:261`, rephrase slightly (e.g. "Since $s_k\to0$ and
      $d_k\to0$, compactness gives $\operatorname{dist}(x_k,\Gamma)\to0$ and these
      estimates …") or accept.
    - p. 24, display (19), the full inverse update (Section 6.1): it fills the line
      and its number drops to a line of its own (already so on 13 September; display
      (1) on p. 4, the same case, was fixed in this edition). Fix:
      `paper/sections/failure.tex:40-45`, take $s=-\alpha Hg$, $y=g^+-g$ out of the
      numbered line, onto a second line (`multline` or `split`) or into the text
      after the display.
    - pp. 26, 35, 38 and 44: in four 2×2 matrices the columns are only about 3pt
      apart (svjour3 sets `\arraycolsep` to 1.5pt), so a row reads almost like one
      expression or a product: $M_1$ in (21), first row "129/256 −1/16" (p. 26;
      already so on 13 September); the matrix in $Z^TFZ=A-\dots$ in the proof of
      Lemma 6 (p. 35); $Dw$ below (41) (p. 38); $M(\zeta,\eta)$ before (49) (p. 44).
      Fix: a wider gap, e.g. `{\arraycolsep=5pt\begin{pmatrix}…\end{pmatrix}}`, at
      `paper/sections/failure.tex:89`, `paper/appendices/matrix_algebra.tex:31`,
      `planar_geometry.tex:118` and `lower_curvature.tex:63`, or `\arraycolsep` set
      once for every `pmatrix`.
    - p. 28, after the proof of Corollary 8: the paragraph "This already excludes
      global convergence …" has no indent, the only paragraph after a proof without
      one (already so on 13 September). Fix: a blank line between `\end{proof}` and
      that paragraph (`paper/sections/failure.tex:226-227`).
    - p. 32, Figure 3, right panel (enlarged affine-model neighborhood): the right
      edge of the dotted box runs through the label $x_0^{(\ell)}$, and $\bar x_\ell$
      is drawn over its lower-left corner, so both look garbled at normal size
      (already so on 13 September). Fix: `paper/figures/generate_figures.py:142-143`
      (it generates `shrinking_scales.tex`), move both labels outside the box (e.g.
      `node[below left=2pt]` for $\bar x_\ell$, `node[right=4pt]` for $x_0^{(\ell)}$)
      and rerun the figure build.
    - p. 38, paragraph "Transport charged to decrease" and the paragraph after (42),
      in wording edited in October: loose lines with stretched spaces around "=",
      the two from "Write $q(\theta)=x+\theta s$" to "and $D(\theta)=$" and the line
      "Since $D'(\theta)=\det(s,Dw\,s)$ there, …". Fix:
      `paper/appendices/planar_geometry.tex:144-154`, rephrase slightly (e.g. the
      parenthesis about $\theta$ as a sentence of its own) or accept.
    - p. 41, Section C.2, first three lines of the proof of the algebraic part of
      Lemma 4, in wording edited in October: very loose, with wide gaps, especially
      around "=" in "$\mathcal B(I,g_0,g_1,1)=M_1$, is immediate from $s_0=(-1,0)^T$
      and $g_1-g_0=$". Fix: `paper/appendices/seed_certificate.tex:99` (shared with
      the companion through `editorial/prepare_shared_appendix.py`), rephrase so that
      the formulas break better (e.g. "From $s_0=(-1,0)^T$ and $g_1-g_0=(-2,-1/8)^T$,
      the first update of the cycle is immediate: $\mathcal B(I,g_0,g_1,1)=M_1$.") or
      accept.
    - p. 42, end of the same proof, paragraph "This gives the matrix and displacement
      closures", lines 2–3, in wording edited in October: two loose lines with
      stretched spaces around "=" ("$s_j=-\alpha_jM_jg_j$ with $\alpha_0=1$, …").
      Fix: `paper/appendices/seed_certificate.tex:140` (shared with the companion),
      rephrase slightly or accept.
    - p. 44, Section D.1: the display
      $\bar g=(1,-16)^T/257=\frac{129}{257}g_0+\frac{128}{257}g_1$ between "The
      vector" and "is the least-norm point …" has almost no space below it, and its
      fractions nearly touch the next line (already so on 13 September). Fix:
      `paper/appendices/lower_curvature.tex:30-35`, lengthen the lead-in (e.g. "The
      vector $\bar g$ defined by"), or end the display with a comma and go on with
      "which is …"; a gap of `\belowdisplayskip` would also do.
  - Companion (V2 and V3; PDF pages):
    - p. 6, Contents: the last entry is Appendix B (printed page 97); the bibliography
      (PDF p. 105, printed 99) has no entry (already so on 13 September). Fix
      (optional): `\addcontentsline{toc}{chapter}{Bibliography}` before the
      bibliography, or the class's option for a bibliography entry in the contents.
    - p. 14, "Relation to earlier work", second paragraph: the date breaks after
      "through 11", and "September 2026" starts the next line (already so on 13
      September). Fix: a tie, `11~September 2026`.
    - p. 38, Section 5.7 (continued): the display of $d$, $\Delta$ and $t$, an
      `align*` with three column pairs, spreads over the full width with a large gap
      above it, while the line of $g_x$, $g_z$, $y$ just above is compact; it looks
      detached (already so on 13 September). Fix: through the generator's
      transformations (`companion/chapters/05_G.tex:311-315`), one display with
      `\quad` separators, or a `gather*` with the $g_x$ line.
    - p. 38, "Relation to earlier work", second paragraph: the range breaks after the
      en dash, "Lemmas 2.2–" / "2.3." (already so on 13 September). Fix:
      `Lemmas~\mbox{2.2--2.3}`, through the generator's transformations.
    - pp. 49 and 50, Sections 7.6 and 7.7.3: "Theorem" ends a line and its number,
      "7.B." and "7.C.", starts the next (already so on 13 September). Fix: ties,
      `Theorem~7.B` and `Theorem~7.C`, through the generator's transformations.
    - p. 76 (printed 70): about five empty lines at the foot of the page, mid-chapter.
      The edited last paragraph gained a line, so the heading of Section 11.7.1, its
      two-line paragraph and the $P(t)$, $Q(t)$ display moved to p. 77 (on 13
      September they ended p. 76). Fix: none needed; if wanted, shorten the paragraph
      "This is a function-class gain beyond RS …" by one line in its transformation.
    - p. 94 (printed 88), "The October 2026 Lean review": "checked 5420 Lean names"
      has no thousands separator, unlike every other count of four or more digits in
      Chapter 14 (9,672; 31,960; …). Fix: "5,420" at
      `companion/current_verification.tex:8`, with the release check changed (see
      above), or leave it.
    - p. 94 (printed 88), same section, last two lines: "(783" ends a line and
      "modules;" starts the next. Fix: a tie, `(783~modules;`, at
      `companion/current_verification.tex:11`, with the release check changed (see
      above).
    - p. 95 (printed 89), Section 14.2: the Record/Meaning register table now breaks
      after its second row, with the header and two rows at the foot of the page and
      the header again with four rows on p. 96 (on 13 September the table was on one
      page); readable, nothing lost. Fix: none needed; if wanted, keep the six rows
      together (start the table on p. 96 or let it float).
    - pp. 98–99 (printed 92–93), Section 14.5: the page break splits the two-line
      command block of the read-only validators
      (`validate_report_reconstruction_19.py` / `verify_report_claim_review_20.py`;
      on one page on 13 September), although p. 99, where Chapter 14 now ends, has
      room. Fix: keep the block together, e.g. `\needspace{3\baselineskip}` before
      "The earlier source/correspondence records also have read-only validators:",
      through the generator's transformation of `chapters/14_E.tex`.
    - p. 106 (printed 100), bibliography entry [13] (Griewank): the opening quotation
      mark before "semi-smooth" has no closing one (already so on 13 September).
      Fix: add `''` after `semi-smooth` in `\bibitem{GR91}` of
      `companion/bibliography.tex`.
    - p. 106 (printed 100), entry [16] (Powell): an explicit `\par` after the title
      splits the entry into two paragraphs, with a blank line inside it (already so
      on 13 September). Fix: remove that `\par` in `\bibitem{FND_P76}` of
      `companion/bibliography.tex`, so that the entry runs on ("… exact line
      searches. In R. W. Cottle …").

## Wording points in the companion (no discrepancy)

Found by the companion coverage and its reviews. Each statement is true as intended,
so its register item is not a `DISCREPANCY`, but a hypothesis is left implicit, a
symbol is undefined, a sentence is an editorial remnant or a printed proof shows less
than its statement (Lean proves the statement). W1 to W11 and W14 to W46 were applied
on 15 October 2026 with the companion corrections, and W47 with the article's
corrections (M30 to M41), as proposed in each entry unless the entry says otherwise;
W12 and W13 are left for the author. W44 to W47 were found while applying the others
or by the independent review of the corrections. The chapters are generated: change
them through `editorial/generate_companion.py` (the seed appendix through
`editorial/prepare_shared_appendix.py`) and regenerate.

- [x] **W1: Bounded gradients left implicit (Chapter M).**
  `companion/chapters/02_M.tex:194`: "$\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$ excludes
  a positive gap" needs $\sum_kq_k^{-1}\to\infty$, which Theorem `M:average`
  provides along runs with bounded gradients. No counterexample without that
  hypothesis is known; the same point as M10, to be applied with it. Proposed:
  "Thus, along runs with bounded gradients, …" (`C/02_M/prose/018`)
  Applied 15 October 2026.
- [x] **W2: Hypotheses of the contradiction at `02_M.tex:211`.** "Positivity gives
  $\sum_{J\le k<N}q_k^{-1}=O(N)$, contradicting Theorem~\ref{M:average}" is correct,
  but the contradiction needs the hypotheses of Theorem `M:average` (bounded
  gradients, $d_k\to0$): the moving-frame suppositions alone are satisfiable, by a
  one-dimensional run whose values tend to $-\infty$. Optional: "…contradicting
  Theorem~\ref{M:average} under its hypotheses." (`C/02_M/prose/023`)
  Applied 15 October 2026.
- [x] **W3: Undefined symbols in Theorem `M:superquadratic`.** `02_M.tex:144-155`
  uses $G$ and $V_\eta$ (which involves $K_0$); all three are defined only in the
  proof of Theorem `M:average`. The claim holds for every gradient bound $G$.
  Proposed: add "with $G$, $K_0$ and $V_\eta$ as in the proof of
  Theorem~\ref{M:average}". (`C/02_M/theorem/M:superquadratic`)
  Applied 15 October 2026.
- [x] **W4: Implicit hypotheses in Theorem `M:hierarchy`.** `02_M.tex:65-70` leaves
  $H\succ0$ and $\alpha>0$ implicit ($e_j$ is defined only for positive definite
  matrices, and $H_+\succ0$ exactly when $\alpha>0$). Optional: state both, as the
  article does. (`C/02_M/theorem/M:hierarchy`)
  Applied 15 October 2026.
- [x] **W5: Chapters cite themselves (M, A).** `02_M.tex:9`: "from
  sources~Chapters~\ref{comp:M}, \ref{comp:H}, …" lists Chapter M among its own
  sources, because the generator maps the frozen source's `\cite{SM,…}` to chapter
  labels. The same in Chapter 8: `08_A.tex:9` "…the geometric propositions of the
  affine-criticality note~Chapter~\ref{comp:A}." (source `affine_geometry.tex:7`,
  `\cite{SA}`; proposed "This chapter preserves the geometric propositions of the
  original affine-criticality note.") and `08_A.tex:111` "the
  references~\cite{BDLS}; Chapter~\ref{comp:A} supply" (source line 109,
  `\cite{SA,BDLS}`; proposed "the references~\cite{BDLS} supply"). Dropping the
  current chapter inside `cite()` alone would leave "note~." at `08_A.tex:9`, so use
  logged replacements. Cosmetic. (`C/02_M/prose/002`, `C/08_A/prose/003`,
  `prose/034`)
  Applied 15 October 2026; Chapter 2 now says "This chapter consolidates the common
  algebra of the source notes."
- [x] **W6: The proof of Lemma `comp:root_certificate` does not give the thirty
  digits of `D:rho` (proof gap).** `companion/appendices/seed_certificate.tex:37-40`:
  "\eqref{D:rho} holds" claims, through the label map `art:seed_rho` → `D:rho`, the
  value $\rho\simeq0.060199206107543764815373666287$ of `12_D.tex:99-102` on the whole
  box, where the article's same words claim only $0.060<\rho<0.061$. The printed
  proof (lines 41–92) still derives only $0.060<\rho<0.061$, which is what Lemma
  `D:root` states; `12_D.tex:117` says the interval calculation "certifies
  \eqref{D:rho}", but the companion never shows the thirty digits. The claim is true
  (`Companion.SeedCertificate.root_certificate`, interval evaluation on the root
  box). Options: map the reference to "$0.060<\rho<0.061$" in
  `prepare_shared_appendix.py` and call the thirty digits explanatory at line 117,
  or add to the proof "The same interval rules on the root box give the thirty
  digits in \eqref{D:rho}". (`C/seed_certificate/lemma/comp:root_certificate`,
  `C/seed_certificate/proof/001`, `C/12_D/proof/001`)
  Applied 15 October 2026 (option 2): the root lemma's proof ends "The same interval
  rules on the root box give the thirty digits in \eqref{D:rho}."
- [x] **W7: "The previous admissible-length counterexample" (Chapter D).**
  `12_D.tex:68`: "…resolves the implementation-selection issue left open by the
  previous admissible-length counterexample." Nothing in the companion is that
  counterexample (the phrase comes from the history of the source report).
  Optional: drop the clause or name the construction (frozen span `D.span.2`).
  (`C/12_D/prose/007`)
  Applied 15 October 2026: the clause is dropped.
- [x] **W8: "In this note".** `12_D.tex:105` (Lemma `D:root`: "All denominators in
  this note are nonzero there"), and the same remnant of the source reports at
  `04_R.tex:83`, `07_H.tex:23` ("This note continues the investigation…") and
  `09_C.tex:110` ("the subject of this note"); also "the previous note
  Chapter~8" at `09_C.tex:93` and "earlier notes" at `11_U.tex:354`. Optional: "in
  this chapter", "Chapter~8". (`C/12_D/lemma/D:root`, `C/04_R/prose/010`,
  `C/07_H/prose/002`, `C/09_C/prose/016`, `C/09_C/prose/020`, `C/11_U/prose/031`)
  Applied 15 October 2026; at `11_U.tex:354` "the source notes". Further places (found
  by the independent review, applied 15 October 2026): `13_L.tex:76` "…were certified
  in the preceding deterministic-bracketing report~Chapter~\ref{comp:D}." (printed
  "…report Chapter 12") → "…were certified in Chapter~\ref{comp:D}."
  (`C/13_L/prose/014`); `07_H.tex:319` "This potential inequality was established in
  the earlier note." → "…in an earlier source note." (`C/07_H/prose/030`);
  `04_R.tex:53` "The preceding report assumes the following positive-band condition:"
  → "The radial secant condition is the following positive-band condition:"
  (`C/04_R/prose/006`, now DEFINITION: it names (4.RS), with the name that W18 uses in
  Chapter 3 and that the article uses).
- [x] **W9: "The third slope" (companion appendix).** `seed_certificate.tex:12`:
  "The two unknown coordinates of the third slope …": "slope" is the article's term;
  the companion calls the $g_i$ gradients (`12_D.tex:160`). Optional: "of the third
  gradient $g_2=(c,d)^T$", a companion-only replacement in
  `prepare_shared_appendix.py`. (`C/seed_certificate/prose/017`)
  Applied 15 October 2026.
- [x] **W10: "The later nonsplitting conclusion" (Chapter 11).** `11_U.tex:492`, in
  "Relation to earlier work": the conclusion comes earlier, in Section 11.7 (subsection
  "The objective need not split as a smooth function plus …", line 453); the word is
  a remnant of the source's order. Proposed: "The nonsplitting conclusion of
  Section 11.7". (`C/11_U/prose/079`)
  Applied 15 October 2026 with `Section~\ref{...}` (prints 11.7.2). The same slip
  (applied 15 October 2026): `07_H.tex:470` "The earlier three-gradient, rank-two
  stagnation example attains this lower bound." → "The three-gradient, rank-two
  stagnation example of Chapter~\ref{comp:D} attains this lower bound." (the example
  is the seed run of Chapter 12, later in the companion; `C/07_H/prose/048`,
  `Ch07H.seed_cardinality_sharp`).
- [x] **W11: Unnamed references to results the companion states (Chapters 5 and 11).**
  `11_U.tex:111` "the affine-criticality program" (Chapter 8); 416 "the recorded
  equivalence between inward radial smoothness and RS" (Theorem `R:thm:equiv`); 422
  "the original arbitrary curved finite-$C^2$-max conjecture" (the conjecture of
  Chapter 8, `C/08_A/prose/042`, OPEN); 424 "the older finite-polyhedral-partition
  theorem" (Theorem `R:thm:plq`); `05_G.tex:89` "The accumulated-expansion budget was
  useful in the proof" (the proof of Chapter 3's theorem; source G.tex:79). Optional:
  cite them with `\ref`. (`C/11_U/prose/019`, `prose/044`, `prose/049`, `prose/050`,
  `C/05_G/prose/012`)
  Applied 15 October 2026.
- [ ] **W12: Redundant compactness hypothesis (Chapter 11).** Theorem 11.1
  (`11_U.tex:31-32`) assumes $F$ finite, convex, with a unique minimizer, and then
  "Let $K=\{F\le F(x_0)\}$ be compact"; lines 87–88 repeat "A compact initial
  sublevel is still required." A finite convex function with a unique minimizer has
  compact sublevel sets, so the assumption is implied. Harmless; optional.
  (`C/11_U/heading/001`, `prose/014`)
- [ ] **W13: Section numbers with gaps.** The frozen sources keep their notes'
  section numbers (`\setcounter{section}{…}`), so the printed companion skips
  numbers: Chapter 3 starts at 3.2, Chapter 4 has no 4.4, Chapter 5 no 5.5 or 5.8,
  Chapter 7 no 7.3 or 7.4, Chapter 10 has only 10.5 and 10.6, and Chapter 11 has no
  11.3 or 11.4; equation tags start late in the same way (Chapter 11 at (11.10)).
  Chapter 4 leaves (4.1) and (4.4) unused.
  Chapter 5 also leaves (5.1), (5.3), (5.5) unused, numbers subsections 5.2.1, 5.3.1,
  5.6.1 like its propositions, and refers to its tags (5.V), (5.S), (5.T), (5.T0) as
  "(V)", "(S)", "(T)", "(T0)". Cosmetic. Renumbering would change the numbers proposed in M17, M18 and the other
  reference fixes, so decide them together. (Notes on `C/11_U/prose/026`,
  `C/11_U/disp/009`.)
  Numbers written out by hand would break under a renumbering: `04_R.tex:307` "Theorem
  3.1, through Section 3.4 and its local form in Section 3.3.2", `04_R.tex:230`
  "Section~4.6", `01_I.tex:123` "Section~12.3.1", Chapter 11's "Theorems 11.1 and
  11.2", (11.11), (11.14), (11.16)--(11.17), (11.18), (11.20), (11.21) (M18) and
  Chapter 3's (3.3)--(3.6) (M25); the references of Chapters 7 and 10 (M17, M28) go
  through the numbering loop and would follow.
- [x] **W14: "We will argue by contradiction that Γ contains no affine-critical
  point" (Chapter 9).** `09_C.tex:151` announces the conclusion as the thing argued
  by contradiction, while the paragraph goes on with its negation as the standing
  supposition ("Then $\ell>F_*$, every point of $\Gamma$ satisfies the
  regular-switching hypothesis, …"). Proposed: "We suppose, for a contradiction,
  that the compact cluster set $\Gamma$ contains no affine-critical point."
  (`C/09_C/prose/027`)
  Applied 15 October 2026.
- [x] **W15: Range of the angular cutoffs (Chapter 9).** `09_C.tex:191` chooses
  smooth angular cutoffs $\chi_j$ "with disjoint supports, equal to one on
  neighborhoods of the entire moving normal arcs"; the later estimates (line 202
  and the display at lines 218–220) also need $0\le\chi_j\le1$. Standard cutoffs
  have it; optional: say so. (`C/09_C/prose/041`; used by `prose/042`, `disp/020`)
  Applied 15 October 2026.
- [x] **W16: Sign of $\epsilon$ left to the context (Chapter 5).** `05_G.tex:269-278`:
  "For $x=\epsilon$, $z=-\epsilon/2$," and the formulas that follow need $\epsilon>0$
  (for $\epsilon<0$, $g_x=1+\epsilon$); only line 278's "strictly eligible" and line
  307's $\epsilon\downarrow0$ fix the sign. Proposed: "For $x=\epsilon$,
  $z=-\epsilon/2$ with $\epsilon>0$," (source `For $x=\epsilon$, $z=-\epsilon/2$,`,
  G.tex:251, occurs once). Lean: `Ch05G.shifted_crossing_gradients`,
  `shifted_crossing_quantities`, `shifted_crossing_eligible_divergent` (all with
  $\epsilon>0$). (`C/05_G/disp/025`, `disp/026`, `prose/054`)
  Applied 15 October 2026.
- [x] **W17: "Conditions (V)--(S)" (Chapter 3).** `03_T.tex:192`: "Conditions
  (V)--(S) become" means "(V) and (S)" (tags (3.V), (3.S)): a range of condition
  names, not a wrong number. Optional: "Conditions (V) and (S) become" (T.tex:170,
  occurs once). (`C/03_T/disp/024`)
  Applied 15 October 2026. Chapter 5 too (applied 15 October 2026): `05_G.tex:142` "If
  $C>0$ and $W$ satisfies (V)--(S)," and `:151` "Thus higher rank adds no pointwise
  power to (V)--(S);" now read "(V) and (S)" (`C/05_G/proof/002`, `C/05_G/prose/022`);
  `05_G.tex:72` "The existential condition (V)--(T)" is a true range of the three
  conditions and is kept.
- [x] **W18: (RS) used before Chapter 4 defines it (Chapter 3).** The section title
  at `03_T.tex:216`, "Given (RS), take" (line 217) and lines 225, 229 use "(RS)",
  which Chapter 4 defines ((4.RS), `04_R.tex:53-59`, label `R:eq:RS`), with no
  pointer. Optional: "Given the radial secant condition (RS) of
  Chapter~\ref{comp:R}, take" (T.tex:191, occurs once). (`C/03_T/disp/026`,
  `prose/029`)
  Applied 15 October 2026.
- [x] **W19: Nonnegative constants in (RS) and (IR) (Chapter 4, proof gap).**
  `04_R.tex:55` ((4.RS)): "$\forall\eta>0\ \exists C_\eta<\infty$"; `04_R.tex:74`
  ((4.IR)): "there exist $M_\eta<\infty$ and $\theta_\eta\in(0,1/2]$". The proofs use
  $C\ge0$ without saying so: line 149, "If $a=0$, the same conclusion follows from
  $\DF(z,x)\le ta=0$" (the bound $\le4C_{\eta/2}t^2$ of lines 146–148 needs
  $C_{\eta/2}\ge0$); the cases $a_\pm=0<t$ of "$a_+\le Ct,\ a_-\le Ct/(1-t)^2$"
  (lines 174–176); and line 177, "The central difference is at most
  $t(a_++a_-)\le5Ct^2$ for $t\le1/2$". True as stated: an (RS) constant on a band
  with a point strictly between the band threshold and $b$ is $\ge0$, since a
  differentiable pair on opposite sides of $x_*$ with $T>0$ forces it. Proposed:
  "$\exists C_\eta\ge0$" in (4.RS) and "there exist $M_\eta\ge0$ and
  $\theta_\eta\in(0,1/2]$" in (4.IR), as in the article
  (`paper/sections/global.tex:31,40`; source R.tex:49, 64). Lean:
  `Ch04R.rs_constant_nonneg`, `error_bound_zero`, `radial_pair_bounds`,
  `central_le_five`, `RS_iff_article`, `IR_iff_article`. (`C/04_R/disp/006`,
  `disp/007`, `disp/019`, `disp/023`, `prose/014`, `prose/018`)
  Applied 15 October 2026.
- [x] **W20: "For differentiable $x,z$" without "$\in K$" (Chapter 4).**
  `04_R.tex:40`: "For differentiable $x,z$, put" introduces $T$ and the bound "$0\le
  T\le T_{\max}:=4GR$" (line 51), which holds only for $x,z\in K$ ($R$ and $G$ are
  bounds on $K$): for $F(x)=|x|$, $b=1$, $R=G=1$, the points $x=-10$, $z=10$ give
  $T=40>4GR$. The article has "$x,z\in K$" (`paper/sections/global.tex:20`); the
  all-of-$\mathbb R^n$ reading is not a reasonable one, so no discrepancy. Proposed:
  "For differentiable $x,z\in K$, put" (source R.tex:34). Lean:
  `Ch04R.curvature_split`, `secant_notation`. (`C/04_R/disp/003`, `disp/005`)
  Applied 15 October 2026.
- [x] **W21: References to unnamed, later or absent material (Chapter 4).** Each
  phrase occurs once in the source R.tex. (a) Line 307, proof of Theorem 4.5.1: "the
  preceding convergence theorem applies" is Theorem 3.1 (`03_T.tex:90`, no
  `\label`), through Section 3.4 and the local form of Section 3.3.2; proposed "…and
  the convergence theorem of Chapter~\ref{comp:T} (Theorem 3.1, through Section 3.4
  and its local form in Section 3.3.2) applies." (R.tex:277; `Ch04R.plq_theorem`;
  `C/04_R/proof/001`). (b) Line 368: "shortening the earlier segment-based proof":
  no such proof is in the companion; optional: drop the clause (R.tex:322;
  `Ch04R.finite_max_branch_test`; `C/04_R/prose/079`). (c) Line 370: "the old
  radial condition" is (RS); proposed "The necessity for (RS) is also clear on
  genuine active ties" (R.tex:324; `Ch04R.finite_max_necessity`;
  `C/04_R/prose/080`). (d) Line 429: "the original local radial criterion" is (RS)
  on neighbourhoods of $X_*$, which fails on every neighbourhood; proposed "…need not
  satisfy (RS) on any neighborhood of a nonzero rank-deficient minimizer."
  (R.tex:375; `Ch04R.spectral_RS_fails`; `C/04_R/prose/095`). (e) Line 230: "the
  breadth of the preceding sufficient classes": the classes come later, in Section
  4.6; optional "of the sufficient classes of Section~4.6" (R.tex:204;
  `C/04_R/prose/040`, NON_CLAIM).
  Applied 15 October 2026.
- [x] **W22: The letter "D" for Chapter 12's objects (Chapter 4).** `04_R.tex:255`:
  "the certified D parameters" and "The unique D optimizer $(-1,16)$"; line 265:
  "the verified D run"; line 276: "$a$ times those of D". "D" is the source letter of
  Chapter 12, which the chapter cites correctly as Chapter~\ref{comp:D} at lines 233
  and 253; in print the letter names nothing, but no wrong number is printed and the
  claims are true. Optional: "Chapter 12's certified parameters", "Chapter 12's
  unique optimizer", "the verified run of Chapter 12", "those of the run of
  Chapter 12" (source R.tex:229 (twice), 239, 250). Lean:
  `Ch04R.fourPiece_constants`, `fourPiece_optimizer`, `fourPiece_transformed_data`,
  `fourPiece_curvatures`. (`C/04_R/prose/043`, `prose/045`, `disp/037`, `prose/054`)
  Applied 15 October 2026 with `Chapter~\ref{comp:D}'s`.
- [x] **W23: The reason given for "broader" (Chapter 4).** `04_R.tex:309`: "This is
  broader than merely having affine pieces plus one common smooth summand: different
  cells can have different quadratic Hessians and different gradient jumps." The
  claim is true for every reading of "smooth" (`Ch04R.plq_broader_2d`:
  $u^2+v^2+(2+|u|)|v|$ is covered and is no differentiable function plus a finite
  max of affine functions), but the reason separates the classes only when "smooth"
  means $C^2$: with a $C^{1,1}$ summand, the chapter's own use of "smooth" (lines
  300–307), different Hessians also occur ($x^2+\max\{x,0\}^2+|x-1|$), and affine
  pieces give different jumps across different boundaries. What such a sum cannot
  produce is a gradient jump that varies along one cell boundary. Proposed:
  "…different cells can have different quadratic Hessians, and the gradient jump can
  vary along a cell boundary (for example $u^2+v^2+(2+|u|)|v|$ near the origin)."
  (source R.tex:279). Lean: `Ch04R.plq_broader_2d`,
  `plq2d_not_smooth_plus_max_affine`, `plq2d_covered`, `plq2d_jump`, `plq_broader`
  ($C^2$ summands, dimension one). (`C/04_R/prose/059`, `prose/060`)
  Applied 15 October 2026.
- [x] **W24: Bounded gradients left implicit (Chapter 6).** `06_F.tex:122-125`: "If
  $R_k\le\bar R$, then \eqref{M:energybound} gives
  $F(x_N)-F_*\le\sqrt{(E_0+\bar RN)/S_N}=o(N^{-1/2})$, because $S_N/N^2\to\infty$.
  The same estimate holds for a linear cumulative correction budget." The inequality
  needs nothing more; the little-$o$ uses Theorem `M:superquadratic`, whose
  bounded-gradient hypothesis is left implicit (same point as W1 and M10). The
  hypothesis is not automatic ($\max\{x^2-y,0\}$ is convex with minimizers and has
  unbounded gradients on every positive sublevel), but no admissible run violating
  the literal claim is known. Proposed: "…, and along runs with bounded gradients
  this is $o(N^{-1/2})$, because $S_N/N^2\to\infty$." Lean:
  `Ch06F.bounded_correction_rate`, `linear_budget_rate` (the inequality without, the
  little-$o$ with bounded gradients). (`C/06_F/disp/013`, `C/06_F/prose/029`)
  Applied 15 October 2026.
- [x] **W25: References to source material absent from the companion (Chapter 6).**
  `06_F.tex:118`: "The source rate note recorded big-$O$ bounds. The little-$o$
  versions below are explicit consolidation deductions from the later superquadratic
  theorem; they do not assert a sharp rate." The rate note (working report [SQ], see
  M27) is not in the companion, and the superquadratic theorem is Theorem
  `M:superquadratic` of Chapter 2, earlier in the companion ("later" is historical).
  `06_F.tex:161`: "Summing first recovers the source bounds $\sqrt{A_N}=O(\log N)$
  and $F(x_N)=O(\log N/N)$." `06_F.tex:197`: "This is the proved tilted-minimum
  construction, replacing the earlier first-right-derivative-threshold route." (W7,
  W8, W21 type.) Proposed: "Big-$O$ versions of these bounds appeared in the source
  notes. The little-$o$ versions below follow from Theorem~\ref{M:superquadratic};
  they do not assert a sharp rate."; "Summing first gives the bounds …"; "This is
  the proved tilted-minimum construction." (`C/06_F/prose/028`, `prose/036`,
  `prose/047`)
  Applied 15 October 2026. The proposal's "these bounds" at `06_F.tex:118` pointed
  forward; it now reads "Big-$O$ versions of these rates appeared in the source
  notes." ("these rates" are the "rates below" of the preceding sentence;
  `C/06_F/prose/028`).
- [x] **W26: Chapter 3's theorem and conditions named only by description
  (Chapter 10).** `10_Q.tex:49`: "This is a concrete application of the
  objective-pair theorem, not the definition of its scope."; `10_Q.tex:115`:
  "Multiplication by $\theta(z)^2$ proves (S). Equation (11) proves (V) …";
  `10_Q.tex:217`: "This is (T). The general theorem proves convergence from every
  admissible initialization." The theorem is Chapter 3's transported-certificate
  theorem (`03_T.tex:90-111`), and (V), (S), (T) are its conditions, tagged (3.V),
  (3.S), (3.T); Chapter 3 itself calls them (V), (S), (T), so these are not wrong
  numbers. Proposed (optional): "… of the transported-certificate theorem of
  Chapter~\ref{comp:T}"; "(S) of Chapter~\ref{comp:T}". (`C/10_Q/prose/002`,
  `prose/014`, `prose/028`)
  Applied 15 October 2026.
- [x] **W27: Tolerances and the implicit basin in Chapter 14's numerical suites.**
  `14_E.tex:184` (Section 14.3.17, printed page 92): "The operative statement is
  analytic: the stated planar example converges, and hence every positive displayed
  tolerance is eventually attained." `14_E.tex:192` (Section 14.3.18, same page): "Its
  convergence implies eventual attainment of the printed positive tolerance." No
  tolerance is displayed or printed anywhere in the companion (the source suites
  measured $F<10^{-45}$ and $F<10^{-28}$; that execution record was removed), so both
  phrases refer to nothing; both claims hold for every positive tolerance. At line 184
  the basin is also left implicit: the example of Section 9.8 is proved to converge
  from its basin $F(x_0)<1/100$ (\eqref{C:eq:explicitbasin}). Convergence from every
  start is not available: $F$ has a second triple point $p\approx(3.5098,2.6494)$ with
  $F(p)\approx19.34$ whose three active gradients are affinely independent, so $p$ is
  affine-critical but not a minimizer and the planar corollary does not apply to
  sublevels containing it (floating-point computation, not formalized; no
  counterexample run is known). Generated file; logged transformations in the
  `if module=='E':` block of `editorial/generate_companion.py`, on the frozen
  `verification.tex`: line 97, span `E.span.21`: `the stated planar example converges,
  and hence every positive displayed tolerance is eventually attained.` (occurs once)
  → `the stated planar example converges from its basin~\eqref{C:eq:explicitbasin},
  and hence every positive tolerance on its objective value is eventually attained.`
  (the generator's letter substitution does not touch `C:eq:`); line 101, span
  `E.span.22`: `eventual attainment of the printed positive tolerance` (occurs once) →
  `eventual attainment of every positive tolerance`. Lean: `Ch14E.planar_tolerance`,
  `Ch14E.spike_tolerance` (every $\varepsilon>0$); the historical values are
  `EReconstruction.planar_eventual_printed_tolerance` and
  `spike_eventual_printed_tolerance`. (`C/14_E/prose/076`, `prose/079`)
  Applied 15 October 2026.
- [x] **W28: Bounded gradients left implicit (Chapter 14).** `14_E.tex:112`
  (Section 14.3.8 "M-mixed", printed page 91): "The actual full-matrix hierarchy
  yields the normalized hierarchy, weighted potential, qualitative reciprocal growth
  and superquadratic reciprocal growth under summable predicted decreases." Every
  result named uses a uniform gradient bound $G$: the normalized hierarchy and the
  weighted potential through $K_0=4G^2/c^2$, and Theorems `M:average` and
  `M:superquadratic` by hypothesis; only the summability is stated. Same point as W1
  and W24; no counterexample run is known. Generated file; proposed, on the frozen
  `verification.tex:61` (span `E.span.12`), as a logged transformation in the
  module-E block: `The actual full-matrix hierarchy yields the normalized hierarchy`
  (occurs once) → `Along runs with bounded gradients, the actual full-matrix hierarchy
  yields the normalized hierarchy`. Lean: `Ch02M.hierarchy_step`,
  `Ch02M.potential_ge_trace`, `Ch02M.weighted_step`, `Ch02M.average`,
  `Ch02M.superquadratic` (all with the gradient bound). (`C/14_E/prose/052`)
  Applied 15 October 2026.
- [x] **W29: The suite labels of Chapter 14 are names, not chapter letters
  (optional).** `14_E.tex:48` (Section 14.3, printed page 90): "The labels below
  preserve correspondence with the original report." The 19 subsection titles of
  Section 14.3 (D-root, …, G-oscillatory-numerical) are the original report's suite
  names, and their letters are not chapter letters: "A-minors" is Chapter 2 material
  (not Chapter 8 or Appendix A), "H-lifting" is Chapters 6–7, and "P-" and "V-" match
  no chapter. They are names, not references (W22 type). Generated file; optional, on
  the frozen `verification.tex:29` (span `E.span.4`), as a logged transformation in
  the module-E block: `The labels below preserve correspondence with the original
  report.` (occurs once) → `The labels below are the original report's suite names,
  whose letters are not chapter letters; they preserve correspondence with that
  report.` (`C/14_E/prose/029`)
  Applied 15 October 2026.
- [x] **W30: Stale or inaccurate statements about the verification and the records
  (Chapter 14 and Appendix B).** All are `NON_CLAIM`; refresh them in step 2.
  - `current_verification.tex:8` (hand-written; printed page 88): "All 2026 Lean
    names cited by the article ledger or declared in the package depend only on …".
    `bfgs_lean_article/AXIOM_AUDIT.json` checks 5403 names (15 October, with every
    coverage module). Replace `All 2026 Lean names` (occurs once) by the count of the
    final audit. (`C/current_verification/prose/004`)
  - `14_E.tex:16` (generated; Section 14.1, printed page 89): "… but each retained
    assertion here has a reviewed formal correspondence." The coverage found retained
    assertions that are false or misreferenced as written (M12–M29). Once those
    corrections are applied the sentence holds again; check it then. Otherwise, on the
    frozen `verification.tex:5` (span `E.span.2`): `but each retained assertion here
    has a reviewed formal correspondence` (occurs once) → `… correspondence or a
    recorded correction`. (`C/14_E/prose/007`)
  - `correspondence.tex:12–13` (hand-written; Appendix B, printed page 97): "The new
    opening changes their scientific presentation and reading order, not their
    mathematical assertions." Accurate for the opening; read it with the next point.
    Optional: after `not their mathematical assertions.` (occurs once), point to the
    logged generalization of the next point. (`C/correspondence/prose/006`)
  - `correspondence.tex:62` (hand-written; printed page 98): "Source transformations
    preserve the corrected mathematical assertions." The 13 October `constant_range`
    transformations of `editorial/generate_companion.py` generalize the
    lower-curvature failures of Chapters 1 and 13 from $c_1=10^{-4}$, $c_2=1/2$ to
    every $0<c_1\le1/3$, $c_1<c_2<1$, a proved strengthening
    (`LUniform.uniform_global_failure`, `LUniform.uniformSmoothLocalFailure`).
    Proposed: `Source transformations preserve the corrected mathematical assertions.`
    (occurs once) → `Source transformations preserve the corrected mathematical
    assertions, except the logged October 2026 generalization of the lower-curvature
    failures to every admissible pair of line-search constants.`
    (`C/correspondence/prose/028`)
  - `correspondence.tex:22` (hand-written; printed page 97): "None of these
    incomparable results is treated as superseded …". "Incomparable" is inaccurate:
    the constant-Hessian family of Chapter 13 is the family of the article's appendix
    Proposition `art:quadratic_failure`, and the consequences of Theorem 7.A for
    bounded-below and coercive objectives give the article's Theorem
    `art:homogeneous`. The policy itself is unaffected. Proposed: `None of these
    incomparable results` (occurs once; "incomparable" at line 32, in the
    supersession-ledger row, is not concerned) → `None of these results`.
    (`C/correspondence/prose/010`)
  - `correspondence.tex:27` (hand-written; table, printed page 97):
    `\path{SOURCE_CORRESPONDENCE.json}`; the file is
    `companion/SOURCE_CORRESPONDENCE.json`, and the other rows give paths from the
    repository root. Proposed: `\path{companion/SOURCE_CORRESPONDENCE.json}`.
    (`C/correspondence/prose/011`)
  - `correspondence.tex:29–30` (hand-written; row of `editorial/CLAIM_LEDGER.json`,
    printed page 97): "… their proof locations …". The ledger's `proof_locations` for
    `paper/appendices/lower_curvature.tex` are stale (see `TODO_LEAN_REVIEW.md` and
    `AGENTS.md`, "Known stale or frozen items"). The fix is in the data, through a new
    correspondence revision (`refresh_correspondence.py` rejects statement changes),
    not in this sentence. (`C/correspondence/prose/012`)
  - `14_E.tex:226` (generated; Section 14.5, printed page 92): "Its README describes
    the read-only evidence check and the exact default output path."
    `bfgs_lean_stage1/master_report/audit/README.md` describes the read-only check
    (`--check`) and says that `--run` creates and prints a new timestamped directory;
    the default path (`master_report/audit/runs/<UTC timestamp>`) is defined in
    `run.py`. Proposed, on the frozen `verification.tex:123` (span `E.span.25`), as a
    logged transformation in the module-E block: `Its README describes the read-only
    evidence check and the exact default output path.` (occurs once) → `Its README
    describes the read-only evidence check; the runner prints the new timestamped
    output directory.` (`C/14_E/prose/095`)
  Applied 15 October 2026: `correspondence.tex:62` adds "and the October 2026
  corrections recorded in \path{TODO_MANUSCRIPT_REVIEW.md}", and
  `current_verification.tex:8-11`, under the new heading "The October 2026 Lean
  review", gives the axiom audit of 15 October 2026 (5403 Lean names, namely every
  name then cited by the claim ledger or by the coverage registers, and the principal
  declarations of the package; PASS) and the kernel replay (every project module
  except the two root modules, which contain only imports: 783 modules; PASS);
  `14_E.tex:16` holds after the corrections and is unchanged. The counts are refreshed
  again with the final audit of step 2.

The wording points W31–W43 are in Chapter 1 and the research story (compI, 15
October). Chapter 1 is generated: unless an item says otherwise, its old string
occurs once in the frozen `bfgs_lean_stage1/master_report/latex/chapters/inventory.tex`
and once in `01_I.tex`, and the fix is a logged replacement in the `if module=='I':`
block of `editorial/generate_companion.py`, which runs after the renumbering and the
relocation of the attribution notes, so it sees the printed strings quoted here. No
replacement adds a line; after regenerating, update the anchors of the items named.

- [x] **W31: The claim/proof index described as complete (Chapter 1).** `01_I.tex:14`:
  "Every retained mathematical assertion is paired with its reviewed formal statement
  and Lean proof in the claim/proof index." The index paired many sentences only
  coarsely, which is why the literal Lean coverage was needed. Proposed, once the
  index is regenerated from the coverage registers in step 2 (`inventory.tex:10`):
  `Every retained mathematical assertion is classified in the claim/proof index, and
  each asserted result is paired there with its formal statement and Lean proof.`
  (`C/01_I/prose/003`)
  The sentence was applied on 15 October 2026, and the same day the claim/proof index
  gained the coverage registers: `editorial/assemble_claim_ledger.py` (through
  `editorial/coverage_index.py`) now lists every item of both documents with its
  status, its target or reason, and the statement of each Lean name it cites (keys
  `lean_coverage`, `lean_coverage_records` and `lean_coverage_declarations` of
  `editorial/CLAIM_LEDGER.json`, last section of `companion/PROOF_CORRESPONDENCE.html`),
  and stops if a cited name is missing from the Lean sources.
- [x] **W32: Bare subsection number (Chapter 1).** `01_I.tex:123`:
  "\textbf{Proofs: 12.3.1 and Chapter~\ref{comp:L}.}" prints the right subsection
  (12.3.1, "A simple coercive global failure", which has no label); the source reads
  `\textbf{Proofs: D.3.1 and Module L.}` (`inventory.tex:97`). Proposed, in the
  module-I block (after the renumbering): `\textbf{Proofs: 12.3.1 and Chapter~\ref{comp:L}.}`
  → `\textbf{Proofs: Section~12.3.1 and Chapter~\ref{comp:L}.}` (`C/01_I/prose/039`)
  Applied 15 October 2026.
- [x] **W33: Hypotheses of Theorem M:average left implicit in P2 (Chapter 1; as W2).**
  `01_I.tex:161`: "Uniform visibility, bounded secant correction, and bounded
  cumulative transport products and inverses exclude positive-level stagnation." As
  at `02_M.tex:211`, the contradiction needs bounded gradients and $d_k\to0$.
  Proposed (`inventory.tex:123`): `exclude positive-level stagnation.` →
  `exclude positive-level stagnation along runs with bounded gradients.`
  (`Ch02M.frame_criterion`; `C/01_I/prose/053`)
  Applied 15 October 2026.
- [x] **W34: Hypotheses of Theorem M:residualtheorem left implicit in P3 (Chapter 1;
  as W1 and M10).** `01_I.tex:176`: the theorem assumes bounded gradients and
  $\sum d_k<\infty$; "the superquadratic reciprocal theorem below" (lines 306–308)
  states them, the sentence does not. Proposed (`inventory.tex:134`):
  `Together with uniform visibility and bounded secant correction, the resulting \(O(N^2)\) error budget is defeated by the superquadratic reciprocal theorem below.`
  → `Together with uniform visibility and bounded secant correction, along runs with bounded gradients and \(\sum d_k<\infty\), the resulting \(O(N^2)\) error budget is defeated by the superquadratic reciprocal theorem below.`
  (`Ch02M.residual_theorem`; `C/01_I/prose/056`)
  Applied 15 October 2026.
- [x] **W35: "The user's paper" (Chapter 1).** `01_I.tex:291`: "The user's paper is
  supplied separately, not rebranded as a new result." A remnant of the drafting.
  Proposed: delete the sentence, or replace it (`inventory.tex:221`) by `That
  paper~\cite{XW} is prior work, not a new result of this report.` (the key `XW` is in
  `companion/bibliography.tex`). (`C/01_I/prose/113`)
  Applied 15 October 2026.
- [x] **W36: Bounded gradients left implicit (Chapter 1; as W1).** `01_I.tex:317`: "A
  cumulative correction \(o(\sum q_k^{-1})\) excludes a positive gap." This needs
  $\sum q_k^{-1}\to\infty$, which Theorem M:average gives along runs with bounded
  gradients. Proposed (`inventory.tex:243`): `A cumulative correction \(o(\sum q_k^{-1})\) excludes a positive gap.`
  → `Along runs with bounded gradients, a cumulative correction \(o(\sum q_k^{-1})\) excludes a positive gap.`
  (`Ch02M.negligible_corrections`, `Ch02M.negligible_corrections_of_divergent`;
  `C/01_I/prose/117`)
  Applied 15 October 2026.
- [x] **W37: A source rate note and implicit bounded gradients (Chapter 1; as W24 and
  W25).** `01_I.tex:319`: "The original rate note" is not in the companion, "later" is
  historical (Theorem M:superquadratic is in Chapter 2), and the \(o(N^{-1/2})\) rate
  needs bounded gradients. Proposed (`inventory.tex:245`):
  `The original rate note recorded big-\(O\) corollaries. The later superquadratic reciprocal theorem strengthens them to \(o(N^{-1/2})\) for uniformly bounded radial correction,`
  → `Big-\(O\) versions of these rates appeared in the source notes. Theorem~\ref{M:superquadratic} strengthens them to \(o(N^{-1/2})\) for uniformly bounded radial correction along runs with bounded gradients,`
  (`Ch06F.bounded_correction_rate`, `Ch06F.linear_budget_rate`,
  `Ch06F.homogeneous_rate`, `Ch06F.quadGauge_rate`; `C/01_I/prose/120`, `prose/121`)
  Applied 15 October 2026. The proposal's "these rates" at `01_I.tex:319` pointed
  forward; it now reads "Big-\(O\) versions of the following rates appeared in the
  source notes." (`C/01_I/prose/120`).
- [x] **W38: Path of the literature register (Chapter 1).** `01_I.tex:391`:
  `\path{literature_audit/}` exists only as `bfgs_lean_stage1/literature_audit/`.
  Proposed (`inventory.tex:6`, in the relocated attribution note):
  `The detailed source/version register is delivered in \path{literature_audit/};` →
  `The detailed source/version register is delivered in \path{bfgs_lean_stage1/literature_audit/};`
  (a software description, as in W30; `C/01_I/prose/159`)
  Applied 15 October 2026.
- [x] **W39: "Value convergence does not imply bounded iterates" (research story).**
  `research_story.tex:30-31`: "The full noncompact homogeneous value alternatives are
  retained separately: value convergence does not imply bounded iterates, and it does
  not subsume Xie--Wächter's finite detection…" A scope remark (Theorem 7.A concludes
  values only), classified `NON_CLAIM`; it reads as the claim that some homogeneous
  run has value convergence with unbounded iterates, which is not established (open
  in recurrent dimension $\ge3$, `Ch07H.ZeroValueIterateQuestion`; the iterates
  converge for max-linear objectives of recurrent dimension $\le2$). Proposed, a
  direct edit (hand-written file): `value convergence does not imply bounded iterates,
  and it does not subsume` (occurs once) → `they conclude objective-value convergence
  without any conclusion about the iterates, and they do not subsume`.
  (`ResearchStory.value_convergence_unbounded_iterates` illustrates the general
  non-implication with $F=e^x$; `C/research_story/prose/017`)
  Applied 15 October 2026.
- [x] **W40: "A compact sublevel" (Chapter 1, minor).** `01_I.tex:218` (P5): "have an
  attained minimum and a compact sublevel" leaves Chapter 9's $b>F_*$ implicit (an
  empty sublevel is compact); harmless, since for convex $F$ one nonempty compact
  sublevel makes all sublevels compact. Optional (`inventory.tex:168`):
  `have an attained minimum and a compact sublevel,` → `have an attained minimum and a
  compact sublevel above the minimum,` (`Ch01I.p5_cluster`,
  `Ch01I.sublevels_compact_of_one`; `C/01_I/prose/074`)
  Applied 15 October 2026.
- [x] **W41: "Neither proves local failure for …" (Chapter 1).** `01_I.tex:107`:
  "Neither proves local failure for a finite maximum of uniformly strongly convex
  \(C^2\) branches through the optimizer." This reads as a claim about every
  representation of the two objectives; what is proved is that the constructed
  branches are not in that class (N1's are not uniformly strongly convex, three of
  N2's four are not $C^2$). Proposed (`inventory.tex:85`, span `I.span.6`):
  `Neither proves local failure for a finite maximum of uniformly strongly convex \(C^2\) branches through the optimizer.`
  → `Neither is constructed from finitely many uniformly strongly convex \(C^2\) branches through the optimizer, so neither proves local failure for that class.`
  (`Ch01I.n1_n2_comparison`; open question
  `Article.Verification.C2StronglyConvexLocalFailure`; `C/01_I/prose/029`)
  Applied 15 October 2026.
- [x] **W42: "These families" without antecedent (Chapter 1).** `01_I.tex:393`: "These
  families include established special cases: Guo--Lewis proves …". The generator
  moved this attribution note (`i.known_special_cases`) from the start of Section 1.4,
  "Strongest concrete local and global positive families" (`inventory.tex:137-140`),
  to "Relation to earlier work", after a paragraph on bibliographic notes. Proposed
  (`inventory.tex:139`; the module-I block sees the relocated note):
  `These families include established special cases` → `The positive families of
  Section~\ref{strongest-concrete-local-and-global-positive-families} include
  established special cases` (the label is at `01_I.tex:182`).
  (`Ch04R.euclidean_norm_recovered`; `C/01_I/prose/160`)
  Applied 15 October 2026.
- [x] **W43: $E_k$ and $B_k$ undefined in Chapter 1 (cosmetic).** `01_I.tex:312-315`:
  "The fixed-reference identity is $E_{k+1}=\dots$"; $E_k$, $r_k$ and $B_k$ are
  defined only in Chapter 2 (`02_M.tex:182`, `02_M.tex:14`), and $B_k$ also appears at
  `01_I.tex:169`. Proposed, two replacements: `The fixed-reference identity is`
  (`inventory.tex:238`) → `For a fixed reference point \(x_*\) and
  \(E_k=(x_k-x_*)^TB_k(x_k-x_*)\), the fixed-reference identity is`; and
  `the actual update gives \(\operatorname{tr}(P_SB_k)=O(k)\).` (`inventory.tex:127`)
  → `the actual update gives \(\operatorname{tr}(P_SB_k)=O(k)\) for \(B_k=H_k^{-1}\).`
  (`Ch02M.fixed_energy`, `Ch01I.smooth_subspace_trace_linear`; `C/01_I/disp/021`,
  `prose/055`)
  Applied 15 October 2026.
- [x] **W44: "the user's" in Chapter 13 (as W35).** `13_L.tex:61`: "The local
  theorem satisfies the user's literal classical-Hessian assumption, and even actual
  strong convexity." "The user" is the person who asked for the source note. It now
  reads "The local theorem satisfies the literal classical-Hessian assumption, and
  even actual strong convexity." (logged module-L replacement; frozen `L.tex:54`,
  span `L.span.2`; `C/13_L/prose/010`, LEAN, `Ch13L.local_failure`). Found while
  applying the companion corrections. Applied 15 October 2026.
- [x] **W45: "C2,1" printed as plain text (Chapter 13 introduction).**
  `introductions['L']` of `editorial/generate_companion.py` (`13_L.tex:3`): "…with
  the preceding local C2,1 branch regularity." now reads "…with the preceding local
  $C^{2,1}$ branch regularity." (`C/13_L/prose/003`). Applied 15 October 2026. The
  same plain "C2,1" remains in a title of Chapter 1 (W47).
- [x] **W46: Duplicate equation numbers in Chapters 12 and 13.** The
  `\setcounter{equation}` values of the frozen sources omit the numbered lines of
  `gather`/`align` displays, so the companion printed (12.9)–(12.11), (13.3)–(13.5)
  and (13.8) twice (for example, "Equation~(13.8) applies at the initial point…" was
  ambiguous). Six logged transformations (modules D and L) make the counter
  continue: `D:fullobjective`, `D:localcone` and `D:finalorbit` are now
  (12.12)–(12.14), and `L:eq:eigshape` to `L:eq:local-model` are now (13.6)–(13.13).
  All references are `\eqref` and print the intended numbers; no number written out
  by hand needed a change. Found by the independent review of the companion
  corrections. Applied 15 October 2026. The gaps of W13 remain.
- [x] **W47: "C2,1" printed as plain text (Chapter 1).** `01_I.tex:69`:
  `\subsection{N1. Deterministic local failure with globally C2,1 convex branches}`
  prints "C2,1" (PDF page 8, printed page 2; frozen `inventory.tex:51`). Proposed: a
  logged module-I replacement `globally C2,1 convex branches}` →
  `globally \texorpdfstring{$C^{2,1}$}{C2,1} convex branches}` (hyperref is loaded).
  Found by the fix pass of the companion corrections. (`C/01_I/prose/015`)
  Applied 15 October 2026 with the article's corrections (M30 to M41); the subsection
  label is unchanged.

## Resolved

- [x] **M1: Qualifier spacing in displays.** In `paper/sections/failure.tex`, the
  seed query bounds `|g_i^Tz|<3 (i=0,1,2)` and the local model condition
  `|g_i^Th|\le a_\ell/2 (i=0,1,2)` lost the space before the qualifier, so they
  rendered as `3(i=0,1,2)` and `a_\ell/2(i=0,1,2)`, which read as products. The
  same happened to `(g_i-g_k)^Tq (k\ne i)` in `paper/appendices/seed_certificate.tex`.
  All three now use `\quad`. A scan of every display in `paper/` found no other
  case. The seed appendix is shared, so `companion/appendices/seed_certificate.tex`
  was regenerated with `editorial/prepare_shared_appendix.py`.

- [x] **M2: `[z]_2` was undefined.** The 13 September exposition revision replaced
  `z_2` by `[z]_2` and removed the sentence saying that it is a coordinate. Lemma
  `art:seed_cycle` now reads "each such point $z$, with second coordinate
  $[z]_2$, satisfies".

- [x] **M3: Symbols reused for different objects in the same argument.**
  - `local.tex`, proof of Lemma `art:localization`: the sphere gap was `\omega`,
    which the article reserves for `1-c_2`. It is now `\delta`.
  - `lower_curvature.tex`: the return factor `r=(M_3)_{11}` is now `\hat\rho`
    (`r=1/128` is the scale ratio later in the same appendix; `\hat\rho(P_*)=\rho`).
    The matrix-shape coordinates `(b,e)` are now `(\zeta,\eta)`, since `b` is the
    scalar-family parameter `b_i`, `\psi_b`, `t_b` in the same appendix. The
    unspecified derivative blocks `C`, `\mu a`, `\mu b'` are now marked `*`.
  - `planar_geometry.tex`, proof of Lemma `art:planar-field`: the local
    branch-gradient Lipschitz constant `L` is now `M` (`L` is the lemma's transport
    constant). The endpoint gradient limits `a,b` and the limiting step direction
    `e` are now `\bar g,\bar h` and `\hat s` (`a,b,e` are the entries of `Dw`).
    The one-sided comparison is stated on `[0,1]` rather than `[a,b]`, and
    `a=\nabla f_i(x)`, `b=\nabla f_j(x)` are written out.
  - `energy.tex` (proof of Theorem `art:reciprocal-growth`) and `global.tex`
    (proof of Theorem `art:radial-equivalence`): the gradient bound `G` is now
    `\Lambda`, since `G` is the seed maximum.
  - `editorial/NOTATION_MAP.md` records the new article symbols and their
    companion counterparts.

- [x] **M4: Regularity-map table.** Table `art:regularity-map` used `\hline`; it
  now uses booktabs rules, like the article's other tables.

- [x] **M5: Abstract overstated what the planar example shows.** "an explicit
  curved-interface example requires moving comparison geometry beyond the radial
  criterion" is now "in an explicit curved-interface example, moving comparison
  geometry proves convergence although the radial criterion fails". Theorem
  `art:nonradial-example` shows that the radial criterion fails and the moving
  field succeeds; it does not show that every fixed comparison geometry fails.
  Of several equivalent wordings, this one keeps the abstract at 22 lines without
  breaking a line after "smooth–" or "curved-".

**Verification.** Both documents were rebuilt; page counts are unchanged (article
49, companion 108). The changed pages (article 1, 9, 12, 13, 16, 26, 30, 32, 38,
39, 42, 44, 45; companion PDF page 102, printed page 96) were inspected visually. LaTeX warnings are
unchanged, except that the underfull page warning on article page 32 (the table)
improved from badness 10000 to 4608. `editorial/CLAIM_LEDGER.json` and
`companion/PROOF_CORRESPONDENCE.html` were regenerated; only file hashes and line
positions changed. `python3 editorial/generate_companion.py --check` passes. The
PDFs under `release/` predate these edits.

- [x] **M6: Theorem `art:local-failure-lower` fixed $c_1=10^{-4}$, $c_2=1/2$.**
  It now holds for every $0<c_1\le1/3$, $c_1<c_2<1$ at once, like Theorem
  `art:local-failure`: one objective and one family of starts with $H_0=I$, and
  for every admissible pair the same iterates, matrices and complete decision tree.
  Proposition `art:quadratic_failure` now chooses its initial state before the pair.
  - Mathematics: every Armijo and weak-Wolfe margin is affine in its constant. At
    the seed, accepted queries pass Armijo with $c_1=1/3$, lower the value and have
    a positive new directional derivative, and rejected queries raise the value.
    These corner margins persist on one neighbourhood of the seed, so one
    stable-manifold orbit serves every pair, and copying and whitening it does not
    involve the constants.
  - Lean (`bfgs_lean_article`): `LUniformGlobal.lean`
    (`LNormalizedOracle.uniform_conditions_eventually`,
    `UniformConditions.conditions`, `LUniform.uniform_global_failure`) and
    `LUniformLocal.lean` (`LUniform.uniformSmoothLocalFailure`,
    `uniform_identity_failure`, `uniform_fixed_metric_failure`,
    `branch_not_twice_differentiable_zero`). The library's local construction
    starts from an orbit chosen for $c_1=10^{-4}$, $c_2=1/2$, so the new module
    selects its own source orbit and repeats the copying and whitening with the
    library's generic lemmas. The new objective is the same four-branch function
    whitened by the new orbit's initial matrix. All new declarations use only
    `propext`, `Classical.choice` and `Quot.sound` (`AXIOM_AUDIT.json`).
  - Article: Theorem `art:local-failure-lower`, Proposition `art:quadratic_failure`,
    Lemma `art:lower_hyperbolic` and its proof, the appendix introduction, the
    copy step, the caption of Table `art:regularity-map`, and one sentence in
    Section `art:failure`. The theorem keeps its original length, so pages 32 to
    42 keep their layout; pages 43 to 49 reflow without bad breaks, and the
    article stays at 49 pages.
  - Companion: Theorems 13.1 and 13.2, Lemma 13.1 and its proof, the setup of
    Chapter 13, the copy step, the N2/N3 summaries in Chapter 1 (logged
    transformations in `editorial/generate_companion.py`), and the Lean-review note
    in `companion/current_verification.tex`. Still 108 pages, same warnings.
  - Ledger: `editorial/lean_review_20261013/LEDGER_ADDITIONS.json` adds the new
    names to `art:local-failure-lower`, `art:quadratic_failure`,
    `art:lower_hyperbolic`, `art:lower_local_model`, `art:lower_curvature`,
    `art:lower_objective` and `art:regularity-map`, and (new `companion_additions`,
    merged by `editorial/ledger_addenda.py`) to the companion records
    `L:thm:global`, `L:thm:local` and `L:lem:agreement`.

- [x] **M7: Abstract, centered theorem** (corrected 15 October 2026). The abstract
  said that Theorem `art:centered` "applies in arbitrary dimension on compact
  initial sublevels", omitting that the sublevel must lie in the region of the
  centered representation; with only a local representation this is false (the
  coercive cap of Corollary `art:failure_polyhedral`,
  `Master.centered_representation_needs_containment`). It now reads "…on compact
  initial sublevels contained in the region of the centered representation."
  (`paper/master.tex:42-45`; `A/master/prose/003`, now `SAME_AS` the corollary
  `art:mixed-benchmark` and Theorem `art:centered`).

- [x] **M8 (article): "Branches that lose second differentiability"** (corrected 15
  October 2026). Three sentences said this of all four lower-curvature branches;
  only three of them lose it, as Theorem `art:local-failure-lower` says, and the
  fourth is a quadratic (`Verification.lower_branch_second_differentiability`,
  `LowerCurvature.branch_second_differentiability`). They now read "…with
  $C^{1,1}$ branches, three of which lose second differentiability at the
  accumulation point" (abstract, `paper/master.tex:53-55`, `A/master/prose/009`),
  "Three of the four lower-curvature branches also lose second differentiability at
  zero." (`paper/sections/verification.tex:33-34`, `A/verification/prose/017`) and
  "…the loss of second differentiability of three of the four branches at the
  accumulation point." (`paper/appendices/lower_curvature.tex:11-13`,
  `A/lower_curvature/prose/010`). The companion's recurrences were corrected the
  same day (M8 in the companion, below).

- [x] **M9: Ray identity without its range** (corrected 15 October 2026).
  Section 7 now says "$G(t(-1,16))=-t$ for $t\ge0$", as `failure.tex` does
  (`paper/sections/verification.tex:11-12`; `Verification.seed_ray`, counterexample
  for $t<0$ `seed_ray_fails_at_minus_one`; `A/verification/prose/004`).

- [x] **M10: "The next theorem" pointed to the wrong theorem** (corrected 15
  October 2026). `paper/sections/energy.tex:108-110` now reads
  "Theorem~\ref{art:reciprocal-growth} proves that, along runs with bounded
  gradients, the full update requires faster growth." The next theorem was the
  one-step hierarchy `art:minor-hierarchy`, and the paragraph did not state the
  bounded gradients that Theorem `art:reciprocal-growth` needs
  (`Energy.reciprocal_sum_superlinear_of_minimizer`; `A/energy/prose/012`).

- [x] **M11: Lemma `art:seed_cycle` and Table `art:trial_table` omitted the range
  of $(c_1,c_2)$** (corrected 15 October 2026). The lemma now says "With
  $p_j=-M_jg_j$, for every $0<c_1\le1/3$ and $c_2>0$ the entire line-search query
  list is Table~\ref{art:trial_table}." (`paper/sections/failure.tex:106-108`) and
  the caption adds "The decisions are those of the specified search for every
  $0<c_1\le1/3$ and $c_2>0$." (lines 147–148). Without the range the lemma is false:
  for $c_1=0.38$ the phase-2 trial $1/16$ fails Armijo
  (`Failure.seed_cycle_range_counterexample`); the corrected statements are
  `Failure.seed_cycle` and `trial_table`. The appendix's closing sentence
  (`A/seed_certificate/prose/012`) is now the `PROOF` item of the lemma. The
  companion's chapter D fixes its constants and does not repeat the omission.

**Verification of M7 to M11.** The article was rebuilt: still 49 pages, LaTeX
warnings unchanged (one, as before; no overfull boxes, the same eight underfull
ones). The pages whose text changed (1, 2, 7, 26, 33, 34, 43; pages 2 and 34 only
reflow) were rendered and inspected. The coverage registers were carried across
the edit with the new `editorial/lean_coverage/resync_register.py` (line numbers of
the items and of the Lean references; the hashes of the abstract, the lemma and the
table); the nine `DISCREPANCY` items are resolved (their register entries moved to
`resolved_discrepancies`), so `check_coverage.py --strict` passes on every article
file without `--allow-discrepancies`. Only docstrings of the coverage modules
changed, and `lake build` passes. `editorial/CLAIM_LEDGER.json` and
`companion/PROOF_CORRESPONDENCE.html` were regenerated (file hashes and line
positions only); `generate_companion.py --check` passes. The companion's text does
not depend on the edited files.

The companion corrections of 15 October 2026 follow. Each entry keeps the text
as found by the Lean coverage (with its proposals) and ends with what was done.

- [x] **M8 in the companion: "branches that lose second differentiability"**
  (corrected 15 October 2026).
  The article's three sentences now say that three of the four branches lose
  second differentiability (M8 under "Resolved"). The companion still says it of
  all branches:
  - Chapter 13: `companion/chapters/13_L.tex:3`, "The local finite-branch functions
    have Lipschitz gradients but lose second differentiability at the accumulation
    point", says the same (`Ch13L.branch_regularity`; line 413 of that chapter has it
    right). It is the hand-written introduction `introductions['L']` in
    `editorial/generate_companion.py`. Proposed: "…have Lipschitz gradients; three of
    the four lose second differentiability at the accumulation point."
    (`C/13_L/prose/002`)
  - Chapter 1 repeats it at `companion/chapters/01_I.tex:103` (N2): "The individual
    branches \textbf{are not twice differentiable at the accumulation point}." follows
    "One version is a maximum of four globally \(C^{1,1}\), uniformly strongly convex,
    gradient-Lipschitz branches", so it speaks of all four (`Ch13L.branch_regularity`,
    `Ch01I.n1_n2_comparison`). Proposed: "Three of the four branches \textbf{are not
    twice differentiable at the accumulation point}." Fix: a logged replacement in the
    `if module=='I':` block of `editorial/generate_companion.py`, with its own kind and
    reason (not `constant_range['I']`, whose reason concerns the line-search range), of
    `The individual branches \textbf{are not twice differentiable at the accumulation point}.`
    (frozen `bfgs_lean_stage1/master_report/latex/chapters/inventory.tex:81`, span
    `I.span.6`, occurs once). The item then becomes `LEAN`. (`C/01_I/prose/023`)
  - The research story paraphrases the abstract's sentence at
    `companion/research_story.tex:51-53`: "A different embedding preserves uniform
    strong convexity with $C^{1,1}$ branches that lose second differentiability at the
    accumulation point" (`Ch13L.branch_regularity`, `Ch01I.n2_four_branch_version`).
    Proposed, a direct edit (the file is written by hand): `branches that lose second
    differentiability at` (occurs once) → `branches, three of which lose second
    differentiability at`. (`C/research_story/prose/029`)
  Corrected: The three recurrences now say that three of the four branches lose second
  differentiability, and they say "at the minimizer" (the minimizer 0 of the local
  objective, where the bad starts accumulate) instead of "at the accumulation point".
  Chapter 13's introduction (`introductions['L']` in
  `editorial/generate_companion.py`) now reads "…have Lipschitz gradients, and three
  of the four lose second differentiability at the minimizer" (`C/13_L/prose/002`, now
  `LEAN`, `Ch13L.branch_regularity_at_minimizer`). Chapter 1 now reads "Three of the
  four branches \textbf{are not twice differentiable at the minimizer}."
  (`01_I.tex:103`; `C/01_I/prose/023`, now `SAME_AS` `C/13_L/prose/002`). The research
  story now reads "…with $C^{1,1}$ branches, three of which lose second
  differentiability at the minimizer." (`research_story.tex:52-53`;
  `C/research_story/prose/029`, now `SAME_AS` `C/01_I/prose/022`, `prose/023`).
  `12_D.tex:380` is unchanged.

- [x] **M12: Theorem `L:thm:local` denies a finite smooth-branch representation**
  (corrected 15 October 2026).
  `companion/chapters/13_L.tex:59`: the last clause, "the latter version has a
  countable polyhedral nonsmooth part, not a finite smooth-branch representation",
  read literally ("has no finite smooth-branch representation"), is false even for
  branches of the class of the theorem's first version: the step version is the
  maximum of ten globally $C^{1,1}$, uniformly strongly convex branches (quadratic
  splines on the geometric pieces; checked with exact rational arithmetic by the
  independent review, not formalized in Lean). The descriptive reading, a countable
  polyhedral nonsmooth part, is true (`Ch13L.local_failure`) and intended (line 403:
  "No claim of four smooth branches is made for this alternative"). Proposed: drop
  ", not a finite smooth-branch representation", or "…constructed from a countable
  polyhedral nonsmooth part rather than from four smooth branches". The clause is
  in the frozen span `L.span.2` (`bfgs_lean_stage1/master_report/latex/chapters/L.tex:52`):
  add a logged `if module=='L':` transformation with its own reason. The item then
  becomes `LEAN`. (`C/13_L/theorem/L:thm:local`)
  Chapter 1 repeats the clause at `companion/chapters/01_I.tex:103` (N2): "Another
  version has one constant SPD classical Hessian wherever it exists, but a countably
  piecewise-affine nonsmooth component rather than finitely many smooth branches."
  The descriptive reading is proved (`Ch13L.local_failure`,
  `Ch13L.step_decomposition`). Proposed: "…wherever it exists; it is constructed from
  a countably piecewise-affine nonsmooth component rather than from four smooth
  branches." Fix: in the same module-I block as M8's Chapter 1 fix, replace
  `wherever it exists, but a countably piecewise-affine nonsmooth component rather than finitely many smooth branches.`
  (`inventory.tex:81`, span `I.span.6`, occurs once) by
  `wherever it exists; it is constructed from a countably piecewise-affine nonsmooth component rather than from four smooth branches.`
  The item then becomes `LEAN`. (`C/01_I/prose/024`)
  Corrected: The final clause now ends "the latter version has a countable polyhedral
  nonsmooth part." (`13_L.tex:59`; `C/13_L/theorem/L:thm:local`, now `LEAN` with
  `Ch13L.local_failure`). Chapter 1 now says "…wherever it exists; it is constructed
  from a countably piecewise-affine nonsmooth component rather than from four smooth
  branches." (`01_I.tex:103`; `C/01_I/prose/024`, now `SAME_AS` the theorem).

- [x] **M13: Chapter L says it uses a fixed line-search pair**
  (corrected 15 October 2026). `13_L.tex:413`:
  "This chapter uses the fixed line-search pair displayed in this chapter; D's wider
  parameter family is not imported." is a remnant of the fixed-pair edition. Since
  the transformation of 13 October (`constant_range['L']` in
  `editorial/generate_companion.py`), the chapter fixes an arbitrary pair
  $0<c_1\le1/3$, $c_1<c_2<1$ and proves its theorems for every such pair
  (`Ch13L.global_failure`, `local_failure`), which is Chapter D's family
  (`12_D.tex:58-60`). No result is affected. Proposed: delete the sentence, or
  "Like Chapter~\ref{comp:D}, the chapter covers every pair $0<c_1\le1/3$,
  $c_1<c_2<1$." Fix: a new `constant_range['L']` entry. (`C/13_L/prose/082`)
  Corrected: The leftover sentence is now "Like Chapter~\ref{comp:D}, the chapter
  covers every pair $0<c_1\le1/3$, $c_1<c_2<1$." (`13_L.tex:413`; `C/13_L/prose/082`,
  now `LEAN`: `Ch13L.global_failure`, `local_failure`, `admissible_iff`).

- [x] **M14: Chapter D denies analyticity of all four branches**
  (corrected 15 October 2026).
  `companion/chapters/12_D.tex:380`: "Thus the branches below are in $C^{2,1}$ as
  well. This does not make them analytic or uniformly strongly convex." The fourth
  branch of `D:fullobjective`, $f_3(u,v)=v$, is linear, hence analytic
  (`Ch12D.branch3_analytic`). The rest holds (`Ch12D.not_analytic`): $f_0,f_1,f_2$
  are not analytic, and no branch, $f_3$ included, is uniformly strongly convex
  (each is constant along a nonzero direction). The same kind of slip as M8.
  Proposed: "This does not make $f_0,f_1,f_2$ analytic, nor any branch uniformly
  strongly convex." ($f_0,f_1,f_2$ are defined only in Section 12.5; "the first
  three branches" avoids the forward reference.) Fix: a logged transformation of
  module D (the sentence is in the frozen span `D.span.7`, source
  `bfgs_lean_stage1/master_report/latex/chapters/D.tex:358`). (`C/12_D/prose/047`)
  Corrected: The sentence now reads "This does not make the first three branches
  analytic, nor any branch uniformly strongly convex." (`12_D.tex:380`;
  `C/12_D/prose/047`, now `LEAN`: `Ch12D.not_analytic`; the former wording is refuted
  by `branch3_analytic`). "The first three branches" avoids the forward reference to
  $f_0,f_1,f_2$.

- [x] **M15: Companion appendix: the interval operations do not give the table's
  decimals**
  (corrected 15 October 2026). `companion/appendices/seed_certificate.tex:190`: "The
  same interval
  operations give the value enclosures in that table." is copied from the article
  (`paper/appendices/seed_certificate.tex:191`), whose Table `art:trial_table` lists
  rational enclosures of $10^4G$. The companion's table (Section 12.3,
  `12_D.tex:205-218`, with the current values in the display after it) lists
  twelve-digit decimals, and the appendix's interval operations, which run on the
  query box, cannot give them: $G(z_0)$ varies by about $4.4\cdot10^{-6}$ over that
  box, so every enclosure valid on it is wider than $10^{-6}$
  (`Companion.SeedCertificate.query_box_too_coarse`). They give enclosures of width
  at most $4\cdot10^{-4}$ of every current and trial value
  (`Companion.SeedCertificate.table_enclosure_widths`); the decimals are nearest
  roundings, proved separately (`Ch12D.trial_table`, `Ch12D.starting_values`).
  Proposed (companion only): "For each trial value $G(z_j+\alpha p_j)$ in the table
  of Section~\ref{comp:trial_table} and each current value $G(z_j)$ in the display
  after it, the same interval operations give a rational enclosure of width at most
  $4\cdot10^{-4}$; the twelve-digit decimals there are explanatory.", or drop the
  sentence. Fix: a companion-only replacement in `prepare_shared_appendix.py`.
  (`C/seed_certificate/prose/006`)
  Corrected: The sentence now reads "For each trial value $G(z_j+\alpha p_j)$ in the
  table of Section~\ref{comp:trial_table} and each current value $G(z_j)$ in the
  display after it, the same interval operations give a rational enclosure of width at
  most $4\cdot10^{-4}$; the twelve-digit decimals there are explanatory."
  (`seed_certificate.tex:190`; `C/seed_certificate/prose/006`, now `LEAN`:
  `SeedCertificate.table_enclosure_widths`).

- [x] **M16: Companion appendix: two references keep the article's structure
  (typo)**
  (corrected 15 October 2026). `prepare_shared_appendix.py` turns the article's
  subsections into
  sections and maps the table label `art:trial_table` to `comp:trial_table`, which
  labels a section heading of Chapter D. (a) `seed_certificate.tex:13-15`: "The
  matrix calculation in the next subsection" means the next section, A.2. Proposed:
  "in the next section" (the source breaks the line after "next": replace
  `'the next\nsubsection'`). (`C/seed_certificate/prose/002`) (b) Lines 185–186:
  "in the order of Table~\ref{comp:trial_table}" prints "Table 12.3", but 12.3 is a
  section (and the number of equation `D:rho`); there is no Table 12.3. Proposed:
  "in the order of the table in Section~\ref{comp:trial_table}" (replace
  `Table~\ref{art:trial_table}` before the label loop).
  (`C/seed_certificate/prose/024`) The claims hold
  (`Article.SeedCertificate.clearing_denominators`, `query_lower_bounds`).
  Corrected: (a) "in the next section" (`seed_certificate.tex:14`;
  `C/seed_certificate/prose/002`, now `SAME_AS` `A/seed_certificate/prose/002`). (b)
  "in the order of the table in Section~\ref{comp:trial_table}" (prints "Section
  12.3"; `C/seed_certificate/prose/024`, now `SAME_AS` `C/seed_certificate/disp/016`).

- [x] **M17: Chapter H's references keep its source note's numbering (typo)**
  (corrected 15 October 2026).
  `companion/chapters/07_H.tex`: "Expanding (2.1)" (line 284) and "Equation (2.1)
  then implies" (line 421) mean the Hessian form (7.2.1); "telescoping (5.2)" (line
  341) means (7.5.2); "Equation (7.3)" (line 577) and "By (7.3)" (line 599) mean
  (7.7.3); "using (7.1)" (line 655) means (7.7.1); "Formula (7.2)" (line 714) means
  (7.7.2); and the title of Section 7.5 (lines 234–235, also in the table of
  contents), "Homogeneous potential and proof of Theorem A", means Theorem 7.A. In
  the PDF, (2.1) and (5.2) are unrelated displays of Chapters 2 and 5, while
  (7.1)–(7.3) and Theorem A do not exist. Cause: `generate_companion.py:69` renumbers
  only `H.`-prefixed references, and the source
  (`bfgs_lean_stage1/master_report/latex/chapters/H.tex:200-201, 242, 294, 371, 511,
  529, 585, 644`) writes these eight without the prefix. Fix: a logged module-H
  transformation, applied before the numbering loop (lines 68–69), that adds the
  prefix (`'Theorem\nA}'` → `'Theorem\nH.A}'`, `'(2.1)'` → `'(H.2.1)'` twice,
  likewise `'(5.2)'`, `'(7.3)'` twice, `'(7.1)'` and `'(7.2)'`), each with an assert
  on its occurrence count; then check Section 7.5's heading and the table of
  contents. The mathematics holds with the intended references
  (`Ch07H.energy_identity`, `weighted_sum_finite`, `common_vector_energy_step`,
  `endpoint_pairings`, `iterate_lift`, `zero_limit_formula`, `theorem_7A`).
  Related, not an error: the bold "Lemma 7.3" (line 405) is the source's Lemma H.3;
  the chapter has no Lemma 7.1 or 7.2. (`C/07_H/prose/028`)
  Corrected: A logged module-H transformation, applied before the numbering loop, adds
  the prefix `H.` to `Theorem\nA}`, `(2.1)` ×2, `(5.2)`, `(7.3)` ×2, `(7.1)` and
  `(7.2)`. The chapter now prints (7.2.1), (7.5.2), (7.7.3), (7.7.1), (7.7.2), and
  "Homogeneous potential and proof of Theorem 7.A" as the title of Section 7.5 and in
  the table of contents (`C/07_H/prose/028`, now `LEAN`: `Ch07H.energy_identity`).

- [x] **M18: Chapter 11's references keep its source note's numbering (typo)**
  (corrected 15 October 2026).
  `companion/chapters/11_U.tex`: eight bare references print literally and point to
  nothing (companion equations and theorems are numbered c.n, and this chapter's
  equation tags are (11.10)–(11.21)). "Theorems 1 and 2" (line 171) means Theorems
  11.1 and 11.2; "(11)" (lines 269 and 340) means (11.11); "Thus (6) holds with
  $T=I$ and" (line 302) means the transport hypothesis
  $V_{k+1}=V_kT_k+s_kb_k^T+R_k$ of Theorem `M:residualtheorem` (Theorem 2.4, an
  unnumbered display at `02_M.tex:230`); "(16)--(17)" (line 352) means
  (11.16)–(11.17); "(21)" (line 415) means (11.21); "(18)" (line 433) means (11.18);
  "(20)" (line 447) means (11.20). The mathematics holds with the intended
  references: along accepted pairs, (11.14) is that transport hypothesis with
  $T_k=I$, rank-one term $s_k(\beta_ke_n)^T$ and $R_k=-\beta_kP_Ss_ke_n^T$
  (`Ch11U.transport_hypothesis`). Fix: a logged `if module=='U':` transformation in
  `generate_companion.py` on the frozen
  `bfgs_lean_stage1/master_report/latex/chapters/U.tex`; each old string occurs once:
  `covers Theorems 1 and 2.` (U.tex:153) → `covers Theorems 11.1 and 11.2.`;
  `follows from (11).` (239) → `follows from (11.11).`;
  `Thus (6) holds with \(T=I\) and` (268) → `Thus (11.14) is the transport
  hypothesis of Theorem~\ref{M:residualtheorem}, with \(T=I\), rank-one term
  \(s(\beta e_n)^T\) and` (this avoids the letter $b$, which is the hyperplane offset
  in this chapter); `This replaces (11).` (302) → `This replaces (11.11).`;
  `Equations (16)--(17)` (314) → `Equations (11.16)--(11.17)`; `bound the left side
  of` + newline + `(21).` (376–377) → `… (11.21).`; `truncate (18).` (391) →
  `truncate (11.18).`; `For the objective (20),` (405) → `For the objective (11.20),`.
  Do not replace "(11)" globally: Chapter 10 prints a bare "(11)" that means (10.11).
  If the section numbering changes as well (W13), these numbers change with it.
  (`C/11_U/prose/027`; notes on `prose/026`, `prose/029`, `prose/043`)
  Corrected: The eight replacements of the TODO entry (module U): Theorems 11.1 and
  11.2; (11.11) twice; "Thus (11.14) is the transport hypothesis of
  Theorem~\ref{M:residualtheorem}, with \(T=I\), rank-one term \(s(\beta e_n)^T\)
  and"; (11.16)--(11.17); (11.21); (11.18); (11.20). (`C/11_U/prose/027`, now `LEAN`:
  `Ch11U.transport_hypothesis`.)

- [x] **M19: Chapter 11: a cubic bound printed without its range (typo)**
  (corrected 15 October 2026).
  `11_U.tex:389-391`: "$0\le r'(v)\le6v^2$, $0\le r(v)\le6v^3$ near zero" omits
  $v\ge0$. The spike $r$ of (11.18) vanishes for $v\le0$, so $r(v)=0>6v^3$ for every
  $v<0$ (`Ch11U.spike_cubic_bound_fails`). Both bounds hold for every $v\ge0$
  (`Ch11U.spike_small_bounds`), and the chapter uses only $v\ge0$. A parallel of M9.
  Proposed: "… for $v\ge0$." Fix: in the module-U transformation of M18,
  `\] near zero. However,` (U.tex:353, occurs once) → `\] for \(v\ge0\). However,`.
  (`C/11_U/disp/026`)
  Corrected: The display is now followed by "for \(v\ge0\)" instead of "near zero"
  (`11_U.tex:391`; `C/11_U/disp/026`, now `LEAN`: `Ch11U.spike_small_bounds`).

- [x] **M20: Chapter 9 refers to a result by its source note's letter (typo)**
  (corrected 15 October 2026).
  `companion/chapters/09_C.tex:398` (Section 9.7.1, page 57 of the built companion):
  "Combining A's low affine-critical gap with Theorem 9.1 gives the following
  restricted planar basin conclusion." The printed companion numbers its chapters
  and shows no source letters; its only "A" is Appendix A (the seed certificate),
  which has no such gap. Meant: Proposition 8.1 (`A:semialgebraic`, "A low-level
  affine-critical gap"). The generator rewrites module letters only in prefixed tags,
  "Module A" phrases and citation keys. Proposed: "Combining the low affine-critical
  gap of Proposition~\ref{A:semialgebraic} with Theorem~\ref{C:thm:cluster} gives the
  following restricted planar basin conclusion." Fix: a logged transformation in the
  `if module=='C':` block of `generate_companion.py` on the frozen
  `master_report/latex/chapters/C.tex:364` (span `C.span.12`), old string
  `Combining A's low affine-critical gap with Theorem~\ref{C:thm:cluster}` (occurs
  once). The corrected claim is `Ch09C.semialgebraic_low_basin` (with
  `RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap`, the Lean form of
  Proposition 8.1, and `semialgebraic_planar_low_basin`). (`C/09_C/prose/117`)
  Corrected: It now reads "Combining the low affine-critical gap of
  Proposition~\ref{A:semialgebraic} with Theorem~\ref{C:thm:cluster}" (prints
  Proposition 8.1; `09_C.tex:398`; `C/09_C/prose/117`, now `LEAN`:
  `Ch09C.semialgebraic_low_basin`).

- [x] **M21: Chapter 5 cites "the preceding theorem" for Chapter 3's theorem (typo)**
  (corrected 15 October 2026).
  `companion/chapters/05_G.tex:59` (Section 5.1): "The preceding theorem says that this
  condition implies objective convergence for every admissible infinite full-BFGS run
  in $K$, and iterate convergence under uniqueness." In the companion the theorem
  before this sentence is Theorem `R:thm:plq` (finite polyhedral partitions,
  `04_R.tex:292`), which says nothing of the kind. Meant: Chapter 3's "One-sided
  transported-certificate convergence" (`03_T.tex:90-111`, no label; item
  `C/03_T/theorem/001`, `Ch03T.one_sided_convergence`), whose hypothesis is this
  condition. The stale reference is already in the frozen source. A parallel of M10.
  Proposed: "The one-sided transported-certificate convergence theorem of
  Chapter~\ref{comp:T} says that this condition implies …". Fix: a new logged
  `if module=='G':` block of `generate_companion.py` (with M22 and M23), old string
  `The preceding theorem says that this condition implies` (G.tex:49, occurs once).
  The content holds as intended (`Ch05G.preceding_theorem`,
  `Ch05G.sufficient_condition`). (`C/05_G/prose/008`)
  Corrected: It now reads "The one-sided transported-certificate convergence theorem
  of Chapter~\ref{comp:T} says that…" (`05_G.tex:59`; `C/05_G/prose/008`, now `LEAN`:
  `Ch05G.preceding_theorem`).

- [x] **M22: Chapter 5: no certificate "on a sublevel containing zero" (imprecision)**
  (corrected 15 October 2026).
  `05_G.tex:269` (Section 5.6): "Already $f(x)=\frac12(x+2)^2+|x|$ gives a finite
  strongly convex example with global convergence but no global certificate on a
  sublevel containing zero." Read for every sublevel containing zero, this is false
  at the boundary: $\{f\le2\}=[-2,0]$ is compact and contains $0$ ($f(0)=2$), yet each
  of its positive bands carries a certificate for $(c_1,c_2)=(1/4,1/2)$ ($W\equiv1$,
  $m=2\eta$, $C=1$, $L=0$, $\delta=1$: every differentiable point of $\{f\le2\}$ is
  negative, where $f(x)=\frac12(x+1)^2+\frac32$; `Ch05G.two_sublevel_counterexample`,
  `twoCert`, found by the independent review). The sentence also leaves the
  line-search constants implicit: with the constants $(1/8,1/4)$ that Section 5.4 uses
  for the same $f$ (line 219), every compact positive band carries $W\equiv1$; the
  claim needs $(1/4,1/2)$, stated at line 278. Proposed: "… but, for
  $(c_1,c_2)=(1/4,1/2)$, no global certificate on any sublevel containing zero in its
  interior." Fix: in the module-G block, `but no global certificate on a sublevel
  containing zero.` (G.tex:251, occurs once). The corrected claim:
  `Ch05G.shifted_global_nonnecessity_interior` (with `interior_sublevel_no_certificate`
  and `zero_mem_interior_iff`: $0$ is interior to $\{f\le b\}$ iff $b>2$); runs exist
  (`Ch05G.shiftedRun`). (`C/05_G/prose/053`)
  Corrected: It now reads "…but, for $(c_1,c_2)=(1/4,1/2)$, no global certificate on
  any sublevel containing zero in its interior." (`05_G.tex:269`; `C/05_G/prose/053`,
  now `LEAN`: `Ch05G.shifted_global_nonnecessity_interior`).

- [x] **M23: Chapter 5: no certificate "on a positive band containing this knot"
  (imprecision)**
  (corrected 15 October 2026). `05_G.tex:321` (Section 5.7): "No certificate exists on
  a positive
  band containing this knot." False when the knot lies on the boundary of the band:
  for every knot $a=(1/4)^j$, $K=\{h\le h(a)\}$ and $\eta=h(a/4)$, the band $K_\eta$
  contains $a$ and carries the certificate $W\equiv1$, $m=2h(a/4)=13a^2/80$, $C=1$,
  $L=0$, $\delta=a^2/8$ for $(c_1,c_2)=(1/4,1/2)$
  (`Ch05G.knot_band_literal_counterexample`, `edgeCert`). The argument of lines
  307–320 needs the pairs $a\pm\epsilon$ in the band, that is, the knot in its
  interior. Proposed: "No certificate exists on a positive band whose interior
  contains this knot ($b>h(a)>\eta$)." Fix: in the module-G block, `No certificate
  exists on a positive band containing this knot.` (G.tex:299, occurs once). The
  corrected claim: `Ch05G.no_certificate_knot_band` (every knot, every
  $b>h(a)>\eta>0$, via `Ch05G.small_crossing_no_certificate`). (`C/05_G/prose/063`)

  For M21–M23: no replacement adds a line, so the register's line numbers stay;
  after regenerating, update the three items' anchors and set them to `LEAN` with
  the names above, then build and inspect Chapter 5 (pages 33–39).
  Corrected: It now reads "No certificate exists on a positive band whose interior
  contains this knot ($b>h(a)>\eta$)." (`05_G.tex:321`; `C/05_G/prose/063`, now
  `LEAN`: `Ch05G.no_certificate_knot_band`).

- [x] **M24: Chapter 3 says that (S) "is exactly" (RS) (imprecision)**
  (corrected 15 October 2026).
  `03_T.tex:225`: "Condition (S) is exactly (RS), while
  $\Pi_s(z-x_*)=\Pi_s(x-x_*)$ makes (T) an equality with $L=0$." With the radial
  field $W(x)=(x-x_*)(x-x_*)^T$ of line 219 the two inequalities coincide
  ($y^TW(z)y=N^2$, $t=T$), but they cover different pairs: (S) only eligible pairs
  $x,z\in K_\eta$ with $d\le\delta_\eta$ (line 106), (RS) (`04_R.tex:53-59`) all
  differentiable $x,z\in K$ with $F_*+\eta\le F(z)\le F(x)$ and $T>0$. So (RS) gives
  (S) with the same constant (`Ch03T.rs_gives_s`, `radial_secant_exact`), and the
  conclusion at line 229 holds (`Ch03T.rs_covered`), but not conversely: for
  $F(x)=\max\{|x|,2x-1\}$, $K=\{F\le2\}$ and any $c_2<1/2$, (S) holds for the radial
  field with $C_\eta=6$ on every band and the field is a band certificate, yet (RS)
  fails at $\eta=1/2$: the pairs $x=1+\varepsilon$, $z=1-\varepsilon$ have
  $N^2/T=(1-\varepsilon)^2/(2\varepsilon)\to\infty$ and are not eligible ($t=d/2$)
  (`Ch03T.s_not_exactly_rs`). The companion itself separates the two (line 231,
  "violates even the eligible-pair radial condition"; `10_Q.tex:300`). Proposed:
  "With this $W$, (S) is the inequality of (RS) restricted to eligible pairs in
  $K_\eta$ with $d\le\delta_\eta$, so (RS) gives (S) with the same constant, while".
  Fix: a logged module-T replacement of `Condition (S) is exactly (RS), while`
  (`master_report/latex/chapters/T.tex:199`, occurs once). (`C/03_T/prose/029`)
  Chapter 1 repeats it at `companion/chapters/01_I.tex:153` (P1): "RS is the radial
  specialization \(W(x)=(x-x_*)(x-x_*)^T\)." (`Ch03T.rs_gives_s`, `Ch03T.rs_covered`,
  `Ch03T.s_not_exactly_rs`; the rest of the paragraph, "The inclusion of RS is
  strict", agrees). Proposed: "RS implies the radial specialization
  \(W(x)=(x-x_*)(x-x_*)^T\)." Fix: in the module-I block of
  `editorial/generate_companion.py`, replace
  `RS is the radial specialization \(W(x)=(x-x_*)(x-x_*)^T\).` (frozen
  `inventory.tex:119`, span `I.span.9`, occurs once); "Its equivalent inward Taylor
  condition…" then still refers to RS. The item then becomes `LEAN`.
  (`C/01_I/prose/048`)
  Corrected: Chapter 3 now says "With this $W$, (S) is the inequality of (RS)
  restricted to eligible pairs in $K_\eta$ with $d\le\delta_\eta$, so (RS) gives (S)
  with the same constant, while" (`03_T.tex:225`; `C/03_T/prose/029`, now `LEAN`:
  `Ch03T.rs_gives_s`). Chapter 1 now says "RS implies the radial specialization …"
  (`01_I.tex:153`; `C/01_I/prose/048`, now `SAME_AS` `C/03_T/prose/029`, `prose/031`).

- [x] **M25: Chapter 3's proof cites (3.3)–(3.6) as (3)–(6) (typo)**
  (corrected 15 October 2026). `03_T.tex:148`
  "Using (3)--(4), the Loewner inequality (T), and (S)," means (3.3)–(3.4); line 160
  "Divide (6) by $P_{k+1}$ and sum" means (3.6); line 165 "This contradicts (5)."
  means (3.5). The source tags these equations (T.3)–(T.6) but cites them without
  the prefix (T.tex:134, 146, 151), and `generate_companion.py:69` renumbers only
  prefixed references, so the PDF (page 23, printed 17) prints numbers that exist
  nowhere in the companion; the same slip as M17 and M18. The mathematics holds with
  the intended references (`Ch03T.hessian_form`, `annihilation_projection`,
  `trace_recurrence`, `reciprocal_budget`, `reciprocal_mean_diverges`,
  `one_sided_convergence`). Fix: logged module-T replacements, each occurring once
  in T.tex: `Using (3)--(4),` → `Using (3.3)--(3.4),`, `Divide (6) by` →
  `Divide (3.6) by`, `This contradicts (5).` → `This contradicts (3.5).`
  (`C/03_T/prose/042`)
  Corrected: The proof now prints (3.3)--(3.4), (3.6) and (3.5) (`03_T.tex:148, 160,
  165`; `C/03_T/prose/042`, now `LEAN`: `Ch03T.trace_recurrence`).

- [x] **M26: "The preceding moving-frame theorem" (Chapter 3, typo)**
  (corrected 15 October 2026).
  `03_T.tex:196`: "Unlike the preceding moving-frame theorem, there is no requirement
  that $\lambda$ be invertible or bounded away from zero." The only moving-frame
  theorem before it is Theorem `M:residualtheorem` (`02_M.tex:220-237`), which
  requires no invertible transport either (`02_M.tex:236`: "No full-rank frame or
  invertible transport is required."; `Ch02M.residual_theorem`), so the contrast is
  false for the literal referent. Meant: the moving-frame criterion stated in prose
  in Section 2.4 (`02_M.tex:196-211`), which assumes bounded norms and bounded inverse
  norms of the products $P_{k+1}=P_kT_k$ (`Ch02M.frame_criterion`). The claim about
  Chapter 3 holds: its scalar condition allows $\lambda=0$
  (`Ch03T.rank_one_degenerate`), even where $\lambda=0$ is forced
  (`Ch03T.degenerate_multiplier`). Same kind as M21. Proposed: "Unlike the
  moving-frame criterion of Section~\ref{M:energy}, …" (prints "Section 2.4"). Fix: a
  logged module-T replacement of `Unlike the preceding moving-frame theorem,`
  (T.tex:174, occurs once). (`C/03_T/prose/043`)

  For M24–M26: one `if module=='T':` block in `generate_companion.py`, after the
  `constant_range` loop and before `if module=='E':`. No replacement adds a line.
  After regenerating, update the anchors of the three items and set them to `LEAN`
  (first names `rs_gives_s`, `trace_recurrence`, `rank_one_degenerate`), update the
  TeX quotations in the docstrings of `Ch03T.trace_recurrence`, `reciprocal_budget`,
  `radial_secant_exact` and `rank_one_degenerate`, then build and inspect pages
  23–24 (printed 17–18).
  Corrected: It now reads "Unlike the moving-frame criterion of
  Section~\ref{M:energy}," (prints Section 2.4; `03_T.tex:196`; `C/03_T/prose/043`,
  now `LEAN`: `Ch03T.rank_one_degenerate`).

- [x] **M27: Chapter 6 names its source working reports by bare letters (typo)**
  (corrected 15 October 2026).
  `06_F.tex:9` (first paragraph of Section 6.1, printed page 34): "This module
  collects the nonredundant structural consequences from [M], [P], [E] and [Q]." The
  bracketed letters print literally and resolve to nothing: the companion has no
  bibliography entry or label [M], [P], [E] or [Q], [P] matches no chapter, and [M],
  [E], [Q] read as the letters of Chapters 2, 14 and 10, which they do not mean. In
  the sources they are the working reports [SM], [SP], [SE] and [SQ] of the original
  master report (`BFGS_MASTER_REPORT_LaTeX/report/master.tex:130`, module F:
  "Consolidated proofs from [SM], [SP], [SE] and [SQ]"; `report/bibliography.tex:11,
  17, 18, 19`). `generate_companion.py:29` maps the citation keys SP, SQ, SE to
  Chapter F itself and SM to Chapter M, but bare bracketed letters are not
  citations; "This module" is the sources' word for a chapter (W8). No mathematical
  content. Proposed: "This chapter collects nonredundant structural consequences of
  the general theory." (or "… of the energy theory of Chapter~\ref{comp:M}.", or
  drop the sentence). Fix: a logged `if module=='F':` replacement of `This module
  collects the nonredundant structural consequences from [M], [P], [E] and [Q].`
  (`master_report/latex/chapters/families.tex:7`, span `F.span.1`, occurs once);
  regenerate, inspect printed page 34. The item then becomes `NON_CLAIM`.
  (`C/06_F/prose/002`)
  Corrected: The sentence is now "This chapter collects nonredundant structural
  consequences of the general theory." (`06_F.tex:9`; `C/06_F/prose/002`, now
  `NON_CLAIM`).

- [x] **M28: Chapter 10's references keep its source note's numbering (typo)**
  (corrected 15 October 2026).
  `10_Q.tex`, Sections 10.5.2–10.6, printed pages 62–64: "Equation (11) proves (V)
  with $m=4\theta_{\min}^2\eta^2$" (line 115) means (10.11); "By (12), bounded
  endpoints and gradients, and $e\le d$," (line 136) means (10.12); "By (13), the
  right side is $O(d)$ uniformly on the band." (line 169) means (10.13); "Whenever it
  vanishes, the second vanishes by (7)." and "There are finitely many segments and
  pairs, proving (16)." (line 198) mean (10.7) and (10.16); "An especially simple
  scaling for (8) is" (line 238) means (10.8). No companion equation is numbered (7),
  (8), (11), (12), (13) or (16); the six print literally. Cause:
  `generate_companion.py:69` renumbers only `Q.`-prefixed references, and the source
  writes these six without the prefix. Same slip as M17, M18 and M25; the
  mathematics holds with the intended references. Fix: a logged `if module=='Q':`
  block applied before the numbering loop (lines 68–69) that adds the prefix, with
  these strings of `master_report/latex/chapters/Q.tex`, each occurring once (assert
  the counts): `(11)` (Q.tex:101), `(12)` (:118), `(13)` (:147), `(7)` and `(16)`
  (:176), `(8)` (:212); the existing substitution then prints (10.11), (10.12),
  (10.13), (10.7), (10.16), (10.8). Only Q's text is touched, so Chapter 11's bare
  "(11)" (M18) is unaffected. Regenerate, inspect printed pages 62–64. Lean:
  `Ch10Q.secant_visibility`, `radial_error`, `multiplier_estimates`,
  `segment_bound_facts`, `branch_change`, `example_scale`. (`C/10_Q/prose/014`)
  Corrected: A logged module-Q transformation, applied before the numbering loop, adds
  the prefix `Q.`. The chapter now prints (10.11), (10.12), (10.13), (10.7), (10.16)
  and (10.8) (`C/10_Q/prose/014`, now `LEAN`: `Ch10Q.secant_visibility`).

- [x] **M29: Chapter 14 refers to Chapters 13 and 4 by their source letters (typo)**
  (corrected 15 October 2026).
  (a) `companion/chapters/14_E.tex:18` (Section 14.1, printed page 89): "The
  stable-manifold conclusion in L follows from the actual return map and a proved
  analytic argument, not a numerical starting vector assumed to lie on that manifold."
  (b) `14_E.tex:136` (Section 14.3.11 "R-interpretation", printed page 91): "The
  explicit four-piece objective in R is a new specified reconstruction with an actual
  full-BFGS failure run; it is not asserted to be an unidentified historical
  objective." "L" and "R" are the source letters of Chapter 13 (lower curvature) and
  Chapter 4 (radial modeling; the four-piece objective is built in Section 4.3). The
  printed companion numbers its chapters 1 to 14 and its appendices A and B, so the
  two labels resolve to nothing; the suite names of Section 14.3 ("L-hyperbolicity",
  "R-interpretation", …) do not define them. The letters are used as places ("in L",
  "in R"), so this is the pattern of M20 and M27, not of W22 (letters naming
  objects). The generator rewrites module letters only in prefixed tags, "Module X"
  phrases and citation keys. Proposed: "in Chapter~\ref{comp:L}" and "in
  Chapter~\ref{comp:R}". Fix: two logged transformations in the `if module=='E':`
  block of `editorial/generate_companion.py`, on the frozen
  `master_report/latex/chapters/verification.tex` (assert the counts): (a) line 7,
  span `E.span.2`: `The stable-manifold conclusion in L follows` (occurs once) →
  `The stable-manifold conclusion in Chapter~\ref{comp:L} follows`; (b) line 73, span
  `E.span.15`: `The explicit four-piece objective in R is` (occurs once) → `The
  explicit four-piece objective in Chapter~\ref{comp:R} is`. No line is added.
  Regenerate, inspect printed pages 89 and 91. The mathematics holds: (a)
  `LowerCurvature.stable_manifold_positive_scale`, `Ch13L.global_failure`,
  `LowerCurvature.quadratic_failure`; (b) `Ch04R.fourPiece_failure_run`,
  `reconstructedFourPieceFailure`, `Ch04R.fourPiece_objective_formula`.
  (`C/14_E/prose/013`, `C/14_E/prose/061`)
  Corrected: They now read "in Chapter~\ref{comp:L}" and "in Chapter~\ref{comp:R}"
  (`14_E.tex:18, 136`; `C/14_E/prose/013`, now `SAME_AS`
  `A/lower_curvature/prose/036`, `C/13_L/theorem/L:thm:global`; `C/14_E/prose/061`,
  now `SAME_AS` `C/04_R/prose/047`, `disp/033`).

- [x] **M33, companion part (reader point R-F-1): the initial point of the chosen
  orbit** (corrected 15 October 2026). Chapter 13 now puts the initial point in the
  neighbourhood too: "so that \emph{the initial point and all queries of the orbit}
  lie inside it" (`13_L.tex:237`), "whose initial point and accepted and rejected
  queries are all in that neighborhood" (line 355), "applies at the initial point and
  to every query" (line 363). New Lean: `Ch13L.chosen_orbit` and
  `Ch13L.local_model_along_orbit` (`C/13_L/prose/062` and `prose/065`, `SAME_AS` →
  `LEAN`; `proof/002` cites `global_failure`, whose `∀ k, x k ∈ V` includes the
  initial point). The article's recurrence (Proposition `art:quadratic_failure`,
  `A/lower_curvature/prose/027-028`) is still open.

**Verification of the companion corrections.** The companion was rebuilt: still 108
pages, LaTeX warnings unchanged (the same three underfull hboxes, no undefined
references, no overfull boxes). The text changed on 75 pages: 72 contain edits (PDF 2,
5, 7–10, 12–18, 23–26, 28–31, 33–35, 37, 38, 40, 42–45, 47–53, 55, 58, 59, 63, 67–70,
73–80, 84, 85, 87, 88, 90–98, 100–104), and pages 3, 11 and 99 only reflow. Every
replacement was rendered at 110 dpi and inspected, every new `\ref`/`\eqref` prints
the intended number, the table of contents shows "Theorem 7.A", and Chapters 12 and 13
print each equation number once ((12.1)–(12.14), (13.1)–(13.13)).
`generate_companion.py --check` passes, and each new string occurs exactly once in the
output with each old string gone. The registers were carried across the edits with
`resync_register.py` (no line moved; 11 accepted hashes). The 25 companion
`DISCREPANCY` items are resolved (entries under `resolved_discrepancies`), and
`check_coverage.py --strict` passes on every companion file without
`--allow-discrepancies` (and on every file overall). In `bfgs_lean_article`, 18
companion coverage modules changed (docstrings; 9 new declarations in `Ch13L` and
`Ch04R`; no existing statement changed), and each compiles with `lake env lean`
without errors or warnings. `editorial/CLAIM_LEDGER.json` and
`companion/PROOF_CORRESPONDENCE.html` were regenerated (file hashes and the title
"Theorem 7.A" only). The independent review found the work sound; its findings F1–F7,
F9 and F10 and its observations O1–O3 were applied the same day (W44–W46 and further
places of W8, W10, W17, W25, W37). F8 (W31) was settled the same day by adding the
coverage registers to the claim/proof index.

The corrections from the line-by-line reading of the article (15 October 2026)
follow. Each entry keeps the text of the finding and ends with what was done.

Six reader agents read the article line by line on 15 October 2026 (step 2 of the plan
in `AGENTS.md`), each one group of files, on the text of commit `c8db802` (before the
corrections M7 to M11; the line numbers below are those of that commit). They checked
every proof step, hypothesis, reference, symbol and number (recomputed exactly where
possible), compared the statements with the Lean registers, and looked at the built
PDF. Their reports, with the exact old and new strings of every finding, occurrence
counts and register items, are in `editorial/line_by_line_reading_20261015/` (findings
`R-A-1` …, `R-F-13`), with the coordinator's decisions (`TRIAGE.md`). No reader found
a false theorem, lemma or proposition, or a wrong number: every number of Section 6
and Appendices C and D was recomputed and holds. The findings are hypotheses left out
of summaries and tables, steps left out of proofs, a statement weaker than its later
use (M33), references, notation, typesetting and language. The items below group the
accepted findings. All were applied on 15 October 2026; what was left to the author is
listed under "Questions for the author".

- [x] **M30: "At the accumulation point" where the minimizer is meant**
  (corrected 15 October 2026). The
  abstract (`master.tex`, the sentence of M8), the header of Table
  `art:regularity-map` and two sentences of Section 6 (`failure.tex:465`, `506`,
  `513`) and `lower_curvature.tex:13` place the loss of second differentiability "at
  the accumulation point". In the abstract nothing has been said to accumulate, and a
  reader takes the limit of a failing run, $\bar x_\ell\ne0$, where every branch is
  smooth. The branches fail to be $C^2$ only at $0$, the minimizer, where the copies
  accumulate (Theorem `art:local-failure-lower` says "at zero", the introduction "at
  the minimizer"). Proposed: "at the minimizer" (in Section 6 once with "where the
  copies accumulate"). The companion had the same phrase at `13_L.tex:3`,
  `01_I.tex:103` and `research_story.tex:52-53`, corrected with M8's companion
  recurrences on 15 October; `01_I.tex:107` and `13_L.tex:413` remain.
  (R-A-1, R-E-2; `A/master/prose/009`, `A/failure/table/art:regularity-map`,
  `A/lower_curvature/prose/010` and the Section 6 prose items.)
  Corrected: The abstract now reads "…with $C^{1,1}$ branches, three of which lose
  second differentiability at the minimizer." (`paper/master.tex:53-55`), the last
  column of Table `art:regularity-map` is headed "At the minimizer"
  (`paper/sections/failure.tex:474`), Section 6 says "…prevents second
  differentiability at the minimizer, where the copies accumulate." and "…which
  regularity survives at the minimizer." (`failure.tex:517-519`, `523-527`), and
  Appendix D "…the loss of second differentiability of three of the four branches at
  the minimizer." (`paper/appendices/lower_curvature.tex:11-13`). The companion's
  remaining recurrences now read "N2 has positive lower curvature and less
  differentiability at the minimizer." (`01_I.tex:107`) and "The first three branches
  … fail to be twice differentiable at the minimizer." (`13_L.tex:413`), as logged
  transformations of modules I and L. (R-A-1, R-E-2; `A/master/prose/009`,
  `A/failure/table/art:regularity-map`, `A/failure/prose/068`, `prose/070`,
  `A/lower_curvature/prose/010`, `C/01_I/prose/028`, `C/13_L/prose/083`.)

- [x] **M31: Table `art:positive-outcomes` omits two hypotheses**
  (corrected 15 October 2026). (a) The caption
  infers global convergence for $u^2+|v|$ from compact sublevels alone; the
  centered representation on all of $\R^2$ is needed too (another place of M7).
  (b) The $\lambda\norm{x}_1$ row promises whole-sequence convergence, which
  Theorem `art:polyhedral` gives only with a unique minimizer: for
  $\tfrac12(x_1+x_2-1)^2+\tfrac12\norm{x}_1$ the minimizers form a segment.
  Proposed: "compact sublevels and a centered representation on all of $\R^2$", and
  "($\lambda>0$, unique minimizer)". (R-A-2, R-A-3; `A/geometry/prose/031`,
  `A/geometry/prose/029`.)
  Corrected: The caption reads "The benchmark $u^2+|v|$ has compact sublevels and a
  centered representation on all of $\R^2$, so the first row gives global
  convergence." and row 3 "…squared loss plus $\lambda\norm{x}_1$ ($\lambda>0$, unique
  minimizer)" (`paper/sections/geometry.tex:79-80`, `88-90`). Lean:
  `Geometry.benchmark_centered_global` (new): every sublevel of $u^2+|v|$ is compact,
  $0$ minimizes it, and on $\R^2$ it is $\psi+\gamma(\cdot-0)$ with $\psi=u^2$ convex
  and locally $C^{1,1}$ and $\gamma=|v|$ convex and positively homogeneous of degree
  one, and every admissible run converges in value and iterates. (R-A-2, R-A-3;
  `A/geometry/prose/031`, `prose/029`.)

- [x] **M32: M10 and M11 at further places**
  (corrected 15 October 2026). (a) The opening of Section 3
  (`energy.tex:8-9`), "persistent missed progress cannot be paid for by a bounded
  secant cost per iteration", needs bounded gradients, like M10: add "when the
  gradients are bounded" (`A/energy/prose/005`). (b) The induction display after the seed lemma and
  the corollary that follows it (`failure.tex:184-209`) state no line-search range; for
  $c_1>r_2\approx0.3752$ they fail, as M11 shows: add "For every fixed pair
  $0<c_1\le1/3$, $c_1<c_2<1$". (c) "Admissible pair" (`failure.tex:495`,
  `lower_curvature.tex:88`, `104`, `182`, `295`) is never defined; read with
  Definition `art:admissible` ($0<c_1<c_2<1$) Lemma `art:lower_hyperbolic` would be
  false. Proposed: define the term where Appendix D fixes the range
  (`lower_curvature.tex:14`) and write the range out at `failure.tex:495`. Check that
  the Lean statements of these items carry the range. (R-B-6, R-E-1, R-F-2.)
  Corrected: (a) Section 3 opens "The matrix hierarchy then shows that, when the
  gradients are bounded, persistent missed progress cannot be paid for…"
  (`paper/sections/energy.tex:8-10`). (b) The induction (26) and Corollary
  `art:failure_polyhedral` begin "For every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$, …"
  (`failure.tex:192-193`, `209`). (c) Appendix D defines the term: "The line-search
  constants are any fixed pair $0<c_1\le1/3$, $c_1<c_2<1$ (an \emph{admissible pair})"
  (`lower_curvature.tex:13-14`), and Section 6.6 writes the range out
  (`failure.tex:505`). The Lean statements already carried the range
  (`Failure.cone_orbit`, `Failure.failure_polyhedral`, `LUniform.Admissible`). (R-B-6,
  R-E-1, R-F-2; `A/energy/prose/005`, `A/failure/disp/010`,
  `A/failure/corollary/art:failure_polyhedral`, `A/failure/prose/063`,
  `A/lower_curvature/prose/011`.)

- [x] **M33: Appendix D: the initial point of the seed orbit must lie in $V$**
  (corrected 15 October 2026).
  Proposition `art:quadratic_failure` (`lower_curvature.tex:49-50`) puts only the
  accepted and rejected query points in the neighbourhood $V$. Section D.3
  (`293-296`, `305-306`) starts copy $\ell$ at $\bar x_\ell+a_\ell x_0^{\rm seed}$ and
  uses the local model there, so it needs $x_0\in V$, which neither the statement
  nor its proof (`176-180`) gives. The repair is one more map of the same kind,
  $w\mapsto\tau z$. The Lean library proves the stronger statement
  (`LUniform.orbit_exists`, `LUniform.source_spec`: every iterate in $U$;
  `LUniform.uniform_global_failure`; `copy_runs`); the register's reading
  `LowerCurvature.quadratic_failure` has to gain `x 0 ∈ V`. Four replacements in
  `lower_curvature.tex`; the companion repeated the slip at `13_L.tex:237`, `355`,
  `363`; it was corrected there on 15 October (see "M33, companion part" under
  "Resolved"). (R-F-1;
  `A/lower_curvature/proposition/art:quadratic_failure`, `proof/002`, `prose/027`,
  `prose/028`, `disp/021`.)
  Corrected: Proposition `art:quadratic_failure` now ends "…its initial point and all
  accepted and rejected query points are differentiable and belong to $V$."
  (`paper/appendices/lower_curvature.tex:49-51`); its proof adds the initial-point map
  $w\mapsto\tau z$ to the maps continuous at $P_*$ with value $0$ and concludes "The
  initial point and every physical query lie in $V$." (`180-185`); Section D.3 chooses
  an orbit "whose initial point and queries all lie in this neighborhood" (`299-301`)
  and says "Equation~\eqref{art:lower_local_model} applies at the initial point and to
  every query because the whole chosen seed orbit lies in its domain." (`311-312`).
  Lean: `LowerCurvature.quadratic_failure_initial_point` (new; from
  `LUniform.uniform_global_failure`); `quadratic_failure` keeps the statement before
  the correction (cited by `C_14_E`); `copy_runs` already placed the initial point in
  the local domain (so does `copy_runs_from_one`, new, the copies for $\ell\ge1$), and
  `copy_transfer` holds at every step, the start included. The companion's recurrences
  (`13_L.tex:237`, `355`, `363`) were corrected the same day. (R-F-1;
  `A/lower_curvature/proposition/art:quadratic_failure`, `proof/002`, `prose/027`,
  `prose/028`, `disp/021`.)

- [x] **M34: Proof steps left out**
  (corrected 15 October 2026). Each fix adds a clause or a sentence.
  - Lemma `art:gram-compression` (`matrix_algebra.tex:56-61`): why adding
    $\rho aa^T$ gives the compression $Z^TH_+Z$ ($Z^Tv=a$), and that the Schur
    complement gives $u\le q$ (R-B-2).
  - Theorem `art:reciprocal-growth` (`energy.tex:179`): $\beta_k$ is not defined,
    and the contraction holds only for $k\ge J$ (R-B-5; the companion repeats it at
    `02_M.tex:129`).
  - Corollary `art:radial-convergence` (`global.tex:103-109`): stated under either
    condition, proved for the radial one; cite Theorem `art:radial-equivalence`
    (R-C-1).
  - Theorem 4's case split (`global.tex`): the identity $T-N=(g-h)^Tr_x$ for the
    reversed pair and the choice $\tau=\theta$ are not stated (R-C-4); the constant
    $\theta=1/2$ is used but not named in Theorem 5's proof and at
    `local.tex:65-75` (R-C-5).
  - Theorem 8 (`local.tex:251-260`): $\lambda^2\le1+Ld$ is used for every close
    eligible pair, while Lemma `art:planar-field` gives it for $d\le1$; add $d\le1$
    and $s_k\to0$, $d_k\to0$ on the tail (R-D-1).
  - Seed certificate (`seed_certificate.tex:112-123`): "Their sum is
    $\widetilde\rho I$" skips the projected term $\Pi(C+\beta E)\Pi=\widetilde\rho\Pi$
    (R-E-3; the companion's appendix is generated from this file).
  - Lemma 5 (`failure.tex`): convexity follows from $\varphi_b''\ge0$, not from the
    sign of $\varphi_b'$ (R-E-4).
  - The weak-Wolfe test needs the gradient at the trial point; say that every point
    queried in Section 6 is differentiable (R-E-10).
  Corrected: Lemma `art:gram-compression`: "Since $Z^Tv=a$, the value
  $\rho=\alpha/(\beta q)$ gives the compression $Z^TH_+Z$. The Schur complement of $A$
  in $\operatorname{Gram}_H(g,Z)$ gives $u\le q$ (and $u\ge0$ since $A\succ0$)"
  (`paper/appendices/matrix_algebra.tex:58-65`). Theorem `art:reciprocal-growth`:
  display (17) defines $\beta_k=-y_k^TH_kg_k/q_k=t_k/d_k\ge\omega$, and "For $k\ge J$,
  multiply…" (`paper/sections/energy.tex:180-183`, `196`; companion `02_M.tex:129`).
  Theorem 4: the inward model "at $z$, both evaluated at $z-\tau r_z$", "The reversed
  pair has radial numerator $(g-h)^Tr_x=T-N\ge|N|$", "the choice $\tau=\theta$"
  (`global.tex:72-88`). Corollary `art:radial-convergence`: "By
  Theorem~\ref{art:radial-equivalence} we may assume \eqref{art:radial-condition}; it
  gives secant control on eligible pairs in $K_\eta$, since these have $F(z)<F(x)$ and
  $T=t>0$." (`global.tex:108-110`). Theorems 5 and 7: "…and $\theta=1/2$ for every
  band" (`global.tex:166-167`, `local.tex:74-75`). Theorem 8: eligible pairs "with
  $d\le1$" and "with $s_k\to0$ and $d_k\to0$" (`local.tex:253`, `261`). Appendix C:
  the projected term $\Pi(C+\beta E)\Pi=\widetilde\rho\,\Pi$ and the rank-one term
  $\widetilde\rho(I-\Pi)$ (`seed_certificate.tex:117-129`; the companion's appendix is
  generated from it). Lemma 5: "The second derivative is nonnegative on every piece:
  …" (`failure.tex:343-346`). Section 6: "Every queried point in the construction is
  differentiable, so the Wolfe test is always defined." (`failure.tex:36-37`, new item
  `A/failure/prose/071`). (R-B-2, R-B-5, R-C-1, R-C-4, R-C-5, R-D-1, R-E-3, R-E-4,
  R-E-10.)

- [x] **M35: References**
  (corrected 15 October 2026). `introduction.tex:36-38` "The following paragraph"
  means
  the paragraph after the corollary (R-A-6); `global.tex:60` "proved in
  Theorem~\ref{art:certificate}": the bound is in its proof (R-B-7, R-C-2);
  `energy.tex:144`: Lemma `art:gram-compression` is in Appendix A (R-B-8);
  `energy.tex:291`: the equation range starts one equation late (R-B-9);
  `local.tex:3` "The global theorem" is Theorem `art:centered` (R-D-7);
  `lower_curvature.tex:25` points to Appendix C for $G$, defined in Section 6
  (R-F-5); Figure `art:gradient-geometry` and Table `art:regularity-map` are never
  cited (R-A-10); "This condition" (R-C-8).
  Corrected: "The paragraph after that corollary" (`introduction.tex:37`); "The
  subgradient bound was shown in the proof of Theorem~\ref{art:certificate}." with the
  unused Lipschitz clause removed (`global.tex:62`; R-C-3);
  "Lemma~\ref{art:gram-compression} of Appendix~\ref{art:matrix-algebra}"
  (`energy.tex:146`); "\eqref{art:visibility}--\eqref{art:transport}"
  (`energy.tex:293`); "Theorem~\ref{art:centered} requires" (`local.tex:3`); "Use the
  slopes $g_0,g_1,g_2$ and the function $G$ of Section~\ref{art:failure}"
  (`lower_curvature.tex:26`); Figure `art:gradient-geometry` and Table
  `art:regularity-map` are cited (`geometry.tex:9`, `36`; `failure.tex:523`);
  "Condition~\eqref{art:inward-condition} controls only inward first-order modeling
  error" and both failing conditions named (`global.tex:115`, `119-122`). (R-A-6,
  R-B-7, R-C-2, R-B-8, R-B-9, R-D-7, R-F-5, R-A-10, R-C-8.)

- [x] **M36: Section 7: the open question and the verification paragraph**
  (corrected 15 October 2026). (a) "The
  broader local question for finitely many uniformly strongly convex $C^2$ branches
  remains open here" passes over the nondegenerate planar case settled by Corollary
  `art:planar-max`, and the examples concern the weak-Wolfe implementation with
  $0<c_1\le1/3$ (R-A-5; `A/verification/prose/025`, which stays `OPEN`, and
  `prose/026`). (b) The verification paragraph (`verification.tex:59-63`, also
  `introduction.tex:124-126`) describes the records of 13 September only; add the
  axiom audit and the kernel replay (R-A-7; `A/verification/prose/027`,
  `A/introduction/prose/049`). The release receipts are refreshed by the release run;
  whether the article mentions the coverage registers: author.
  Corrected: (a) "The local question for finitely many uniformly strongly convex $C^2$
  branches remains open here outside the nondegenerate planar case of
  Corollary~\ref{art:planar-max}." and "The examples concern the specified weak-Wolfe
  implementation with $0<c_1\le1/3$ and exceptional deterministic starts"
  (`paper/sections/verification.tex:57-62`; `A/verification/prose/025` stays `OPEN`).
  (b) "…compiler, axiom and kernel-replay audits," (`verification.tex:67`); the
  companion reports the kernel replay since W30. Left for the author: whether the
  article mentions the coverage registers. (R-A-5, R-A-7.)

- [x] **M37: The AI-use statement leaves out the October work**
  (applied 15 October 2026). The article's
  statement points to `companion/master.tex:63` and
  `editorial/AI_AND_AUTHOR_ACTIONS.md`, which name only OpenAI ChatGPT/Codex; the
  Lean coverage, the reviews and the corrections of 13 to 15 October 2026 were done
  with Anthropic Claude in OpenCode. Proposed: add this to both (a factual
  addition); the author confirms the wording in step 3. (R-A-8;
  `A/verification/prose/030`.)
  Applied: `companion/master.tex:63-64` reads "OpenAI ChatGPT/Codex systems and, from
  October 2026, Anthropic Claude (in OpenCode) assisted mathematical development and
  correction, …"; `editorial/AI_AND_AUTHOR_ACTIONS.md` adds "From 13 October 2026,
  Anthropic Claude (in OpenCode) assisted with the Lean review, the Lean coverage of
  every claim of the article and the companion, the reviews of the manuscripts and the
  corrections that followed them." and the same addition to its draft disclosure.
  (R-A-8.)

- [x] **M38: Notation**
  (corrected 15 October 2026). "Whitening" and $A$ used in Section 7 before Appendix D
  defines them (R-A-4); $\operatorname{Gram}_H$ undefined (R-B-1); "$\det A(r-z)$"
  (R-B-3; also `02_M.tex:87`, `91`); R-B-4; $\frac{m}{\overline P}$ (R-B-11); $T$ of
  Section 4 is $t$ of Section 3, "radial numerator" undefined (R-C-7); "noncritical"
  for "non-affine-critical" and "the compact level set" (R-D-2); symbols reused in one
  argument (R-D-3); Section 6.6 uses Appendix D's $a_\ell$, $\bar x_\ell$ and an
  undefined $C_*$ (R-E-5); R-E-9; eigenvalues "at $P_*$" (R-F-3); $z_m,\tau_m$ not
  introduced (R-F-4); the shape map not written down (R-F-6).
  Corrected: Section 7 says "the fixed change of coordinates of
  Appendix~\ref{art:lower_curvature}" and "$x=Az$ with $A=(H_0^{\rm seed})^{1/2}$"
  (`verification.tex:25-33`); Appendix A defines $\operatorname{Gram}_H(g,Z)$ and
  $\operatorname{Gram}_H(g,y,Z)$ and writes $(r-z)\det A$ (`matrix_algebra.tex:41-47`,
  also `02_M.tex:87`, `91`), names $Z$ an orthogonal matrix with $A^{-1}=Z^TH^{-1}Z$
  (`67-69`); Section 4: "Here $T$ is the quantity $t$ of Section~\ref{art:energy}, and
  $N$ is the \emph{radial numerator}." (`global.tex:28-29`, new item
  `A/global/prose/042`); "non-affine-critical", "that compact part of the level",
  $B_\rho$, the transport factor (`local.tex`), the segment parameter and exp
  (`planar_geometry.tex:144`, `190`); Section 6.6 recalls Appendix D's $a_\ell$, $\bar
  x_\ell$, $C_*$ (`failure.tex:508-510`); R-E-9 (a)–(d), (f) in Lemma 4 and Appendix
  C; "at $P_*$", $w_m$, the shape map and $v$ in Appendix D. R-D-3 (d) was left ($t$
  is also the level in Section 5.2 and Appendix B; renaming it only in Theorem 8 would
  make the two disagree, and the two meanings never meet in one formula), and so were
  R-D-3 (e) (the corner index $j$ does not occur in the secant paragraph, which names
  its branches itself) and R-E-9 (e) (the ramp coordinate $v$ and the coordinate $v$
  of $F(u,v)$ are in different subsections). (R-A-4, R-B-1, R-B-3, R-B-4, R-C-7,
  R-D-2, R-D-3, R-E-5, R-E-9, R-F-3, R-F-4, R-F-6.)

- [x] **M39: Typesetting, figures and tables**
  (corrected 15 October 2026). Figure 1(b): the zero marker touches
  the hull, and the caption misdescribes an arrow (R-A-9); the number of equation (1)
  on its own line (R-A-12); Table 1 layout and two undefined terms (R-A-13); the
  invisible paragraph break in Theorem 11 (R-A-14, R-E-8); no end-of-proof marks
  (`\smartqed` without `\qed`, R-C-11); line breaks inside short formulas (R-D-4,
  R-F-13); Figure 2's caption "as indicated" (R-E-6); Table 3 columns, displays (44)
  and (46), Figure 3 labels (R-E-8); a period inside display (49) (R-F-7); decimals
  without a leading zero (R-F-12).
  Corrected: Figure 1: smaller zero marker and the caption "Zero lies just above the
  edge $[g_1,g_0]$, at distance $1/\sqrt{257}$ from the hull. Solid arrows indicate
  gradients and the dashed arrow a common descent direction; none is a BFGS step."
  (new item `A/geometry/prose/043`); equation (1) with its qualifier in the text;
  Table 1 ragged-right, spaced, placed at the top of page 5, middle cell "Compact
  initial sublevel where the representation holds", "admissible runs"; the same
  undefined term at `paper/sections/local.tex:99-100` now reads "the neighborhood $U$
  of Theorem~\ref{art:polyhedral}"; Theorem 11 paragraph indent and space after it;
  end-of-proof marks in all 28 proofs; unbreakable $F:\R^2\to\R$ (Corollary 7,
  Appendix B) and two short formulas of Appendix D; Figure 2's caption gives the
  vertical-to-horizontal ratios; Table 3 ragged-right; displays (44)–(46) on two
  lines; a comma ending display (49); 0.038 and 0.039. R-D-4 was not applied to
  Theorems 5 and 8 (the unbreakable formula gives an overfull line in Theorem 5 and
  leaves the head of Theorem 8 alone on a stretched line), and R-E-8 (e) was left (the
  labels of the schematic inset of Figure 3 would mean regenerating both committed
  figure PDFs with `generate_figures.py`). (R-A-9, R-A-12, R-A-13, R-A-14, R-C-11,
  R-D-4, R-E-6, R-E-8, R-F-7, R-F-12, R-F-13.)

- [x] **M40: Bibliography, citations, metadata**
  (corrected 15 October 2026). Citation order, a stray `\par`, a
  publication date (R-A-15); preprint citations repeat the author's name, unused
  preprint keys (R-A-16); the PDF keywords differ from the printed ones, and the
  edition date (release run) (R-A-17); two citations run together (R-B-10). Author:
  whether to sort the reference list alphabetically.
  Corrected: Citations \cite{FND_N92,FND_BN89,FND_P76} in order
  (`introduction.tex:6`); stray `\par` removed and "(2026); published online 8 May
  2026" (`bibliography.tex`); PDF keywords as printed (`master.tex:30`); a comma
  between the two citations of `energy.tex:212`; `paper/preprint_references.tex` now
  defines each preprint once (`\bfgsdefinepreprint`), and the starred `\preprintcite*`
  omits the authors right after the sentence names them (Xie–Wächter, Diao,
  Lewis–Overton, Bogosel, Dyatlov); the unused keys LL18 and JM25v2 are gone. Left for
  the author: alphabetical order of the reference list; the edition date is set by the
  release run. (R-A-15, R-A-16, R-A-17, R-B-10.)

- [x] **M41: Language**
  (corrected 15 October 2026). "At every scale", "certified perturbed orbit" (R-A-11);
  R-A-18 (a)-(f); an unused Lipschitz clause (R-C-3); the Lebesgue-number sentence
  (R-C-6); "In particular", "Equivalently" (R-C-9, R-C-10); a tautology at
  `local.tex:39-40` (R-D-5); "the numerator" without antecedent (R-D-6); "classical
  Hessian" (R-E-7); R-E-11; R-F-8 to R-F-11.
  Corrected: "At infinitely many shrinking scales", "Along the perturbed orbit of
  Proposition~\ref{art:quadratic_failure}" (`verification.tex:16`, `47`); R-A-18
  (a)–(f) (`introduction.tex:34`, `46-48`, `122-124`, `geometry.tex:63`,
  `master.tex:46`, `negative_lower.tex:7-8`), where (e) reads "the value-convergence
  theorem for a broader homogeneous family in Chapter~7 of the complete companion
  (introduced at the end of this section) does not replace that finite escape result";
  the unused Lipschitz clause (R-C-3, with M35); R-C-6, R-C-9, R-C-10
  (`global.tex:153-155`, `132`, `225-227`); "Near $x_*$ only cells containing $x_*$
  occur: the finitely many closed cells that miss $x_*$ avoid a ball around it."
  (`local.tex:39-40`); "Since $D'(\theta)=\det(s,Dw\,s)$ there, the numerator of
  $D'/D$" (`planar_geometry.tex:154`); "In Theorem~\ref{art:local-failure-lower} and
  Table~\ref{art:regularity-map}, a Hessian is the classical one"
  (`failure.tex:493-496`); R-E-11 (`failure.tex:6`, `60`, `seed_certificate.tex:131`);
  R-F-8 to R-F-11 (Appendix D).

**Verification of M30 to M41 and W47.** Both documents were rebuilt; page counts are
unchanged (article 49, companion 108). The article's text changed on every page except
page 10 (mostly reflow and the new end-of-proof marks); every changed page was
rendered at 110 dpi and inspected, and so were the companion's changed pages 3, 8, 16,
17, 93 and 100–102. LaTeX warnings: the article's eight underfull boxes (six hbox, two
vbox) are gone and none is new; the companion keeps two of its three underfull hboxes
(the one in the appendix's matrix-identity paragraph is gone); no overfull box, no
undefined reference or citation, no hyperref warning in either. An independent review
of the corrections found two gaps in the text (the first mention of the companion in
the introduction; the local model at the start of each copy in Appendix D), a missing
conjunct in a new Lean statement and a false docstring sentence; they were fixed the
same day, together with the undefined term at `local.tex:100`, and the article was
rebuilt again (pages 2, 18 and 48 changed and were inspected; no warning). The
coverage registers were carried across the edits with `resync_register.py` (one
`--write` run against HEAD with 62 accepted hashes, and one against the saved copy for
the fixes), then by hand (anchors, notes, three new items, Lean lists, and the bare
line references in notes and docstrings); all 1681 prose anchors lie within their
lines. `check_coverage.py --strict` passes on every article file without
`--allow-discrepancies` and on every companion file, and the full checker reports no
problem. Three Lean declarations were added and no existing statement changed; every
changed Lean module compiles, and the new declarations use only `propext`,
`Classical.choice` and `Quot.sound`. The new companion transformations are logged at
the ends of their module lists. `editorial/CLAIM_LEDGER.json` and
`companion/PROOF_CORRESPONDENCE.html` were regenerated; `generate_companion.py
--check` passes. The PDFs under `release/` predate these edits.
