# TODO: Manuscript review

Review date: 13 October 2026. Reviewer: AI assistant (Claude), at the author's request.

Scope: notation, typesetting and claim wording in the article (`paper/`) and, from
M12 on and in the W items, in the companion (`companion/`). The seed
numerics were re-checked in the first reading and all matched. Unless an item says
otherwise, no mathematical statement and no Lean declaration changed.

**Status (14 October 2026):** M1 to M6 are resolved. M7 onwards were found by the
Lean coverage work (`TODO_LEAN_COVERAGE.md`) and are open; they will be fixed with
the line-by-line reading of the proofs.

## Open (found by the Lean coverage, 14 October 2026)

Each item is a `DISCREPANCY` in `editorial/lean_coverage/register/` with a Lean
witness in `bfgs_lean_article/BfgsArticle/Coverage/Article/`. Independent review
confirmed each one.

- [ ] **M7: Abstract, centered theorem.** `paper/master.tex:42-44`: Theorem
  `art:centered` "applies in arbitrary dimension on compact initial sublevels"
  omits that the sublevel must lie in the region where the centered
  representation holds. With only a local representation this is false: the
  coercive cap of Corollary `art:failure_polyhedral` has a centered
  representation on a ball around its minimizer and compact sublevels, but its run
  fails (`Master.centered_representation_needs_containment`). The introduction
  and Table `art:positive-outcomes` state the containment correctly. Proposed:
  "…applies in arbitrary dimension on compact initial sublevels contained in the
  region of the centered representation." (`A/master/prose/003`)
- [ ] **M8: "Branches that lose second differentiability".** `paper/master.tex:52-54`,
  `paper/sections/verification.tex` (item `A/verification/prose/017`) and
  `paper/appendices/lower_curvature.tex:11-13` speak of the lower-curvature branches
  losing second differentiability; only three of the four do, as Theorem
  `art:local-failure-lower` says. The fourth is a quadratic
  (`Verification.lower_branch_second_differentiability`,
  `LowerCurvature.branch_second_differentiability`). Proposed: "…with
  $C^{1,1}$ branches, three of which lose second differentiability at the
  accumulation point", "Three of the four lower-curvature branches also lose
  second differentiability at zero." and "…the loss of second differentiability of
  three of the four branches at the accumulation point."
  (`A/master/prose/009`, `A/verification/prose/017`, `A/lower_curvature/prose/010`)
  Companion: `companion/chapters/13_L.tex:3`, "The local finite-branch functions
  have Lipschitz gradients but lose second differentiability at the accumulation
  point", says the same (`Ch13L.branch_regularity`; line 413 of that chapter has it
  right). It is the hand-written introduction `introductions['L']` in
  `editorial/generate_companion.py`. Proposed: "…have Lipschitz gradients; three of
  the four lose second differentiability at the accumulation point."
  (`C/13_L/prose/002`)
- [ ] **M9: Ray identity without its range (typo).** `paper/sections/verification.tex`
  (item `A/verification/prose/004`): "$G(t(-1,16))=-t$" holds only for $t\ge0$, as
  `failure.tex:200` says (`Verification.seed_ray`, counterexample
  `seed_ray_fails_at_minus_one`). Proposed: add "for $t\ge0$".
- [ ] **M10: "The next theorem" points to the wrong theorem.** `paper/sections/energy.tex:108-109`:
  "The next theorem proves that the full update requires faster growth" — the next
  theorem is `art:minor-hierarchy`, a one-step inequality; the faster growth is
  Theorem `art:reciprocal-growth`, which also needs bounded gradients, a hypothesis
  the paragraph does not state (the paragraph's contradiction relies on it too).
  With it the corrected claim holds (`Energy.reciprocal_sum_superlinear_of_minimizer`).
  Proposed: "Theorem~\ref{art:reciprocal-growth} proves that, along runs with
  bounded gradients, the full update requires faster growth." (`A/energy/prose/012`)
- [ ] **M11: Lemma `art:seed_cycle` and Table `art:trial_table` omit the range of
  $(c_1,c_2)$.** `paper/sections/failure.tex:107-108`: "the entire line-search query
  list is Table~\ref{art:trial_table}" fixes no constants; the range appears only
  after the table (lines 154–161), as a consequence of the margins. Armijo holds at
  the accepted trial of phase $j$ exactly when $c_1\le r_j$, with $r_0\approx0.76658$,
  $r_1\approx0.39319$, $r_2\approx0.37521$, so for $c_1=0.38$ the phase-2 trial $1/16$
  is rejected (`Failure.accepted_armijo_ratios`, `seed_cycle_range_counterexample`).
  Both theorems use $0<c_1\le1/3$, so no later result is affected. Proposed: "With
  $p_j=-M_jg_j$, for every $0<c_1\le1/3$ and $c_2>0$ the entire line-search query list
  is Table~\ref{art:trial_table}." and add to the table caption "The decisions are
  those of the specified search for every $0<c_1\le1/3$ and $c_2>0$."
  (`A/failure/lemma/art:seed_cycle`, `A/failure/table/art:trial_table`; corrected
  statements `Failure.seed_cycle`, `trial_table`). The closing sentence of the
  seed appendix, "these calculations complete the proof of
  Lemma~\ref{art:seed_cycle}" (`paper/appendices/seed_certificate.tex:199-200`,
  `A/seed_certificate/prose/012`), needs no separate change: it is correct once
  the lemma states the range. Flip that item to `PROOF` when fixing M11.

## Open: companion discrepancies (found by the Lean coverage, 14 October 2026)

Each item is a `DISCREPANCY` in `editorial/lean_coverage/register/C_*.json`; the
intended statement is proved in `bfgs_lean_article/BfgsArticle/Coverage/Companion/`,
and independent review confirmed each item. Recurrences of article items are listed
under those items (M8). The chapters are generated: fix them through
`editorial/generate_companion.py` (the seed appendix through
`editorial/prepare_shared_appendix.py`) and regenerate.

- [ ] **M12: Theorem `L:thm:local` denies a finite smooth-branch representation.**
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
- [ ] **M13: Chapter L says it uses a fixed line-search pair.** `13_L.tex:413`:
  "This chapter uses the fixed line-search pair displayed in this chapter; D's wider
  parameter family is not imported." is a remnant of the fixed-pair edition. Since
  the transformation of 13 October (`constant_range['L']` in
  `editorial/generate_companion.py`), the chapter fixes an arbitrary pair
  $0<c_1\le1/3$, $c_1<c_2<1$ and proves its theorems for every such pair
  (`Ch13L.global_failure`, `local_failure`), which is Chapter D's family
  (`12_D.tex:58-60`). No result is affected. Proposed: delete the sentence, or
  "Like Chapter~\ref{comp:D}, the chapter covers every pair $0<c_1\le1/3$,
  $c_1<c_2<1$." Fix: a new `constant_range['L']` entry. (`C/13_L/prose/082`)
- [ ] **M14: Chapter D denies analyticity of all four branches.**
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
- [ ] **M15: Companion appendix: the interval operations do not give the table's
  decimals.** `companion/appendices/seed_certificate.tex:190`: "The same interval
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
- [ ] **M16: Companion appendix: two references keep the article's structure
  (typo).** `prepare_shared_appendix.py` turns the article's subsections into
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
- [ ] **M17: Chapter H's references keep its source note's numbering (typo).**
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
- [ ] **M18: Chapter 11's references keep its source note's numbering (typo).**
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
- [ ] **M19: Chapter 11: a cubic bound printed without its range (typo).**
  `11_U.tex:389-391`: "$0\le r'(v)\le6v^2$, $0\le r(v)\le6v^3$ near zero" omits
  $v\ge0$. The spike $r$ of (11.18) vanishes for $v\le0$, so $r(v)=0>6v^3$ for every
  $v<0$ (`Ch11U.spike_cubic_bound_fails`). Both bounds hold for every $v\ge0$
  (`Ch11U.spike_small_bounds`), and the chapter uses only $v\ge0$. A parallel of M9.
  Proposed: "… for $v\ge0$." Fix: in the module-U transformation of M18,
  `\] near zero. However,` (U.tex:353, occurs once) → `\] for \(v\ge0\). However,`.
  (`C/11_U/disp/026`)

## Wording points in the companion (no discrepancy)

Found by the companion coverage and its reviews. Each statement is true as
intended, so its register item is not a `DISCREPANCY`, but a hypothesis is left
implicit, a symbol is undefined, a sentence is an editorial remnant or a printed
proof shows less than its statement (Lean proves the statement). Optional; decide
in the line-by-line reading. The chapters are generated: change them through
`editorial/generate_companion.py` (the seed appendix through
`editorial/prepare_shared_appendix.py`) and regenerate.

- [ ] **W1: Bounded gradients left implicit (Chapter M).**
  `companion/chapters/02_M.tex:194`: "$\sum_{k<N}R_k=o(\sum_{k<N}q_k^{-1})$ excludes
  a positive gap" needs $\sum_kq_k^{-1}\to\infty$, which Theorem `M:average`
  provides along runs with bounded gradients. No counterexample without that
  hypothesis is known; the same point as M10, to be applied with it. Proposed:
  "Thus, along runs with bounded gradients, …" (`C/02_M/prose/018`)
- [ ] **W2: Hypotheses of the contradiction at `02_M.tex:211`.** "Positivity gives
  $\sum_{J\le k<N}q_k^{-1}=O(N)$, contradicting Theorem~\ref{M:average}" is correct,
  but the contradiction needs the hypotheses of Theorem `M:average` (bounded
  gradients, $d_k\to0$): the moving-frame suppositions alone are satisfiable, by a
  one-dimensional run whose values tend to $-\infty$. Optional: "…contradicting
  Theorem~\ref{M:average} under its hypotheses." (`C/02_M/prose/023`)
- [ ] **W3: Undefined symbols in Theorem `M:superquadratic`.** `02_M.tex:144-155`
  uses $G$ and $V_\eta$ (which involves $K_0$); all three are defined only in the
  proof of Theorem `M:average`. The claim holds for every gradient bound $G$.
  Proposed: add "with $G$, $K_0$ and $V_\eta$ as in the proof of
  Theorem~\ref{M:average}". (`C/02_M/theorem/M:superquadratic`)
- [ ] **W4: Implicit hypotheses in Theorem `M:hierarchy`.** `02_M.tex:65-70` leaves
  $H\succ0$ and $\alpha>0$ implicit ($e_j$ is defined only for positive definite
  matrices, and $H_+\succ0$ exactly when $\alpha>0$). Optional: state both, as the
  article does. (`C/02_M/theorem/M:hierarchy`)
- [ ] **W5: Chapter M cites itself.** `02_M.tex:9`: "from
  sources~Chapters~\ref{comp:M}, \ref{comp:H}, …" lists Chapter M among its own
  sources, because the generator maps the frozen source's `\cite{SM,…}` to chapter
  labels. Cosmetic. (`C/02_M/prose/002`)
- [ ] **W6: The proof of Lemma `comp:root_certificate` does not give the thirty
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
- [ ] **W7: "The previous admissible-length counterexample" (Chapter D).**
  `12_D.tex:68`: "…resolves the implementation-selection issue left open by the
  previous admissible-length counterexample." Nothing in the companion is that
  counterexample (the phrase comes from the history of the source report).
  Optional: drop the clause or name the construction (frozen span `D.span.2`).
  (`C/12_D/prose/007`)
- [ ] **W8: "In this note".** `12_D.tex:105` (Lemma `D:root`: "All denominators in
  this note are nonzero there"), and the same remnant of the source reports at
  `04_R.tex:83`, `07_H.tex:23` ("This note continues the investigation…") and
  `09_C.tex:110`, and "earlier notes" at `11_U.tex:354`. Optional: "in this
  chapter". (`C/12_D/lemma/D:root`, `C/07_H/prose/002`, `C/11_U/prose/031`)
- [ ] **W9: "The third slope" (companion appendix).** `seed_certificate.tex:12`:
  "The two unknown coordinates of the third slope …": "slope" is the article's term;
  the companion calls the $g_i$ gradients (`12_D.tex:160`). Optional: "of the third
  gradient $g_2=(c,d)^T$", a companion-only replacement in
  `prepare_shared_appendix.py`. (`C/seed_certificate/prose/017`)
- [ ] **W10: "The later nonsplitting conclusion" (Chapter 11).** `11_U.tex:492`, in
  "Relation to earlier work": the conclusion comes earlier, in Section 11.7 (subsection
  "The objective need not split as a smooth function plus …", line 453); the word is
  a remnant of the source's order. Proposed: "The nonsplitting conclusion of
  Section 11.7". (`C/11_U/prose/079`)
- [ ] **W11: Unnamed references to results the companion states (Chapter 11).**
  `11_U.tex:111` "the affine-criticality program" (Chapter 8); 416 "the recorded
  equivalence between inward radial smoothness and RS" (Theorem `R:thm:equiv`); 422
  "the original arbitrary curved finite-$C^2$-max conjecture" (the conjecture of
  Chapter 8, `C/08_A/prose/042`, OPEN); 424 "the older finite-polyhedral-partition
  theorem" (Theorem `R:thm:plq`). Optional: cite them with `\ref`. (`C/11_U/prose/019`,
  `prose/044`, `prose/049`, `prose/050`)
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
  Cosmetic. Renumbering would change the numbers proposed in M17, M18 and the other
  reference fixes, so decide them together. (Notes on `C/11_U/prose/026`,
  `C/11_U/disp/009`.)

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
