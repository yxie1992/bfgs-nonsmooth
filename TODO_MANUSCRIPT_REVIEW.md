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
- [ ] **M20: Chapter 9 refers to a result by its source note's letter (typo).**
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
- [ ] **M21: Chapter 5 cites "the preceding theorem" for Chapter 3's theorem (typo).**
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
- [ ] **M22: Chapter 5: no certificate "on a sublevel containing zero" (imprecision).**
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
- [ ] **M23: Chapter 5: no certificate "on a positive band containing this knot"
  (imprecision).** `05_G.tex:321` (Section 5.7): "No certificate exists on a positive
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
- [ ] **M24: Chapter 3 says that (S) "is exactly" (RS) (imprecision).**
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
- [ ] **M25: Chapter 3's proof cites (3.3)–(3.6) as (3)–(6) (typo).** `03_T.tex:148`
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
- [ ] **M26: "The preceding moving-frame theorem" (Chapter 3, typo).**
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
- [ ] **M27: Chapter 6 names its source working reports by bare letters (typo).**
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
- [ ] **M28: Chapter 10's references keep its source note's numbering (typo).**
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
- [ ] **W5: Chapters cite themselves (M, A).** `02_M.tex:9`: "from
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
  `09_C.tex:110` ("the subject of this note"); also "the previous note
  Chapter~8" at `09_C.tex:93` and "earlier notes" at `11_U.tex:354`. Optional: "in
  this chapter", "Chapter~8". (`C/12_D/lemma/D:root`, `C/04_R/prose/010`,
  `C/07_H/prose/002`, `C/09_C/prose/016`, `C/09_C/prose/020`, `C/11_U/prose/031`)
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
- [ ] **W11: Unnamed references to results the companion states (Chapters 5 and 11).**
  `11_U.tex:111` "the affine-criticality program" (Chapter 8); 416 "the recorded
  equivalence between inward radial smoothness and RS" (Theorem `R:thm:equiv`); 422
  "the original arbitrary curved finite-$C^2$-max conjecture" (the conjecture of
  Chapter 8, `C/08_A/prose/042`, OPEN); 424 "the older finite-polyhedral-partition
  theorem" (Theorem `R:thm:plq`); `05_G.tex:89` "The accumulated-expansion budget was
  useful in the proof" (the proof of Chapter 3's theorem; source G.tex:79). Optional:
  cite them with `\ref`. (`C/11_U/prose/019`, `prose/044`, `prose/049`, `prose/050`,
  `C/05_G/prose/012`)
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
- [ ] **W14: "We will argue by contradiction that Γ contains no affine-critical
  point" (Chapter 9).** `09_C.tex:151` announces the conclusion as the thing argued
  by contradiction, while the paragraph goes on with its negation as the standing
  supposition ("Then $\ell>F_*$, every point of $\Gamma$ satisfies the
  regular-switching hypothesis, …"). Proposed: "We suppose, for a contradiction,
  that the compact cluster set $\Gamma$ contains no affine-critical point."
  (`C/09_C/prose/027`)
- [ ] **W15: Range of the angular cutoffs (Chapter 9).** `09_C.tex:191` chooses
  smooth angular cutoffs $\chi_j$ "with disjoint supports, equal to one on
  neighborhoods of the entire moving normal arcs"; the later estimates (line 202
  and the display at lines 218–220) also need $0\le\chi_j\le1$. Standard cutoffs
  have it; optional: say so. (`C/09_C/prose/041`; used by `prose/042`, `disp/020`)
- [ ] **W16: Sign of $\epsilon$ left to the context (Chapter 5).** `05_G.tex:269-278`:
  "For $x=\epsilon$, $z=-\epsilon/2$," and the formulas that follow need $\epsilon>0$
  (for $\epsilon<0$, $g_x=1+\epsilon$); only line 278's "strictly eligible" and line
  307's $\epsilon\downarrow0$ fix the sign. Proposed: "For $x=\epsilon$,
  $z=-\epsilon/2$ with $\epsilon>0$," (source `For $x=\epsilon$, $z=-\epsilon/2$,`,
  G.tex:251, occurs once). Lean: `Ch05G.shifted_crossing_gradients`,
  `shifted_crossing_quantities`, `shifted_crossing_eligible_divergent` (all with
  $\epsilon>0$). (`C/05_G/disp/025`, `disp/026`, `prose/054`)
- [ ] **W17: "Conditions (V)--(S)" (Chapter 3).** `03_T.tex:192`: "Conditions
  (V)--(S) become" means "(V) and (S)" (tags (3.V), (3.S)): a range of condition
  names, not a wrong number. Optional: "Conditions (V) and (S) become" (T.tex:170,
  occurs once). (`C/03_T/disp/024`)
- [ ] **W18: (RS) used before Chapter 4 defines it (Chapter 3).** The section title
  at `03_T.tex:216`, "Given (RS), take" (line 217) and lines 225, 229 use "(RS)",
  which Chapter 4 defines ((4.RS), `04_R.tex:53-59`, label `R:eq:RS`), with no
  pointer. Optional: "Given the radial secant condition (RS) of
  Chapter~\ref{comp:R}, take" (T.tex:191, occurs once). (`C/03_T/disp/026`,
  `prose/029`)
- [ ] **W19: Nonnegative constants in (RS) and (IR) (Chapter 4, proof gap).**
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
- [ ] **W20: "For differentiable $x,z$" without "$\in K$" (Chapter 4).**
  `04_R.tex:40`: "For differentiable $x,z$, put" introduces $T$ and the bound "$0\le
  T\le T_{\max}:=4GR$" (line 51), which holds only for $x,z\in K$ ($R$ and $G$ are
  bounds on $K$): for $F(x)=|x|$, $b=1$, $R=G=1$, the points $x=-10$, $z=10$ give
  $T=40>4GR$. The article has "$x,z\in K$" (`paper/sections/global.tex:20`); the
  all-of-$\mathbb R^n$ reading is not a reasonable one, so no discrepancy. Proposed:
  "For differentiable $x,z\in K$, put" (source R.tex:34). Lean:
  `Ch04R.curvature_split`, `secant_notation`. (`C/04_R/disp/003`, `disp/005`)
- [ ] **W21: References to unnamed, later or absent material (Chapter 4).** Each
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
- [ ] **W22: The letter "D" for Chapter 12's objects (Chapter 4).** `04_R.tex:255`:
  "the certified D parameters" and "The unique D optimizer $(-1,16)$"; line 265:
  "the verified D run"; line 276: "$a$ times those of D". "D" is the source letter of
  Chapter 12, which the chapter cites correctly as Chapter~\ref{comp:D} at lines 233
  and 253; in print the letter names nothing, but no wrong number is printed and the
  claims are true. Optional: "Chapter 12's certified parameters", "Chapter 12's
  unique optimizer", "the verified run of Chapter 12", "those of the run of
  Chapter 12" (source R.tex:229 (twice), 239, 250). Lean:
  `Ch04R.fourPiece_constants`, `fourPiece_optimizer`, `fourPiece_transformed_data`,
  `fourPiece_curvatures`. (`C/04_R/prose/043`, `prose/045`, `disp/037`, `prose/054`)
- [ ] **W23: The reason given for "broader" (Chapter 4).** `04_R.tex:309`: "This is
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
- [ ] **W24: Bounded gradients left implicit (Chapter 6).** `06_F.tex:122-125`: "If
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
- [ ] **W25: References to source material absent from the companion (Chapter 6).**
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
- [ ] **W26: Chapter 3's theorem and conditions named only by description
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
