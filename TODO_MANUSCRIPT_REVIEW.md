# TODO: Manuscript review

Review date: 13 October 2026. Reviewer: AI assistant (Claude), at the author's request.

Scope: notation, typesetting and claim wording in the article (`paper/`). The seed
numerics were re-checked in the first reading and all matched. Unless an item says
otherwise, no mathematical statement and no Lean declaration changed.

**Status (13 October 2026):** M1 to M6 are resolved. M7 onwards were found by the
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

## Wording points in the companion (no discrepancy)

Found by the companion coverage and its reviews. Each statement is true as
intended, so its register item is not a `DISCREPANCY`, but a hypothesis is left
implicit, a symbol is undefined or a sentence is an editorial remnant. Optional;
decide in the line-by-line reading. The chapters are generated: change them
through `editorial/generate_companion.py` and regenerate.

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
