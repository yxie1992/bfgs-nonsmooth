# Triage of the line-by-line reading (step 2), coordinator decisions

Reports: `READING_<X>.md` in this directory (text of commit `c8db802`, before the
corrections M7–M11; line numbers are those of that commit).
Decision codes: ACCEPT (apply in Unit B), AUTHOR (record for the author, no change),
DONE-ELSEWHERE, REJECT (with reason). Exact old/new strings: in the reports; verify
counts against the current files before applying.

## Reader A (master, introduction, statements, geometry, verification, bibliography)

- R-A-1 ACCEPT (M8 companion part goes to compFix): master.tex `differentiability at the
  accumulation point.` -> `differentiability at the minimizer.`; harmonize
  lower_curvature.tex:13 (optional; decide in context: Appendix D says x̄_ℓ -> 0 just
  before? if "the accumulation point" is unambiguous there, keep); failure.tex 465/506/513
  read correctly (keep).
- R-A-2 ACCEPT (another M7 location): geometry.tex Table 1 caption -> `compact sublevels
  and a centered representation on all of $\R^2$, so the first row gives global
  convergence.` Check the term "centered representation" matches Theorem art:centered's
  wording.
- R-A-3 ACCEPT: Table 1 row 3 `($\lambda>0$, unique minimizer)`.
- R-A-4 ACCEPT: verification.tex "whitening" x3 (use the appendix's notation for A).
- R-A-5 ACCEPT (a)+(b): verification.tex open question "outside the nondegenerate planar
  case of Corollary art:planar-max" (verify the corollary covers it: planar, uniformly
  strongly convex C^2 branches, affinely independent active gradients, positive weights)
  and "with $0<c_1\le1/3$". OPEN item A/verification/prose/025: keep OPEN, note.
- R-A-6 ACCEPT: introduction "The paragraph after that corollary explicitly leaves".
- R-A-7 ACCEPT (2): verification.tex `compiler and dependency audits,` -> `compiler, axiom
  and kernel-replay audits,` + companion current_verification.tex kernel-replay sentence
  (after compFix; numbers refreshed at the end of step 2). (1) release run planned.
  (3) AUTHOR: whether the article mentions the coverage registers.
- R-A-8 ACCEPT + AUTHOR flag: companion/master.tex AI disclosure add "and, from October
  2026, Anthropic Claude (in OpenCode)"; same in editorial/AI_AND_AUTHOR_ACTIONS.md.
  Verify dates (TODO_LEAN_REVIEW.md:3, HANDOFF.md:3).
- R-A-9 ACCEPT: Figure 1 marker radius 1pt + caption (zero above edge [g1,g0], distance
  1/sqrt(257); solid arrows gradients, dashed arrow descent direction). Render and look.
- R-A-10 ACCEPT: cite Figure 1 (twice) and Table 3 (failure.tex) in the text.
- R-A-11 ACCEPT: "at infinitely many shrinking scales"; "Along the perturbed orbit of
  Proposition~\ref{art:quadratic_failure}".
- R-A-12 ACCEPT: equation (1) conditions moved into the text. Render.
- R-A-13 ACCEPT: Table 1 raggedright columns, \addlinespace, "inside the region of the
  representation", "admissible runs". Check packages array/booktabs. Render.
- R-A-14 ACCEPT: minipage \setlength{\parindent}{15pt}. Render page of Theorem 11.
- R-A-15 ACCEPT (a) cite order, (b) stray \par, (c) Gebken date; AUTHOR: alphabetical
  sort of the reference list (optional).
- R-A-16 ACCEPT: Diao citation without repeated name (check the other two cases:
  Xie-Wächter, Lewis-Overton; same treatment if they read "X's ... (X, ...)");
  delete unused LL18, JM25v2 blocks in preprint_references.tex.
- R-A-17 ACCEPT pdfkeywords = printed \keywords; edition date at the release run
  (record in TODO for the release).
- R-A-18 ACCEPT (a)-(f) after checking (c) (families named must be exactly those of the
  global corollaries) and (e) (how the article refers to companion chapters elsewhere).

## Reader B (energy, matrix_algebra): all ACCEPT
- R-B-1 Gram notation defined; R-B-2 rank-one compression step (gap); R-B-3 `(r-z)\det A`
  (companion 02_M.tex:87, 91 -> batch 2); R-B-4 orthogonal-matrix wording; R-B-5 beta_k
  defined, "For $k\ge J$" (companion 02_M.tex:129 -> batch 2); R-B-6 M10 at energy.tex:8-9
  ("when the gradients are bounded"); R-B-7 = R-C-2; R-B-8 "of Appendix A"; R-B-9 eqref
  range (verify label order); R-B-10 cite separator; R-B-11 `m\overline P^{-1}`.

## Reader C (global): all ACCEPT
- R-C-1 Cor. radial-convergence proof uses Theorem radial-equivalence for the inward case
  (gap); R-C-2+R-C-3 "shown in the proof of Theorem art:certificate", drop the unused
  Lipschitz clause; R-C-4 three replacements (check grammar of the second with its display);
  R-C-5 theta=1/2 named (global.tex:160-161; local.tex:65-75 with rho of R-D-3(c));
  R-C-6 Lebesgue sentence; R-C-7 T = t of Section 3, radial numerator N (verify R_k=N^2/T);
  R-C-8 "Condition (..)" + Theorem 9 sentence; R-C-9 "Moreover"; R-C-10 x_*=0, U=R^n,
  "Alternatively"; R-C-11 \qed in all 28 proofs (check the companion copy of the seed
  appendix: \qed defined there? else strip in prepare_shared_appendix.py).

## Reader D (local, planar_geometry): ACCEPT
- R-D-1 d<=1 and d_k->0 (gap); R-D-2 "non-affine-critical", "that compact part of the
  level"; R-D-3 (a) exp form, (b) segment parameter remark, (c) B_rho, (d)(e) optional
  renames (only if letters free), (f) transport factor lambda; R-D-4 \mbox around "F:R^2->R"
  (local x2, global Theorem 5) and "phi'(0)=-d"; R-D-5 cells sentence; R-D-6 numerator of
  D'/D; R-D-7 "Theorem art:centered requires".

## Reader E (failure, seed_certificate): ACCEPT
- R-E-1 (with R-F-2) M11 at the induction (26), Corollary after it, failure.tex:495; define
  "admissible pair" in Appendix D line 14 (check Lean statements carry the range);
  R-E-2 (= R-A-1) "at the minimizer" (master, Table 3 header, failure 506, 513,
  lower_curvature 13); R-E-3 seed certificate projected/rank-one terms (shared appendix:
  rerun prepare_shared_appendix.py + companion resync); R-E-4 convexity via phi_b''>=0;
  R-E-5 notation of failure.tex:498-500 (verify a_l, x_l, C_* in Appendix D);
  R-E-6 Figure 2 caption ratios (verify in figures/cycle_trials.tex); R-E-7 classical
  Hessian sentence; R-E-8 (a) parindent, (b) Table 3 raggedright, (c) check p.31 underfull,
  (d) gathered (44), (46) if simple, (e) Figure 3 labels optional; R-E-9 (a)-(d), (f)
  optional; R-E-10 Wolfe test defined; R-E-11 three wording fixes.

## Reader F (lower_curvature): ACCEPT
- R-F-1 initial point in V (gap; 4 article replacements; companion 13_L.tex:237, 355, 363
  in compFix; Lean: Proposition statement gains x_0 in V, library LUniform.orbit_exists /
  source_spec); R-F-2 -> R-E-1; R-F-3 "at P_*"; R-F-4 z_m, tau_m; R-F-5 G defined in
  Section 6; R-F-6..R-F-13 with the report's strings.

## Grouping for TODO_MANUSCRIPT_REVIEW.md (section "Line-by-line reading of the article")
- M30 "the accumulation point" -> "the minimizer" (R-A-1, R-E-2; companion in compFix).
- M31 Table 1 hypotheses (R-A-2, R-A-3).
- M32 M10 and M11 at further places (R-B-6, R-E-1, R-F-2).
- M33 initial point of the seed orbit in V (R-F-1; companion in compFix).
- M34 proof steps left out (R-B-2, R-B-5, R-C-1, R-C-4, R-C-5, R-D-1, R-E-3, R-E-4, R-E-10).
- M35 references (R-A-6, R-B-7/R-C-2, R-B-8, R-B-9, R-D-7, R-F-5, R-A-10, R-C-8).
- M36 Section 7: scope of the open question, verification paragraph (R-A-5, R-A-7).
- M37 AI-use disclosure (R-A-8; AUTHOR to confirm).
- M38 notation (R-A-4, R-B-1, R-B-3, R-B-4, R-B-11, R-C-7, R-D-2, R-D-3, R-E-5, R-E-9,
  R-F-3, R-F-4, R-F-6).
- M39 typesetting, figures, tables (R-A-9, R-A-12, R-A-13, R-A-14, R-C-11, R-D-4, R-E-6,
  R-E-8, R-F-7, R-F-12, R-F-13).
- M40 bibliography, citations, metadata (R-A-15, R-A-16, R-A-17, R-B-10).
- M41 language (R-A-11, R-A-18, R-C-3, R-C-6, R-C-9, R-C-10, R-D-5, R-D-6, R-E-7, R-E-11,
  R-F-8..R-F-11).
