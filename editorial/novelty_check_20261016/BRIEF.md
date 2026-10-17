# Novelty check of the BFGS nonsmooth article (16 October 2026): common brief

The author asked: "Please do a novelty check, make sure nothing related has been
published that renders this work stale". You are one of three literature agents
(A: forward citations, B: topic search, C: authors and cited preprints). Today is
16 October 2026; your training data stops earlier, so rely on the web tools
(`websearch`, `webfetch`, and HTTP APIs: arXiv `http://export.arxiv.org/api/query`,
OpenAlex `https://api.openalex.org`, Semantic Scholar
`https://api.semanticscholar.org/graph/v1`, Crossref `https://api.crossref.org`).

Repository (read only): `/Users/yxie/Projects/bfgs-nonsmooth`. The article is
`paper/` (`master.tex`, `sections/introduction.tex` positions the prior work,
`sections/verification.tex` lists open questions, `bibliography.tex`,
`preprint_references.tex`). The companion is `companion/`. A historical literature
review of 12 September 2026 is `editorial/LITERATURE_LEDGER.json` (keys `sources`,
`unselected_related_work_review`, `paper_literature_claims`): read it first so you
do not redo it, and look for what appeared or changed since.

## The article's claims (what could be made stale)

Setting: ordinary full BFGS (unmodified inverse update), arbitrary SPD H0, fixed
0<c1<c2<1, Armijo + weak Wolfe steps, differentiable accepted iterates
("admissible run"); convex nonsmooth objectives; theorems about every infinite
admissible run.

1. Counterexamples (Section 6, Appendices C, D): convex objectives on R^2, maxima of
   four convex C^{2,1} branches with bounded Hessians (and a second version with four
   uniformly strongly convex C^{1,1} branches), where a fixed unit-first
   Armijo-weak-Wolfe doubling/bisection line search makes full BFGS converge to a
   NONSTATIONARY point, with failing starts arbitrarily close to the unique
   minimizer, H0 = I, the same history for all 0<c1<=1/3, c1<c2<1; also global
   failure for a strongly convex max of a quadratic and linear pieces. Exact
   rational/interval certificates. These refute every-start local convergence
   guarantees for convex nonsmooth BFGS (not the almost-sure Lewis-Overton
   Challenge 7.1).
2. Positive theorems: (a) whole-sequence convergence for F(u,v)=u^2+|v| (left open by
   Guo-Lewis 2018, Cor. 4.4 and discussion; called unresolved in Gebken JOTA 2026);
   (b) centered smooth-plus-sublinear objectives, global value convergence and
   iterate convergence under a unique minimizer; (c) every coercive finite convex
   degree-one homogeneous function (every norm, gauges, coercive max-linear)
   -> every admissible run converges to 0; (d) local convergence for smooth convex
   plus polyhedral terms / finite polyhedral partitions with smooth extensions
   (Lasso-type); (e) planar smooth maxima under strict-contour and active-gradient
   nondegeneracy; an explicit three-quadratic example that fails the radial
   secant condition.
3. Technique: a principal-minor (adjacent-degree) hierarchy for the full BFGS update
   forcing the mean of 1/(g_k^T H_k g_k) to diverge, plus "comparison energy" /
   band-certificate (transported metric field) arguments; no bounded condition
   number or spectral limit assumed.
4. Companion extras: value convergence (to 0 or -inf) for all finite convex
   degree-one homogeneous functions; radial secant conditions; Lean 4 formalization
   of every claim (Lean coverage, axiom audit, kernel replay).

Cited prior work (do not report as new): Lewis-Overton 2013 (Math. Program.);
Guo-Lewis 2018 (SIOPT); Gebken JOTA 2026 (doi 10.1007/s10957-026-03008-z);
Xie-Waechter arXiv:1712.08571; Lewis-Zhang JOTA 2015; Asl-Overton IMA JNA 2021;
Mascarenhas 2004, 2007; Lewis-Overton 2008 exact-line-search manuscript;
Diao arXiv:2609.09686 (2026); Jin-Jiang-Mokhtari NeurIPS 2024; Powell 1976;
Byrd-Nocedal 1989; Nocedal 1992; Combettes-Vu 2013; Schoepfer 2016;
Lewis-Wylie arXiv:1907.11742.

## What to report

A work "renders the article stale" only if it proves (before or concurrently) one
of the claims above, or a strictly stronger statement. Classify each relevant hit:
- SUPERSEDES: proves a main claim (or stronger) in the same setting.
- OVERLAPS: proves part of a claim, or the same result under slightly different
  assumptions (e.g. another line search, limited memory, a modified BFGS).
- RELATED: should probably be cited or discussed (same question, different
  algorithm or setting; new evidence on the benchmark; new counterexamples in a
  different setting).
- IRRELEVANT: skip (do not list beyond a count).

For every hit rated SUPERSEDES, OVERLAPS or RELATED you must have fetched the
work itself (arXiv abstract page at least; for SUPERSEDES/OVERLAPS the PDF or HTML
full text, and quote the exact theorem statement with its number). Record: full
citation, first-appearance date (arXiv v1 date) and publication venue/date if any,
URL you fetched, the exact claim, and a precise comparison with the article's claim
(setting, algorithm, line search, assumptions, conclusion). Never invent or guess a
citation: if you cannot fetch it, say so. Note works published since 12 September
2026 especially.

## Rules

- Do not edit the repository; no git commands that change anything; no Lean, no
  lake. Scratch only in your own directory under
  `/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/novelty_20261016/`.
- Keep a `PROGRESS.md` there (search queries run, counts screened) so the work can
  be resumed.
- Write the full report to `<your dir>/REPORT.md`: method (queries/APIs, date
  ranges, counts screened), the classified hits, works you could not access, and
  your conclusion. Final answer: at most 15 lines (verdict, the SUPERSEDES/OVERLAPS
  hits if any, the most important RELATED ones, path of the report).
