# Novelty check (16 October 2026)

The author asked: "Please do a novelty check, make sure nothing related has been
published that renders this work stale".

Three agents (Claude in OpenCode) searched the literature independently, from the
common brief `BRIEF.md`; the coordinating agent checked their key findings against
the sources and wrote this summary. Paths of the form `$S/…` or `…/novelty_20261016/…`
in the reports are scratch directories that were not kept.

| Report | Search |
|---|---|
| `REPORT_A_forward_citations.md` | works of 2022–2026 citing the article's main references (Lewis–Overton 2013, Guo–Lewis 2018, Gebken 2026, Xie–Wächter, Asl–Overton 2021, Lewis–Zhang 2015, Diao 2026, Jin–Jiang–Mokhtari 2024): 192 citing works screened, 6 read in full |
| `REPORT_B_topic_search.md` | topic and keyword searches, 2020 to 16 October 2026 (arXiv, OpenAlex, Crossref, the web): about 4,500 titles, 60 abstracts, 8 papers read in detail |
| `REPORT_C_authors_preprints.md` | recent work of the 14 authors closest to the topic, and newer or published versions of every preprint the article cites |

## Verdict

Nothing found renders the work stale. No paper or preprint up to 16 October 2026
proves or disproves any of the article's results:

- whole-sequence convergence of full BFGS with an Armijo–weak-Wolfe search on
  $u^2+|v|$ (the centered smooth–sublinear theorem);
- global convergence on coercive degree-one homogeneous functions (norms, gauges,
  max-linear functions);
- the local theorems for finite polyhedral partitions and planar finite maxima;
- the convex counterexamples in which full BFGS with the specified search converges
  to a nonstationary point (four convex $C^{2,1}$ branches; four uniformly strongly
  convex $C^{1,1}$ branches);
- the principal-minor and comparison-energy technique.

The latest published statement on the benchmark still calls it open: Gebken's
JOTA paper (2026, the article's `BG`) says that for $x_1^2+|x_2|$ "the convergence
of the BFGS method is not yet understood", and its Theorem 3.1 assumes that the
iterates converge. Asl and Overton (arXiv:2006.11336, proceedings 2021) also call
the case $|x_1|+x_2^2$ open. Every preprint the article cites is unchanged or was
published without new results on these questions (report C).

## Related work not cited (none overlaps; optional additions)

1. Q. Chen, "Initialization-dependent BFGS trial rates for tilted absolute
   values", arXiv:2609.09872 (9 September 2026). For one-dimensional BFGS with the
   Lewis–Overton line search on $\max\{x,-ux\}$, two nonterminating runs with
   different sharp trial-normalized rates exist for every tilt in an open interval,
   which refutes the "independent of the initial data" part of the Lewis–Overton
   2008 conjecture (the article's `NEG_LO08`). Both runs converge to the minimizer;
   the result concerns rates in one dimension. Rational certificates and a Lean
   formalization. A natural citation where the article mentions sharp rates or the
   Lewis–Overton manuscript.
2. A. Asl and M. L. Overton, "Behavior of limited memory BFGS when applied to
   nonsmooth functions and their Nesterov smoothings", arXiv:2006.11336, in a
   Springer proceedings volume (2021, doi 10.1007/978-3-030-72040-7_2). Not the
   Asl–Overton paper the article cites (IMA J. Numer. Anal. 2021). A third source,
   with Guo–Lewis and Gebken, for the open status of the benchmark.
3. Liu, Wang, Wen, Zhang and Yuan, "A counterexample to global convergence of
   classical DFP under the standard strong Wolfe conditions", arXiv:2608.21708
   (22 August 2026): DFP, not BFGS, on a smooth uniformly convex function in the
   plane, with chosen step lengths; Lean formalization. Related only as another
   formally verified quasi-Newton counterexample.
4. Peripheral: Lean formalizations of other optimization algorithms (for example
   arXiv:2606.25412, line search and Zoutendijk's theorem); smooth BFGS papers
   (arXiv:2609.00596, arXiv:2608.16009); a paper on a multi-agent mathematical
   discovery system whose BFGS case study is Chen's result (arXiv:2610.19864).

The article and the companion claim no first formalization, so these need no
correction; whether to cite them is a question for the author
(`TODO_MANUSCRIPT_REVIEW.md`, Q8).

## Bookkeeping

- Gebken's paper appeared in JOTA 209, issue 2, article 57; the bibliography could
  add the issue number.
- `editorial/LITERATURE_LEDGER.json` (historical) and the hash-pinned
  `bfgs_lean_stage1/literature_audit` name Lewis–Zhang's coauthor "Shubao Zhang";
  the coauthor is Shanshan Zhang (zbMATH, MaRDI, the Cornell thesis). The article
  prints "S. Zhang", which is right. Both files are frozen, so this is recorded
  only.

## Limits

- Semantic Scholar refused requests (rate limit) and Google Scholar was blocked, so
  the citing works of the Lewis–Overton 2008 manuscript, which OpenAlex does not
  index, were not listed; Google Scholar's count of works citing Lewis–Overton 2013
  (about 670) exceeds what the open indexes list (350–410). The missing ones are
  probably applications.
- The arXiv export API was rate-limited; the arXiv search pages were used instead.
- Curtis and Robinson's 2025 SIAM book (chapter "Variable-Metric Methods") could not
  be opened.
- Work under review that is not public cannot be found by any search.

## Checked by the coordinator

The arXiv records of 2609.09872, 2006.11336 and 2608.21708 (titles, authors,
dates, abstracts) match the reports. The open-status sentences of Gebken and of
Asl–Overton are quoted by the agents from the full texts.
