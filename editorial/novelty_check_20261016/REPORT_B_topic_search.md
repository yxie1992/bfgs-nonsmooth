# Novelty check, agent B (topic / keyword search, 2020–2026) — REPORT

Date: 16 October 2026. Scratch dir: this directory. Repository read only (no git, no Lean).

## Verdict

**No work found that SUPERSEDES or OVERLAPS any claim of the article or the companion.**
No paper, preprint or repository located by the topic search proves (i) convergence of
every BFGS run on u²+|v| (or any superset: centered smooth-plus-sublinear, degree-one
homogeneous/norms/coercive max-linear, polyhedral/Lasso local, planar smooth maxima),
(ii) a convex nonsmooth counterexample in which full BFGS with an Armijo–weak-Wolfe search
converges to a nonstationary point, (iii) a principal-minor / adjacent-degree hierarchy for
the BFGS update, or (iv) a Lean formalization of such BFGS results. The newest works in the
area (Aug–Sep 2026) are on different questions (1-D rate conjecture, DFP, smooth BFGS) and
are listed below as RELATED; three of them (Chen 2026, Liu–Wang–Wen–Zhang–Yuan 2026,
Asl–Overton 2020/21) are plausible additional citations. Nothing relevant appeared on arXiv
in the nonsmooth-BFGS topic after 9 September 2026 (latest hits: arXiv:2609.09686 and
arXiv:2609.09872, both 9 Sep 2026); none after the 12 September literature review.

## Method

Read first: `editorial/LITERATURE_LEDGER.json` (sources, unselected_related_work_review),
`paper/sections/introduction.tex`, `paper/sections/verification.tex`,
`paper/bibliography.tex`, `paper/preprint_references.tex`. Everything already cited there
(the brief's list) is not re-reported.

| Source | Queries | Date range | Results screened |
|---|---|---|---|
| arXiv export API (`export.arxiv.org/api/query`, cats math.OC, cs.LG, math.NA, stat.ML, cs.NA) | 2 succeeded (BFGS∧nonsmooth: 22; BFGS∧"non-smooth": 6); then HTTP 429 on every request for >1 h, abandoned | all, screened ≥2020 | 28 |
| arXiv search HTML (`arxiv.org/search`, all fields, newest first, 200/page) — replacement for the API | 50 queries h01–h50 (list in `arxiv_html_search.py`) | all, screened ≥2020 | see "Counts" |
| OpenAlex relevance search | 38 queries o01–o38 (`openalex_search.py`), top 100 each | from 2020-01-01 | 2 419 unique works; titles screened (`oa_qn_titles.txt`: 267 qN-titled; `oa_other_titles.txt`: 405 nonsmooth/formal-titled) |
| OpenAlex boolean title+abstract filters (complete result sets) | (BFGS ∨ quasi-Newton ∨ variable metric) ∧ (nonsmooth ∨ non-smooth ∨ nondifferentiable ∨ piecewise linear ∨ polyhedral ∨ partly smooth): 173; (BFGS ∨ quasi-Newton ∨ DFP) ∧ (counterexample ∨ failure ∨ nonconvergence): 244; (Lean ∨ Coq ∨ Isabelle ∨ formalization) ∧ (line search ∨ gradient descent ∨ quasi-Newton ∨ BFGS ∨ convex optimization): 796 | from 2020-01-01 | 1 213, all titles screened (`openalex_filtered.json`) |
| Crossref bibliographic search | 12 queries c01–c12 (`crossref_search.py`) | from 2020-01-01 | 888 unique; 153 qN/formal-titled not already in OpenAlex set screened |
| Semantic Scholar Graph API | 28 queries prepared (`s2_search.py`) | 2020–2026 | **not usable**: HTTP 429 on every request (also the bulk endpoint) |
| Web search (websearch tool) | ≈25 queries: BFGS nonsmooth convex convergence 2026; "u^2+\|v\|"; weak Wolfe convex nonstationary counterexample; Lewis–Overton conjecture/Challenge 7.1; norm/max-type/piecewise-linear; l1/Lasso; BFGS stable manifold; Dai perfect example and later failures; whole-sequence/Guo–Lewis open question; principal minors / 1/(gᵀHg) / potential; local convergence of max of smooth functions; gauge/sublinear; Lean/Coq/Isabelle formalization of BFGS, of line search; DFP counterexample; Benqi Liu/Wen group; Curtis–Robinson book; Dai ICM overview; Smirnov 2026 | – | top ≈10 each |
| Direct fetches | arXiv abs/HTML pages of every RELATED hit; GitHub repos `canghaimeng/lewis-overton-bfgs-rate`, `imathwy/DFP_wolfe_local`, `imathwy` repository list; OpenAlex/Crossref records | – | – |

Query topics covered (brief's list): BFGS nonsmooth convex convergence; quasi-Newton
nonsmooth convergence proof; BFGS with Armijo / weak Wolfe nonsmooth; u²+|v|; norm /
polyhedral / max-affine / piecewise linear / partly smooth / Lasso / L1; convergence to a
nonstationary point / convex counterexample / failure with Wolfe search; Lewis–Overton
challenge and conjecture; stable-manifold counterexamples; variable metric bundle methods;
Dai's perfect example and later failure examples; principal-minor / potential / energy
arguments; formal verification (Lean/Coq/Isabelle) of optimization algorithms and
quasi-Newton convergence.

### Counts

- arXiv search HTML: 50 queries, 551 unique records, 411 submitted 2020 or later; every
  title screened, abstracts read for all optimization-related ones (`arxiv_html_results.json`).
  (Query h43 "BFGS Isabelle OR Coq" was parsed by arXiv as plain terms and returned noise.)
- arXiv API: 28 records (2 queries) before rate limiting.
- OpenAlex: 2 419 (relevance) + 1 213 (boolean filters) records; Crossref: 888.
- Total distinct records screened by title (with overlaps between sources): about 4 500;
  about 60 abstracts read; full text (arXiv HTML) read for R1, R2, R3, plus the two
  GitHub repositories of R1 and R2; abstract pages fetched for R4 and R5.
- Classified: SUPERSEDES 0, OVERLAPS 0, RELATED 8 (R1–R5), could not access 1 book
  chapter; everything else IRRELEVANT.

## Classified hits

### SUPERSEDES — none
### OVERLAPS — none

### RELATED (fetched; not in the article's bibliography)

**R1. Qiuyu Chen, "Initialization-dependent BFGS trial rates for tilted absolute values",
arXiv:2609.09872v1 [math.NA, math.OC], submitted 9 Sep 2026 (only version); no
publication found.** Fetched: https://arxiv.org/abs/2609.09872 and full HTML
https://arxiv.org/html/2609.09872v1; Lean repository
https://github.com/canghaimeng/lewis-overton-bfgs-rate (created 8 Sep 2026, pushed
12 Oct 2026; Lean/Mathlib v4.33.0).
- Exact claim, Theorem 3.1 (Two exact periodic families): "Let u∈ℐ and c₂∈(0,1). Starting
  from the states in (20), the Lewis–Overton line search generates two nonterminating
  executions with the following properties. […] Consequently their exact trial-normalized
  rates are ρ_A(u)=q_A(u)^{1/5}, ρ_B(u)=q_B(u)^{1/4}, and ρ_B(u)<ρ_A(u)." with
  ℐ=(9/5,13/6), q_A=3u/(4(u+1)²), q_B=u/(u+1)². Corollary 4.1: "For every u∈ℐ, there are
  two nonterminating initializations whose exact R-linear factors, measured by line-search
  trials, are the unequal values in (24)." The paper concludes that the
  initialization-independent rate assertion of Lewis–Overton's 2008 Conjecture 4.1
  (Optimization Online report "Nonsmooth optimization via BFGS") is false.
- Comparison: one-dimensional f_u(x)=max{x,−ux}; Lewis–Overton doubling–bisection line
  search with Armijo parameter c₁=0 (the paper's convention) and any c₂; both executions
  converge to the minimizer; the question is the rate. The article's claims concern R²/Rⁿ,
  convergence vs. nonstationary limits, 0<c₁<c₂<1. No overlap. Related because it is a
  concurrent exact (rational-certificate, Lean-formalized) analysis of unmodified BFGS on a
  nonsmooth convex function with the same family of line searches, and it disproves part
  of a Lewis–Overton conjecture. Worth a citation in the related-work paragraph (and in the
  companion's formal-verification discussion: it is another Lean-checked nonsmooth-BFGS
  result, though only 1-D). The article makes no "first formalization" claim (checked by
  grep of `paper/` and `companion/`), so nothing needs correcting.

**R2. Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, Ya-xiang Yuan, "A counterexample to
global convergence of classical DFP under the standard strong Wolfe conditions",
arXiv:2608.21708v1 [math.OC], submitted 22 Aug 2026 (only version).** Fetched:
https://arxiv.org/abs/2608.21708 and HTML https://arxiv.org/html/2608.21708v1; Lean
formalization https://github.com/imathwy/DFP_wolfe_local (Lean 4 v4.32.0; README reports
axiom audits with only propext/Classical.choice/Quot.sound and a `leanprover/comparator`
check).
- Exact claim, Theorem 1 (Main theorem), for 0<c₁<2/3≤c₂<1: "there exist f∈C²(R²),
  x₀∈R², H₀≻0, and positive step lengths α_k such that ½I⪯∇²f(x)⪯(3/2)I (x∈R²), all
  classical DFP iterates are well defined, every step satisfies (1) and (3) with these
  constants, but there is a constant G_∞>0 such that ‖∇f(x_k)‖→G_∞. The same conclusion
  holds in every dimension n≥2 by an orthogonal direct sum." Corollary 2 gives H₀=I with
  problem-dependent Hessian bounds.
- Comparison: different method (DFP, not BFGS), smooth uniformly convex objective, step
  lengths chosen to satisfy (strong) Wolfe (not produced by a fixed unit-first
  doubling/bisection procedure), one start. The article's counterexamples are for BFGS on
  nonsmooth convex maxima with a fixed search procedure and failing starts arbitrarily close
  to the minimizer. No overlap. Related as a concurrent convex quasi-Newton failure built
  near an invariant (center) manifold, with Lean verification — a natural citation next to
  Mascarenhas/Dai/Diao in "Deterministic limits".

**R3. Azam Asl, Michael L. Overton, "Behavior of Limited Memory BFGS when Applied to
Nonsmooth Functions and their Nesterov Smoothings", arXiv:2006.11336v1, 18 Jun 2020;
published in Numerical Analysis and Optimization (NAO-V), Springer Proceedings in
Mathematics & Statistics 354 (2021), doi 10.1007/978-3-030-72040-7_2.** Fetched:
https://arxiv.org/html/2006.11336v1 (statement verified in that text; the published
chapter was not fetched).
- Exact statement (Section 2, list of known full-BFGS results): "As far as we know, even
  the case f(x)=|x^(1)|+(x^(2))² remains open!"
- Comparison: this is exactly the article's benchmark F(u,v)=u²+|v| (coordinates swapped).
  The article currently documents the open status through Guo–Lewis 2018 and Gebken 2026;
  this is a third, independent statement of the open problem by Asl–Overton (2020/2021).
  Possibly missing citation (supports claim 2(a)); does not prove anything about it.
  (The article cites the different Asl–Overton IMA JNA 2021 paper.)

**R4. Lean formalizations of optimization theory (context for the companion's Lean claim;
none treats BFGS or nonsmooth quasi-Newton convergence):**
- Yiyang Zhang, Kenneth W. Shum, "Formalization of Line Search Methods by Lean",
  arXiv:2606.25412v1 [math.OC], 24 Jun 2026. Fetched abstract/HTML
  https://arxiv.org/abs/2606.25412: formalizes Armijo, Goldstein, Wolfe, nonmonotone
  conditions and the Zoutendijk theorem in Lean 4.
- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen, "Formalization of
  Complexity Analysis of the First-order Algorithms for Convex Optimization",
  arXiv:2403.11437 (v1 18 Mar 2024). Fetched https://arxiv.org/abs/2403.11437.
- Chenyi Li et al., "Formalization of algorithms for optimization with block structures",
  Science China Mathematics (online 14 Apr 2026), doi 10.1007/s11425-025-2516-2. Fetched
  publisher abstract (https://link.springer.com/article/10.1007/s11425-025-2516-2): Lean 4
  formalization of BCD and ADMM convergence, subdifferentials and the KL property.
- Plus R1 and R2 repositories above. Optional citations for the companion; no overlap.

**R5 (minor, smooth setting; no overlap).**
- Benqi Liu, Chenyi Li, Zaiwen Wen, "The Minimum Q-Order of BFGS with Exact Line Search Is
  One", arXiv:2609.00596v1, 1 Sep 2026 (fetched abstract https://arxiv.org/abs/2609.00596):
  smooth strongly convex counterexample about Q-order; exact line search.
- Lijun Ding, Jinwen Yang, Baoyu Zhou, "On the Complexity of BFGS Method for Smooth Convex
  Optimization", arXiv:2608.16009v1, 17 Aug 2026 (fetched abstract): O(k^{-1/2}) gradient
  and O(k^{-1}) value rates for Armijo–Wolfe BFGS on L-smooth convex functions without
  strong convexity, via the trace–log-det potential. Technique context only (the article's
  principal-minor hierarchy is different and its objectives are nonsmooth).

### Could not access
- Frank E. Curtis, Daniel P. Robinson, *Practical Nonconvex Nonsmooth Optimization*, SIAM
  2025, Chapter 14 "Variable-Metric Methods", pp. 377–402, doi
  10.1137/1.9781611978599.ch14 (Crossref metadata fetched; epubs.siam.org returned 403). A
  textbook; unlikely to contain new theorems of the article's type, but the author may
  wish to look at what it states about unmodified BFGS on nonsmooth functions.
- Semantic Scholar API (rate-limited throughout).

### Screened and judged IRRELEVANT (examples; not exhaustive)
Proximal / regularized / stochastic / multiobjective / Riemannian quasi-Newton methods for
composite problems (Orban et al., Kanzow et al., Wang–Fadili–Ochs, Song–Wang–Yuan, …);
variable-metric bundle and gradient-sampling frameworks (Curtis–Robinson–Zhou IMA JNA 2020,
Maleknia–Shamsi 2022, Tang–Xing–Huang COAP 2026, NonOpt 2026) — modified algorithms, no
overlapping claims; smooth BFGS rate papers (Jin–Mokhtari et al., Rodomanov 2024,
Krutikov 2023, Yu–Gao–Luo 2025); modified/cautious BFGS for nonconvex smooth problems;
Smirnov 2026 (Russian Technological Journal, purely experimental); engineering
applications of (L-)BFGS; Lean/Coq/Isabelle works outside optimization algorithms.

## Conclusion

The topic search (arXiv, OpenAlex, Crossref, web; 2020–16 Oct 2026) found nothing that
renders the article or the companion stale. No SUPERSEDES or OVERLAPS hits. Suggested
optional additions: cite Asl–Overton (2020/2021) as another source stating that u²+|v| was
open; cite Chen (arXiv:2609.09872, Lean-formalized 1-D BFGS rate counterexample to a
Lewis–Overton conjecture) and Liu–Wang–Wen–Zhang–Yuan (arXiv:2608.21708, Lean-formalized
convex DFP counterexample) as concurrent related work. Neither proves any of the article's
claims.
