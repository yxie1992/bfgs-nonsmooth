# Novelty check, agent A: forward-citation sweep (16 October 2026)

## Verdict

**No work found that SUPERSEDES or OVERLAPS any claim of the article or the companion.**
Among the 2022–2026 works that cite the seed papers, none proves (or claims) any of:
convex nonstationary-limit counterexamples for full BFGS with Armijo–weak-Wolfe steps;
whole-sequence convergence on `u^2+|v|`; convergence for norms / coercive degree-one
homogeneous functions; local polyhedral or planar smooth-max convergence; or the
principal-minor / comparison-energy technique. Gebken's 2026 JOTA paper is the only
citing work that studies nonsmooth BFGS convergence theory, and it is already cited.

Three September 2026 preprints sit close to the topic. One is RELATED and probably worth
citing. Two are peripheral smooth-case works:

- **Q. Chen, arXiv:2609.09872 (9 Sep 2026): RELATED.** It cites LO13, GL18, Gebken,
  Asl–Overton and Lewis–Zhang. It refutes the initialization-independence part of
  Lewis–Overton's 2008 rate conjecture for the 1-D tilted absolute value. This is a
  rate question, not a question of convergence or stationarity. It uses c1 = 0, and
  every run it builds converges to the minimizer.
- L. Ding, J. Yang, B. Zhou, arXiv:2608.16009 (17 Aug 2026): peripheral. Rates for
  smooth convex functions without strong convexity.
- B. Liu, C. Li, Z. Wen, arXiv:2609.00596 (1 Sep 2026): peripheral. Exact-line-search
  Q-order for smooth strongly convex functions.

## Method

Seeds were resolved to IDs on 16 Oct 2026:

| Seed | DOI / arXiv | OpenAlex | Semantic Scholar paperId |
|---|---|---|---|
| Lewis–Overton 2013 (LO13) | 10.1007/s10107-012-0514-2 | W2151568819 | 8aedae3f… |
| Guo–Lewis SIOPT 2018 (GL18) | 10.1137/17M1121883 | W2801405307 | 3fcdb551… |
| Guo–Lewis arXiv 1703.06690 ("BFGS convergence to nonsmooth minimizers of convex functions") | 10.48550/arXiv.1703.06690 | W2601597851 | (merged in S2) |
| Gebken JOTA 2026 (= arXiv 2511.03296) | 10.1007/s10957-026-03008-z | W4416019633 | c88fd3bc… |
| Asl–Overton IMA JNA 2021 (= arXiv 1810.00292) | 10.1093/imanum/drz052 | W2894232939 | 364b872b… |
| Lewis–Zhang JOTA 2015 | 10.1007/s10957-014-0622-7 | W1998045815 | 2883ba69… |
| Jin–Jiang–Mokhtari NeurIPS 2024 (= arXiv 2404.16731) | 10.52202/079017-0536 | W4415798480 | 24de24cd… |
| Xie–Wächter arXiv:1712.08571 | 10.48550/arXiv.1712.08571 | W2781304003 | 79c6a6a4… |
| Diao arXiv:2609.09686 | 10.48550/arXiv.2609.09686 | W7212107007 | f3253fac… |
| Lewis–Overton 2008 exact-line-search manuscript | none | **not indexed** (title search) | S2 search rate-limited (HTTP 429) throughout; not checked |

APIs and counts (date range 2022-01-01 to 2026-10-16):

- **OpenAlex** `filter=cites:<id>,from_publication_date:2022-01-01`: LO13 103,
  GL18 3, GL17 1, Gebken 0, AO21 11, LZ15 0, JJM24 2, XW17 1, Diao 0, giving **119
  unique works**. The index includes items up to 14 Oct 2026, so its lag is small.
- **Semantic Scholar** `/paper/{id}/citations` (all years): LO13 411, GL18 14,
  Gebken 1, AO21 17, LZ15 16, JJM24 15, XW17 5, Diao 0, giving 445 unique works.
  Merged with OpenAlex by normalized title and filtered to year ≥ 2022 (4 undated S2
  items kept): **173 unique works**.
- **OpenCitations COCI v2** on the DOI seeds (LO13 285 in all years / 97 since 2022;
  GL18 10/4; AO21 14/12; LZ15 10/1; Gebken 0; JJM24 0) added 6 DOIs not in the
  merged set. 4 are new works, all irrelevant (materials science, evolutionary
  bilevel optimization, S-DIGing, phase field); 2 are title duplicates (a
  Cambridge-repository copy and an SSRN copy).
- **Crossref** (`is-referenced-by-count`: LO13 295, GL18 11, AO21 12, LZ15 10,
  Gebken 0, JJM24 2) was used to check counts and to get metadata and abstracts for
  hits (for example Smirnov 2026). Crossref has no public cited-by list.
- **Extended seeds** (Asl–Overton OMS 2020 W2768607332; Asl–Overton 2021 proceedings
  W3036238959; Guo–Lewis "Rescaling…" arXiv 1802.06453 W2787890441): 19 citing works
  since 2022, of which 13 are new. All are irrelevant: one is a J-symmetric
  quasi-Newton method for smooth minimax; the rest are applications.
- **arXiv API checks for index lag**: `abs:BFGS` submitted 2026-01-01 to 2026-10-16
  (95 titles), and `(nonsmooth OR non-smooth) AND (BFGS OR quasi-Newton OR "variable
  metric")` submitted 2025-01-01 to 2026-10-16 (31 titles). All titles were screened.
  They turned up no BFGS-theory preprint missing from the citation indexes, other
  than those already listed.
- **Web search** (Gebken citers, Guo–Lewis citers): added Gebken–Ulbrich
  arXiv:2603.23236 and arXiv:2603.23261 (bundle trust-region methods, superlinear
  convergence; they cite Lewis–Overton 2008 "Nonsmooth optimization via BFGS"):
  irrelevant to the claims. Google Scholar was not usable (blocked).

**Totals screened:**
- 192 unique forward-citing works from 2022–2026: 173 (OpenAlex + Semantic Scholar)
  + 13 (extended seeds) + 4 (OpenCitations) + 2 (web search). Every title was
  screened, and about 60 abstracts.
- 126 arXiv titles from the index-lag checks.
- Full text was read for 6 works: 2609.09872, 2610.19864, 2608.16009, 2609.00596
  (main theorem and related-work section), 2603.23236 and 2603.23261 (grep for
  BFGS-related content).

## Classified hits

### SUPERSEDES: none
### OVERLAPS: none

### RELATED

**R1. Qiuyu Chen, "Initialization-dependent BFGS trial rates for tilted absolute
values"**
- arXiv:2609.09872v1 [math.NA], submitted 9 Sep 2026 (no later versions, no journal
  reference).
- Fetched: https://arxiv.org/abs/2609.09872 and https://arxiv.org/html/2609.09872v1
  (full text).
- Lean formalization: https://github.com/canghaimeng/lewis-overton-bfgs-rate.
- Cites LO13, GL18, Gebken JOTA 2026, Asl–Overton 2021, Lewis–Zhang 2015, and
  Lewis–Overton 2008 "Nonsmooth optimization via BFGS" (Optimization Online).

Setting:
- Objective: `f_u(x)=max{x,-ux}` on R (one dimension).
- Line search: Lewis–Overton doubling–bisection (their Algorithm 2.6), started at
  unit step, with **c1 = 0** ("we set the Armijo parameter c1=0 and allow any weak
  Wolfe parameter c2∈(0,1)").

Main result, verbatim:
- Theorem 3.1 (Two exact periodic families): "Let u∈I and c2∈(0,1). Starting from
  the states in (20), the Lewis–Overton line search generates two nonterminating
  executions …" with five-trial and four-trial scale-free cycles. The full state is
  multiplied by q_A(u)=3u/(4(u+1)^2) or q_B(u)=u/(u+1)^2 per period. The rates are
  ρ_A=q_A^{1/5} and ρ_B=q_B^{1/4}, with ρ_B<ρ_A, for I=(9/5,13/6).
- Corollary 4.1: "For every u∈I, there are two nonterminating initializations whose
  exact R-linear factors, measured by line-search trials, are the unequal values in
  (24)." The paper concludes: "The initialization-independent rate assertion in Lewis
  and Overton's Conjecture 4.1 [4] is false."

Comparison with the article:
- The question is different: asymptotic **rates** in one dimension, not stationarity
  or convergence of every run.
- Both of its executions converge to the minimizer 0. This is consistent with the
  article's homogeneous theorem, since `f_u` is a coercive degree-one homogeneous
  convex function, although c1 = 0 lies outside the article's 0<c1 setting.
- It proves nothing about R^2 failures, `u^2+|v|`, norms, or polyhedral and
  smooth-max local theory.
- Why it is relevant:
  - same algorithm and same line search family;
  - exact rational certificates plus Lean formalization, like the article's
    counterexample methodology;
  - it bears on the open question the companion lists ("sharp rates or universal
    matrix asymptotics").
- Suggestion: cite it in the open-questions / related-work discussion as new
  evidence that nonsmooth BFGS rates depend on initialization even in one dimension.
- Appeared after the 12 Sep 2026 literature review? No, it was submitted 9 Sep 2026,
  but that review does not list it.

**R1′. Q. Chen, Q. Wang, L. Xu, X. Jin, B. Xie, W. Zeng, "Euler: Towards
Human-Centered Multi-Agent Mathematical Discovery"**
- arXiv:2610.19864v1 [cs.AI], 14 Oct 2026.
- Fetched: https://arxiv.org/abs/2610.19864 and https://arxiv.org/html/2610.19864v1
  (Section 7.2 read).
- It is a system paper. Its "Lewis–Overton" case study is exactly the result of R1
  (same q_A, q_B and interval). There is no further BFGS theorem.
- Peripheral; listed only because it cites LO13 and is very recent. No need to cite.

**R2 (peripheral). Lijun Ding, Jinwen Yang, Baoyu Zhou, "On the Complexity of BFGS
Method for Smooth Convex Optimization"**
- arXiv:2608.16009v1 [math.OC], 17 Aug 2026. Cites JJM24.
- Fetched: https://arxiv.org/html/2608.16009v1 (full text).
- Theorem 3.1: BFGS with Armijo–Wolfe on a **convex, L-smooth**, bounded-below
  function. It gives min_{i<k}‖g_i‖ = O(k^{-1/2}), and a value gap of O(1/k) under a
  bounded initial sublevel set (gap-to-gradient bound W_0).
- The tool is a trace–log-det potential inequality (Lemma 2.2), which needs
  ‖y‖²≤L yᵀs, that is smoothness.
- Their stated open question 1: under convexity, global L-smoothness and a nonempty
  solution set, must every full-BFGS Armijo–weak-Wolfe sequence satisfy
  f(x_k)→f*?
- Comparison: the setting is smooth only and the potential argument depends on the
  Lipschitz gradient. The article's principal-minor hierarchy is designed precisely
  for when the uniform secant bound fails. No overlap.
- Optional citation as recent matrix-potential work alongside JJM24.

**R3 (peripheral). Benqi Liu, Chenyi Li, Zaiwen Wen, "The Minimum Q-Order of BFGS
with Exact Line Search Is One"**
- arXiv:2609.00596v1 [math.OC], 1 Sep 2026. Cites Lewis–Zhang 2015.
- Fetched: https://arxiv.org/html/2609.00596v1 (Theorem 1.1 and §1.3).
- Theorem 1.1: for every n≥2, ε>0 and R>0 there is a C^∞ globally strongly convex F
  with ‖∇²F−I‖<ε, equal to the standard quadratic outside B(0,R). Exact-line-search
  BFGS from B0=I converges Q-superlinearly, but no Q-order >1 holds.
- It realizes prescribed BFGS orbits by convex functions, using Lewis–Zhang's convex
  converse criterion (Prop. 3.1).
- Comparison: smooth, exact search, a rate question; no overlap. At most a
  methodological parallel (orbit realization by convex objectives) to the article's
  counterexamples.

### Screened and judged IRRELEVANT (counts only)

The remaining ~185 works are application papers (robotics, PINNs, control,
statistics, physics) or works on other algorithms, all judged IRRELEVANT. The other
algorithms are:
- gradient sampling: Gebken 2210.04579, 2312.12032, 2410.01382; Boskos et al.
  2503.16638;
- bundle and bundle–trust-region methods: Gebken–Ulbrich 2603.23236 and 2603.23261;
  several Optimization Methods & Software, IMA JNA and SIOPT papers;
- the NonOpt software;
- proximal and regularized quasi-Newton methods: 2410.11676, 2506.00521,
  2507.18363, 2510.06615;
- smooth BFGS rate papers: 2507.00361, 2509.22508, 2508.19712, 2303.16188;
- a stochastic subgradient counterexample (Jiajin Li, 2610.11298, 8 Oct 2026: a
  nonminimizing attractor for the stochastic subgradient method on a semialgebraic
  function; different algorithm);
- the S. J. Wright survey 2510.15734 (smooth focus).

Of note: A. V. Smirnov, "Experimental investigation of convergence characteristics of
quasi-Newton algorithm on nonsmooth and nonconvex functions", Russian Technological
Journal 14(1) (2026) 103–112, doi 10.32362/2500-316x-2026-14-1-103-112 (Crossref
metadata and abstract fetched). It is numerical only, on nonconvex test functions;
judged IRRELEVANT.

## Works not accessed / limitations

- Lewis–Overton 2008 exact-line-search manuscript: no index record in OpenAlex.
  Semantic Scholar search stayed rate-limited (HTTP 429) during the session, so I
  could not list its citers. Lewis–Overton's 2008 inexact-line-search report
  "Nonsmooth optimization via BFGS" is also not indexed. Its known citers here (Chen
  2609.09872, Gebken–Ulbrich 2603.23236) were found through other routes.
- Coverage of LO13 citers is incomplete: Semantic Scholar has 411 citers in all
  years and OpenAlex 352, while a web-search snippet for the Springer page shows
  "Cited by 673" (Google). Google Scholar itself could not be queried. The missing
  LO13 citers are probably mostly application papers. The citers of GL18, Gebken,
  Xie–Wächter, Asl–Overton and Lewis–Zhang are few, and the sources agree on them.
- Very recent preprints (October 2026) may not be indexed yet. The arXiv keyword
  checks above found none beyond those listed.

Scratch files: `openalex_citing.json`, `s2_citing.json`, `merged.json` (all 173 with
abstracts), `oc_*.json`, `arxiv_*.xml`, `fetched/` (HTML and text of the papers read).
