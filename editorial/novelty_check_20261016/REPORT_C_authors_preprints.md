# Novelty check, agent C (authors and cited preprints): report

Date of the searches: 16 October 2026. Scope (from the brief): (1) 2022–2026 output of the named
authors, screened for BFGS or quasi-Newton methods on nonsmooth (convex) functions; (2) current status
and newer versions of the preprints the article and companion cite; (3) whether Gebken 2026 or any later
work settles whole-sequence convergence on u^2+|v|, proves BFGS convergence on norms, max-linear or
polyhedral convex functions, or builds convex counterexamples with Wolfe line searches.

## Verdict

**No SUPERSEDES and no OVERLAPS hits.** None of the named authors has published or posted anything
between 2022 and 16 October 2026 that proves any of the article's claims, or part of one. None of the
cited preprints has a newer version, and the ones still unpublished stay unpublished. Gebken's published
JOTA 2026 article still calls the convergence of BFGS on x1^2+|x2| "not yet understood". It does not
cover the l1 norm. I found no work, by these authors or in the targeted topic searches, that:

- proves whole-sequence convergence on u^2+|v|;
- proves convergence of full BFGS on norms, max-linear or polyhedral convex functions;
- or builds a convex counterexample under a Wolfe line search.

There is one new RELATED item that nobody in the repository has noticed: Chen, arXiv:2609.09872 (9 Sep
2026, before the 12 Sep ledger review). It concerns the 1-D tilted absolute value, with c1 = 0, and is
about rates. It is not an overlap.

One metadata error turned up. In the ledger, Lewis–Zhang's coauthor is listed as "Shubao Zhang"; the
correct name is Shanshan Zhang. The printed article says "S. Zhang", so it is not affected.

## Method

APIs and sources used:

- **arXiv export API:** `id_list` check of all cited preprints. After that, the API returned HTTP 429
  (rate limit, probably shared with agents A and B), so I used the arxiv.org/search HTML and the
  abstract pages instead.
- **OpenAlex API:**
  - author IDs: Overton A5069099932, Lewis A5081400874, Gebken A5035920167, Wächter A5112274231 and
    A5067291755, Jin A5049692758, Jiang A5085106727 and A5020301131, Mokhtari A5008417632,
    Mascarenhas A5064718420, Dai A5109187979, A5110798385 and A5087410694;
  - works from 2022-01-01 onwards;
  - a name-plus-keyword filter (BFGS, quasi-Newton, variable metric, nonsmooth) for 17 name variants.
- **Crossref** for titles and DOIs, **Semantic Scholar** for the Gebken record and its citations, and
  the **MaRDI/zbMATH** portal.
- **Web search:** 7 queries.
- **Personal pages:** Overton (papers.html, nonsmoothalg.html, thiscentury.html), Lewis (home page and
  publications page, both stale since 2019; CV dated July 2019), Wächter (page no longer maintained;
  he moved to Gurobi), Dyatlov (home page).
- **Springer:** the published JOTA HTML for Gebken, through rd.springer.com, because link.springer.com
  serves a JavaScript challenge.
- **DBLP:** returned HTTP 429 and a bot challenge, so I could not use it.

Counts screened (titles; abstracts for anything plausibly relevant):

| Author | arXiv results (all years / 2022+) | Relevant 2022+ |
|---|---|---|
| Overton, M. L. | 20 / 5 | none (gradient sampling for control, numerical radius, Householder, max functions) |
| Lewis, A. S. | 43 / 11 | none on BFGS; Lewis–Pirani 2608.20642 (Goldstein subgradients) screened in full text: no BFGS |
| Gebken, B. | 16 / 8 | 2511.03296 = the cited JOTA paper; Gebken–Ulbrich 2603.23236 and 2603.23261 (bundle and cutting-plane methods): irrelevant |
| Guo, Jiayi | about 45 / about 40 | all namesakes; the Cornell Jiayi Guo (now SUFE) has no BFGS work after his 2018 thesis |
| Diao, Rui | 3 / 1 | only 2609.09686 v1 |
| Asl, Azam | 4 / 1 | 2202.02279 (J-symmetric quasi-Newton for minimax, Math. Program. 2024): irrelevant |
| Xie, Yuchen | about 70 / about 65 | namesakes; the author's own 2022+ items (2305.09978, noisy-optimization papers) are irrelevant; no nonsmooth-BFGS preprint after 1712.08571 |
| Wächter, A. | 22 / 9 | none |
| Jin, Qiujiang | 9 / 6 | all smooth (cited NeurIPS 2024, Math. Program. 2026, NeurIPS 2025, and earlier) |
| Jiang, Ruichen | 24 / 21 | smooth quasi-Newton; 2602.08232 (Shampoo-type matrix online learning): irrelevant |
| Mokhtari, A. | 107 / 47 | same smooth quasi-Newton papers |
| Zhang, Shanshan | 54 / 33 | all namesakes; Lewis's coauthor (Cornell thesis 2013) has no 2022+ work |
| Mascarenhas, W. F. | 19 / 0 | none (OpenAlex: 0 works in 2022+) |
| Dai, Yu-Hong | 82 / 42 | none on nonsmooth BFGS; ICM 2022 overview (doi 10.4171/icm2022/72) read: it discusses only smooth DFP/BFGS questions |

Totals: about 289 arXiv entries from 2022 onwards and about 232 OpenAlex works from 2022 onwards (these
overlap), plus 49 keyword-filtered OpenAlex hits.

Topic searches for part (3), on the arXiv abstract field:

- "BFGS nonsmooth" (21), "BFGS non-smooth" (25), "quasi-Newton nonsmooth convergence" (40)
- "BFGS counterexample" (3), "BFGS Wolfe convex nonsmooth" (1), "BFGS piecewise linear" (2)
- "BFGS polyhedral" (1), "BFGS max-type" (0), "variable metric nonsmooth convergence" (26)
- "BFGS norm convergence nonsmooth" (1), "Lewis Overton challenge BFGS" (0)

I also screened the 200 newest results of an all-fields arXiv search for "BFGS", back to January 2025.

## Part 2: status of the cited preprints

Each row was checked against the arXiv abstract page (submission history), OpenAlex and Crossref.

| Cited as | Latest version (UTC) | Publication status | New results? | Action |
|---|---|---|---|---|
| Xie–Wächter arXiv:1712.08571**v1** | v1, 22 Dec 2017 (still the only version) | none found (Crossref: none; OpenAlex: arXiv only; Wächter's page unmaintained) | none | none |
| Dyatlov arXiv:1805.11660**v1** | v1, 29 May 2018 (only version); also on his home page as stunnote.pdf | expository notes, unpublished | not applicable | none |
| Lewis–Wylie arXiv:1907.11742**v1** | v1, 26 Jul 2019 (only version) | none (Crossref: none; Gebken–Ulbrich, Mar 2026, still cite it as arXiv) | none | none |
| Diao arXiv:2609.09686**v1** | v1, 9 Sep 2026 04:02:59 (only version) | none | none | none |
| Gebken, JOTA 209, article 57 (2026); arXiv:2511.03296 | arXiv v1 only (5 Nov 2025; DOI link added); published online 8 May 2026 | JOTA **209(2)**, article 57, open access CC BY | none: no erratum, no follow-up preprint (arXiv, Google Scholar, MaRDI) | optional: add issue "(2)" |
| Lewis–Overton 2008 exact-line-search manuscript | PDF unchanged (Last-Modified 15 Dec 2008); still listed without a venue on Overton's "Nonsmooth Algorithms" page; Optimization Online 2008/12/2173 | unpublished | none | none |
| Jin–Mokhtari arXiv:2507.00361 (v2) | v2, 25 Oct 2025 01:22:57 (v1 1 Jul 2025); no v3 | NeurIPS 2025 (doi 10.52202/085713-2938), as the companion already says | smooth, self-concordant; no overlap | none |
| Lewis–Liang arXiv:1807.03134**v1** | v1, 9 Jul 2018 (only version) | SIAM J. Optim. 32(1) (2022), with Tian, as the companion already says | none | none |

The arXiv dates in the companion and the ledger match the UTC submission histories. The arXiv search
page shows the Eastern-time dates, 30 June and 24 October 2025, for 2507.00361, which is consistent.

## Part 3: Gebken 2026 and later work

Source: the published JOTA HTML at https://rd.springer.com/article/10.1007/s10957-026-03008-z (open
access, "Published: 08 May 2026, Volume 209, article number 57"). Quotes:

- **Introduction:** "However, even for simple nonsmooth functions like f: R^2 → R, x ↦ x_1^2 + |x_2|
  from [15], the convergence of the BFGS method is not yet understood." ([15] is Guo–Lewis.) The article's
  sentence "Gebken's published 2026 introduction still identifies u^2+|v| as unresolved" is accurate.
- **Theorem 3.1:** "Assume that f satisfies (A2). There is an open neighborhood U ⊆ R^n of x* such that
  if (B1) holds for the sequence generated by Alg. 1 starting at x^0 ∈ U, then the limit x̄ of (x^k)_k is
  a critical point of f."
  - (B1.2) assumes the iterates have a limit.
  - (B1.3) assumes each selection is active infinitely often.
  - (B1.4) assumes the eigenvalues λ_j^k for j > dim N(x̄) lie in [σ_ℓ, σ_u].
  - (B1.5) assumes H_k(∇f_i(x̄) − ∇f_1(x̄)) → 0.

  This matches the article's description (Theorem 3.1 and (B1)).
- **Theorem 4.1:** a piece-visiting result under (A2) and (B2): the first m iterates visit all m
  selections. It is not a convergence theorem.
- **Section 5:** "The obvious question is whether it is possible to prove that for the BFGS method, the
  assumption (B1), specifically (B1.4) and (B1.5), actually holds in some general setting. The way it is
  stated in this article, we believe that this is not possible". Also: "even for functions as simple as
  the l1-norm on R^2, this assumption [affine independence (A2.1)] is violated."

Gebken therefore proves no unconditional convergence, says nothing about norms or max-linear functions
beyond what is quoted above, and gives no counterexample. Semantic Scholar lists one citing work, Chen
2609.09872 (below). MaRDI's citing list for Lewis–Zhang adds nothing beyond Gebken and Chen.

Later work on the same questions:

- **u^2+|v|:** no work found after Guo–Lewis 2018 that claims whole-sequence convergence. The Guo–Lewis
  manuscript ends: "That conjecture remains open." Gebken 2026 repeats that it is open.
- **Norms, max-linear, polyhedral:** nothing new. The only norm result remains Guo–Lewis Corollary 4.2
  (the Euclidean norm), which the article already cites.
- **Convex counterexamples with Wolfe searches:** none found.
  - Diao 2609.09686 is smooth and nonconvex, with a first-local-minimizer search; it is already cited.
  - Chen 2609.09872 has convergent runs only.
  - Liu–Li–Wen 2609.00596 is smooth and strongly convex, with an exact line search, and concerns
    Q-order only.

## Classified hits

### SUPERSEDES

None.

### OVERLAPS

None.

### RELATED

**R1. Q. Chen, "Initialization-dependent BFGS trial rates for tilted absolute values"**, arXiv:2609.09872v1.

- Submitted 9 Sep 2026; not published; math.NA and math.OC.
- Fetched: https://arxiv.org/abs/2609.09872 and https://arxiv.org/html/2609.09872v1.
- Not mentioned anywhere in the repository.
- **Claim (Theorem 3.1 and Corollary 4.1):** for f_u(x) = max{x, −ux} on R, every u ∈ (9/5, 13/6) and
  every c2 ∈ (0,1), with c1 = 0 and the Lewis–Overton doubling/bisection line search ([LO 2008,
  Algorithm 2.6]), two nonterminating executions have different trial-normalized R-linear factors. This
  refutes the initialization-independence part of Lewis–Overton's Conjecture 4.1 in the 2008 Optimization
  Online preprint "Nonsmooth optimization via BFGS".
- **Comparison:**
  - Its setting is 1-D, whereas the article's counterexamples are in R^2.
  - It uses c1 = 0; the article requires 0 < c1.
  - Both of its runs converge to the minimizer, so it says nothing about convergence or failure, which
    are the article's subjects.
  - It shares the doubling/bisection search and the deterministic, initialization-dependent flavor of
    the article's failure constructions.
- **Assessment:** an optional citation in the "Deterministic limits" paragraph, as recent evidence that
  even 1-D nonsmooth BFGS behavior depends on the initialization. It does not affect any claim.

### RELATED (low; smooth setting, outside my author scope, passed on to agent B)

**L. Ding, J. Yang, B. Zhou, "On the Complexity of BFGS Method for Smooth Convex Optimization"**,
arXiv:2608.16009v1.

- Submitted 17 Aug 2026; fetched: https://arxiv.org/abs/2608.16009.
- **Claim:** BFGS with an Armijo–Wolfe line search on L-smooth convex functions without strong
  convexity: min_{i≤k} ||∇f(x_i)|| = O(k^{-1/2}), and the value gap is O(1/k) with bounded sublevels. It
  uses the trace-log-det potential.
- **Assessment:** smooth only, so no overlap with the article's nonsmooth claims. At most a "recent
  potential-function analyses" pointer next to Jin–Jiang–Mokhtari.

**B. Liu, C. Li, Z. Wen, "The Minimum Q-Order of BFGS with Exact Line Search Is One"**, arXiv:2609.00596v1.

- Submitted 1 Sep 2026; fetched: https://arxiv.org/abs/2609.00596.
- Smooth, strongly convex, exact line search, Q-order only. It uses Lewis–Zhang's convex realization
  criterion (Proposition 3.1).
- **Assessment:** no overlap.

### IRRELEVANT

About 520 author-list entries and about 60 topic-search entries from 2022 onwards were judged irrelevant.
They include:

- Lewis–Pirani 2608.20642 (full text has no BFGS);
- Gebken–Ulbrich 2603.23236 and 2603.23261;
- Jiang–Mhammedi–Mohri–Mokhtari 2602.08232;
- Kong–Lewis 2210.00652 and 2405.12655;
- Asl–Lu–Yang 2202.02279;
- Zhao 2608.29300 (a smoothed and modified L-BFGS for minimax);
- vom Dahl–De Marchi–Kanzow 2605.11627 (proximal limited-memory quasi-Newton).

## Citation and metadata updates

1. **No version updates are needed.** Every preprint the article pins to v1 is still at v1. Jin–Mokhtari
   is still at v2 and is published in NeurIPS 2025, as the companion records.
2. **Optional:** Gebken JOTA has issue number 2 (Crossref: volume 209, issue 2, article 57). The paper's
   `bibliography.tex` and the companion print "209, article 57"; adding "(2)" is optional.
3. **Metadata error (TODO for the coordinator).** The coauthor of Lewis–Zhang (JOTA 165 (2015), doi
   10.1007/s10957-014-0622-7) is **Shanshan Zhang**:
   - evidence: the MaRDI/zbMATH record https://portal.mardi4nfdi.de/wiki/Publication:2346393 and her
     2013 Cornell PhD thesis "Theory and Algorithms for Structured Nonsmooth Optimization", whose BFGS
     chapter has the same abstract;
   - files that say "Shubao Zhang":
     - `editorial/LITERATURE_LEDGER.json` (line 761)
     - `editorial/narrative_rebuild/prior_records/LITERATURE_LEDGER.json` (line 706)
     - `bfgs_lean_stage1/literature_audit/SOURCES.json` (line 533)
     - `bfgs_lean_stage1/literature_audit/packets/negative_D_L.json` (line 70)
     - `bfgs_lean_stage1/literature_audit/references.bib` (line 191)
   - The printed article and companion use "S. Zhang", so neither needs a change.
   - `bfgs_lean_stage1/` is hash-pinned, so record it there as a known erratum rather than edit it.
   - The `editorial/LITERATURE_LEDGER.json` entry is generated, so fix it at its source and regenerate.
4. **Optional:** cite Chen 2609.09872 (R1).

## Works I could not access, or accessed only partly

- **link.springer.com:** a JavaScript challenge blocked it. The same published article was read in full
  at rd.springer.com.
- **DBLP:** HTTP 429 and a bot challenge; I used OpenAlex, arXiv and Semantic Scholar instead.
- **arXiv export API:** HTTP 429 after the first queries; the arxiv.org search and abstract pages worked.
- **zbmath.org:** HTTP 403; I used the MaRDI mirror instead.
- **Lewis's publication page and CV:** both stale (2019). His 2022–2026 output was taken from arXiv
  (43 entries) and OpenAlex (16 works).
- **Wächter's Northwestern page:** no longer maintained; I used arXiv and OpenAlex.
- **Google Scholar:** not queried directly; web search snippets of Gebken's Scholar profile were used.
- **Optimization Online:** a site search found no nonsmooth-BFGS postings by these authors after 2020.

## Conclusion

From the authors' side and for the cited preprints, nothing published or posted up to 16 October 2026
makes the article stale. The open problems the article claims to settle are still described as open in
the newest relevant work: Gebken, JOTA, May 2026, for u^2+|v|, and Guo–Lewis's conjecture. No named
author has posted a competing result. The only new and relevant item is Chen 2609.09872: 1-D, c1 = 0,
about rates, and optional to cite. Fix the "Shubao Zhang" metadata in the ledger.
