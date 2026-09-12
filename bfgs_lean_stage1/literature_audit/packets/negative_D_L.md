# Literature comparison for the negative results in Modules D and L

Search performed 2026-09-11 America/Los_Angeles (2026-09-12 UTC); cutoff is this search time. This packet compares the corrected report, not the uncorrected archives. It does not independently reprove external papers, and failure to find a match is not a proof of novelty. Companion JSON records sources, locators, search queries, access limits, and classifications.

## Conclusions by claim

| Report claim | Classification | Result of comparison |
|---|---|---|
| N1 / D Theorem 1: one coercive maximum of four convex C2,1 branches, fixed identity initialization, bad starts approaching the unique nonsmooth minimizer, actual unit-first bracketing with all differentiable queries | `no_exact_match_found` | No accessed source has this complete combination. Keep the no-uniform-positive-curvature qualification. |
| N2 / L Theorem 2, first version: strongly convex four-C1,1-branch objective with a common fixed initial matrix and arbitrarily close bad starts | `no_exact_match_found` | No accessed source has this combination. The lack of second differentiability of the branches at the accumulation point is essential to the report's stated scope. |
| N2 / L Theorem 2, second version: countable polyhedral nonsmooth part and a constant positive definite classical Hessian wherever it exists | `no_exact_match_found` | No accessed exact match. This is a different representation from the finite smooth-branch version. |
| N3 / D §3: coercive four-affine maximum with deterministic nonstationary convergence | `no_exact_match_found` | The older convex polyhedral failure below has a materially different oracle and null-step mechanism. |
| N3 / L Theorem 1: positive quadratic plus a three-affine maximum, actual bracketing and nonstationary convergence | `no_exact_match_found` | No accessed exact match. It is a global failure, not failure arbitrarily near its true minimizer. |

The phrase “no exact match found” describes a bounded literature search with moderate confidence. It does not authorize a “first ever” claim. In particular, these existential bad-start constructions do not settle the almost-sure random-initialization challenge of [Lewis–Overton, §7, pp.160–161](https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf).

## Closest negative results and exclusions

**Lewis–Overton (2008).** Their author manuscript §3, Examples 3.1/3.3 and Proposition 3.2 (PDF pp.3–4), treats a convex three-affine maximum through a conceptual subgradient extension of exact-search BFGS. Nondifferentiable points and null steps make later matrices singular. D/L instead use strictly positive accepted lengths, differentiable queries, and positive definite matrices at every finite iteration. These are related failure questions, not the same theorem. [Primary manuscript](https://cs.nyu.edu/overton/papers/pdffiles/bfgs_exactLS.pdf)

**Lewis–Zhang (2014 online; 2015 issue).** The publisher explicitly describes convergence to a stationary point that nevertheless has descent directions. The 2013 manuscript's indexed §4 distinguishes Clarke stationarity from regular stationarity. Thus this does not already establish convex nonstationary convergence. Full manuscript retrieval was unsuccessful in this audit; the publisher abstract and indexed author text were checked, so exact proof equivalence is left unresolved. [Publisher](https://link.springer.com/article/10.1007/s10957-014-0622-7) · [Author manuscript](https://people.orie.cornell.edu/aslewis/publications/sub-nonsmoothness.pdf)

**Asl–Overton (2021 issue; 2020 online; 2018 preprint).** Theorem 3.11 and Corollary 3.12 establish fixed-bracketing nonoptimal convergence for **scaled memoryless BFGS**, on a two-piece convex function unbounded below. Theorem 3.11 uses the standing size condition on the nonsmooth slope. The scaling and memory restriction prevent importing the result as a full-BFGS counterexample. [Published full text, §3.3](https://academic.oup.com/imajna/article/41/1/1/5706038)

**Mascarenhas (2004).** Theorems 1–4 (pp.52–54), with proofs in §§2–3, construct a smooth nonconvex three-dimensional example with exact global line minimizers and a positive Armijo margin. This is a substantial older failure result, but its smooth nonconvex objective and asymptotic octagon differ from D/L's convex two-dimensional shrinking orbits. [Author-hosted published article](https://www.ime.usp.br/~walterfm/orientacao/bfgs.pdf)

**Mascarenhas (2007; 2014).** These strengthen the smooth nonconvex failure examples to compact level sets and search-line convexity; the 2014 example also uses unit steps. Global convexity is absent. The 2007 published §§3–7 and the 2013 preprint of the 2014 article §§3,5 were inspected. [2007 published full text](https://www.scielo.br/j/cam/a/JBFzLzr4PNdcqKHJRRS4mHf/) · [2014 article's preprint](https://arxiv.org/pdf/1309.7922)

**Dai (2002/2003; 2013).** These are smooth nonconvex counterexamples, including a later four-dimensional polynomial and unit steps. The 2002 paper's primary abstract/bibliography and the later author's manuscript/primary publisher abstract were accessed; a complete proof review of both versions was not completed. They remain context rather than grounds for an exact-overlap verdict. [2002 DOI](https://doi.org/10.1137/S1052623401383455) · [2013 publisher](https://link.springer.com/article/10.1007/s10107-012-0522-2)

**Diao (new preprint, 9 September 2026).** Theorem 1 and §5.2 give a smooth nonconvex planar failure with bounded-below objective and Lipschitz gradient, for every prescribed Wolfe pair. The trajectory escapes to infinity and the sublevels are unbounded. Its first-local-minimizer exact search differs from D/L's bracketing. The proof uses an explicitly prescribed orbit and tubular interpolation. This timely neighboring result belongs in related work, but does not duplicate D/L. Its correctness was not independently certified here. [Theorem 1 and proof](https://arxiv.org/html/2609.09686v1)

## Existing proof ingredients and attribution

| Ingredient used in D/L | Existing work / comparison | Attribution status |
|---|---|---|
| Unit-first weak-Wolfe doubling/bisection | Lewis–Overton Algorithm 4.6, p.147; earlier draft calls it Algorithm 2.6 | Explicitly cited as `[LO]` in D §1. This algorithm is existing work. |
| Affine invariance, fixing a common SPD initialization to identity | Lewis–Overton §2, p.140 states the full Broyden-class change-of-variables property | Established ingredient; `[LO]` is in the report but L's final transformation has no local citation. Add one in a future bibliographic edition. |
| Finite algebraic seed, scaling/periodicity, matrix closure, then objective extension | Mascarenhas 2004 Theorems 1–4; 2007 §§3–7; 2014 preprint §3 | Strong methodological precedent. D's specific convex scalar plateau construction is not identified as their Whitney extension construction. No causal borrowing can be inferred. |
| Normalized state separating scale from shape | Lewis–Overton 2008 §4, equation (4.1) and Algorithm 4.2; broader scaling symmetry in Mascarenhas | Existing general technique; the particular D/L three-step return map is not located in those works. |
| Stable manifold of a hyperbolic fixed point | Dyatlov §§3–4, Theorems 3–4; graph transform construction and invariant contracting manifold | Explicit `[DY]` in L's global-failure proof. This theorem is classical; neither it nor the general method is a new BFGS result. [Primary notes](https://arxiv.org/pdf/1805.11660) |
| Preconditioned residual map on a rational box, derivative bound, existence/uniqueness | Rump (2010), §13, Theorem 13.3, author-PDF p.89: related interval enclosure using a preconditioned residual map | Standard validated-numerics technique; D uses an explicit contraction bound and Lean rational checks. No claim of using INTLAB or of identical code. [Primary article](https://www.tuhh.de/ti3/rump/intlab/ActaNumerica2010.pdf) |
| Strict finite query inequalities persist under perturbation | Elementary continuity and finite intersection of open neighborhoods | Standard argument. No specialized external theorem is needed; novelty can concern its particular return-map application. |

D/L cite internal labels `[SD]` for the report's own seed. Such labels are not external publication evidence. The corrected bibliography includes `[LO]`, `[DY]`, `[XW]`, and `[BG]`; it does not list the Mascarenhas, Dai, Asl–Overton, Lewis–Zhang, Diao, or Rump items discussed here. The preceding table identifies mathematical precedents; it cannot reveal which sources influenced the earlier AI generations.

## Positive results that delimit the negative comparison

Xie–Wächter's Theorem IV.1 and Remark IV.2 (2017 preprint, pp.9–14) prove finite detection of an unbounded descent direction on the relevant **two-piece** affine class. This helps explain why D uses three active slopes and why the memoryless failure is not interchangeable with full BFGS. [Primary preprint](https://arxiv.org/pdf/1712.08571)

Gebken's May 2026 article Theorem 3.1 assumes Behavior (B1), including convergence of iterates and explicit spectral behavior of the matrices, as well as local geometry (A2). It is not an unconditional theorem contradicted by D/L. Its updated publication metadata should replace a preprint-only entry in future related work. [Primary full article, §§3–4](https://link.springer.com/article/10.1007/s10957-026-03008-z)

## Search limitations

The search covered scholarly web results, arXiv, author pages, publisher full text, and references in the closest papers, including recent 2025–2026 work and distinctive seed constants. It did not exhaust every dissertation, language, unpublished manuscript, subscription archive, or citation database. The exact decimal seed and the phrase combinations for local failure did not return a matching primary paper. Some engines returned unrelated or AI-generated aggregation pages; those were not used as evidence. Access-limited records are explicitly qualified in JSON. No external PDF or full-text article is redistributed in this packet.
