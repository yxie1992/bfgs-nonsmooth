# Narrative review of the article (16 October 2026)

Reviewer: AI assistant (Claude), at the author's request: "narratively, or
writing-wise, we have a long way to go. Read the paper, how can we make the
overall story easier to follow for human?"

Scope: the article's main text (`paper/sections/`, `paper/statements/`, 34 of
54 pages, about 12,200 words) and the appendix headings. The mathematics is
taken as settled; this review is about order, emphasis, terminology and prose.
Page and theorem numbers refer to the build of the 15 October edition with
Appendix E (svjour3 numbers theorems, corollaries and lemmas separately).

## The story the paper can tell

BFGS converges on u²+|v| (open since Guo–Lewis 2018, still listed open by
Gebken 2026) and on a broad convex class built around it; it can also fail on
a coercive maximum of four affine functions in the plane, and near the
minimizer of a single smooth (or strongly convex) piecewise objective. One
idea proves every positive result: an energy that would have to grow linearly
if a gap persisted, against a principal-minor hierarchy that forces faster
growth. One mechanism produces every failure: a three-step cycle that returns
the iterate and the matrix to a smaller copy of themselves near a corner from
which descent is still possible, so that the steps are summable.

The current text contains all of this, but a reader has to assemble it.

## Diagnosis

1. **The headlines are buried.** The two most quotable results are
   Corollary 2 on p. 15 (`art:mixed-benchmark`, u²+|v|) and Corollary 8 on
   p. 28 (`art:failure_polyhedral`, four affine pieces, H₀ = I, the
   Lewis–Overton line search, convergence to a nonstationary point). The
   second is not mentioned in the abstract or the introduction; Section 2
   cites it only to limit the positive claims.

2. **No informal statement of the main results.** The introduction describes
   the results in words with qualifications attached ("centered
   smooth-plus-sublinear objectives with compact initial sublevels contained in
   the region where the representation holds"), before any of these terms is
   defined. There is no list or box of main theorems a reader can return to.

3. **Three different orders.** The abstract goes positive → negative →
   technique; the introduction ("We give three answers", and its paragraphs)
   goes negative → positive → technique; the sections go overview →
   technique → global → local → failure.

4. **Section 2 comes before what it explains.** "What the results say about
   nonsmooth BFGS" (pp. 4–6) mixes the u²+|v| intuition, the counterexample's
   seed gradients (with an algebraic number defined in Appendix C, before the
   BFGS update is defined), an affine-versus-convex balance excursion that is
   first needed in the planar subsection of Section 5, the scope table, and
   the hypothesis-check guide added for M42.

5. **The machinery is more general than its use.** Definition 2
   (`art:band-certificate`: PSD fields, projected transport with constant L)
   and Theorem 3 (`art:certificate`) prove one result of the main text, with a
   rank-one field and L = 0 (Corollary 1, radial); Appendix E instantiates the
   definition twice as worked examples (the mixed ridge, and a full-rank
   calibration). The only proof that needs a moving field, Theorem 8
   (`art:planar-cluster`), cannot apply Theorem 3, because its field exists
   only near the cluster set rather than on a whole band; it repeats the
   summation "exactly as in the proof of Theorem 3". The reader learns an
   abstraction whose generality no main result uses, and the case that needs
   transport is argued separately.

6. **No example-first path through the positive theory.** The u²+|v| proof
   fits in half a page (energy r_kᵀB_kr_k, its identity, the exact inward
   remainder τ²u², reciprocal growth). In the text it arrives as a corollary
   after the radial secant condition, the inward condition (both with
   ε-band quantifiers), their one-way equivalence, the radial corollary and
   the centered theorem.

7. **The planar subsection runs backwards.** The three-quadratic example that
   motivates moving fields (Theorem 9) comes last, after a page-long sketch of
   the field construction and three results; the introduction, Section 2 and
   Section 4 all refer forward to it.

8. **Overlapping local results.** The lasso is covered twice: as a smooth
   loss plus polyhedral regularizer (Corollary 4, `art:plq`) and through the
   centered decomposition (Corollary 5 and the display after it).

9. **The failure section front-loads data.** Section 6 (pp. 24–34) gives the
   seed's slopes, ρ, matrices and steps before the picture of the cycle, and
   keeps the full scalar interpolation (t_b, P_b, J_b, the constant
   139264/(5b²)) in the main text. The idea "the cycle shrinks by ρ, so the
   steps are summable and the run stalls at the corner" is never said in one
   sentence.

10. **Terminology drift.** u²+|v| is the "mixed model", "mixed benchmark",
    "mixed ridge", "quadratic–absolute-value benchmark" and "benchmark"; the
    bad point is the "wrong corner", "bad corner", "nonstationary corner",
    "wrong vertex" and "seed"; the analytical object is a "comparison
    energy/field/geometry/direction", "band certificate", "transported
    comparison certificate", "moving geometry" and "contour field".

11. **Qualifications are scattered rather than stated once.** In the main
    text: "does not" 13 times, "do not" 11, "need not" 8, "neither" 11,
    "admissible" 28, "actual" 16. Most are the same few scope statements
    repeated (a run is assumed to exist; conditions are sufficient, not
    necessary; failures are deterministic starts, not positive measure; the
    comparison field is not part of the algorithm). They were added as
    overclaim guards in earlier reviews and must be kept, but once each, where
    a reader can find them.

12. **Prose habits.** Paragraphs often open with an abstract claim and give
    the concrete content later ("The positive conclusions differ in their
    geometry and in the locality of the guarantee."); many sentences take the
    form "X; it is not Y"; references to the companion (8 in the main text)
    appear before the companion is introduced (introduction, line 47).

13. **Missing reader aids.** No dependency map of the results; no picture of
    a converging run to set against the failing cycle the title also
    promises; the Lean verification, a distinctive strength, gets one sentence
    at the end of the introduction and one paragraph at the end of the paper.

14. **The abstract** has 14 sentences and relies on undefined terms
    ("centered smooth–sublinear", "region of the centered representation",
    "unit-first implementation", "complete trial trees", "infinite local
    embeddings", "adjacent-degree hierarchy").

## Proposed outline

1. **Introduction.** The question; prior work (Lewis–Overton, Guo–Lewis,
   Gebken; Xie–Wächter shortened); a box of main results stated informally,
   positive and negative side by side (A: u²+|v| and the centered family;
   B: coercive homogeneous, norms, max-linear; C: local, polyhedral cells and
   planar maxima; D: failure, the four-piece polyhedral global example and the
   two local regimes); the proof idea in one paragraph with the energy
   identity and its contradiction; one "Scope and conventions" paragraph
   collecting the qualifications; formal verification stated precisely;
   organization with a dependency map.
2. **Setting and the energy method.** Admissible runs, invariants, the energy
   identity, the hierarchy, reciprocal growth, and one energy lemma about
   the tail of a run, in the form actually used: comparison vectors w_k with
   (g_kᵀw_k)² ≥ m, (y_kᵀw_{k+1})² ≤ C t_k, and w_{k+1} = λ_k w_k + β_k s_k with
   λ_k² ≤ 1 + L d_k contradict reciprocal growth. Radial is w_k = x_k − x_*
   (λ = β = 1); planar is the contour field. Theorem 3 can be kept as a
   consequence (Appendix E uses Definition 2), or its PSD-field form left to
   the companion.
3. **Global convergence.** Warm-up: the complete proof for u²+|v|; then
   inward accuracy, the centered theorem, coercive homogeneous objectives,
   norms.
4. **Local convergence.** Localization; finite cells (one path to the
   lasso); curved interfaces in the order example (radial fails) → moving
   field → theorem → nondegenerate planar maxima.
5. **Failure.** The cycle idea and its figure; the four-piece polyhedral
   failure as the section's first theorem; scale matching; the local C^{2,1}
   embedding; the strongly convex variant. Explicit interpolation formulas to
   an appendix, with a figure of φ_b.
6. **What separates the two sides; open questions** (enumerated);
   verification; AI assistance.

Section 2 is dissolved: the u²+|v| geometry goes to the warm-up, the seed
geometry to Section 5, the affine/convex balance to the planar subsection, the
scope table to the introduction's main-results box, and the hypothesis-check
guide to the end of the local section or the start of Appendix E.

## Stages

- **A. Prose only, no statement or numbering changes.** Abstract;
  main-results box; one scope paragraph and removal of repeated caveats;
  terminology; companion references; mention Corollary 8 in the abstract
  and introduction; align the introduction's order with the sections.
- **B. Reordering within sections.** Example-first warm-up in Section 4;
  planar subsection reordered; failure section led by the polyhedral
  example; one path to the lasso.
- **C. Structural.** Dissolve Section 2; state the tail energy lemma, derive
  Theorem 3 from it and apply it in the planar proof; move the
  interpolation formulas to an appendix; add the dependency map and
  convergence figure.

## Costs and constraints

Every stage edits the article, so each needs the PDF build and visual check,
the register resync (`editorial/lean_coverage/resync_register.py`), new
correspondence rows and, at the end, a release run. Stage A touches statement
text only where a theorem's wording changes (ideally nowhere). Stages B and C
renumber statements (correspondence and ledger) and move text between files
(registers are keyed to TeX files). Stage C's energy lemma is a new statement
and needs a Lean coverage theorem, which should follow from the existing
planar and radial proofs. A numerical convergence figure would be the article's
only floating-point content and should be labelled as an illustration, as the
existing cycle figure is.
