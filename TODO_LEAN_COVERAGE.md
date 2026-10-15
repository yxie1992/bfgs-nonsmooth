# TODO: Lean coverage of every claim

Started 14 October 2026, at the author's request: "We want lean to have 100%
coverage for all proofs and claims on both main manuscript and companion."
Reviewer: AI assistant (Claude). Method, statuses and rules:
`editorial/lean_coverage/README.md`.

Agreed scope:
- Every definition, named result, result stated in prose, and displayed formula
  asserted as true (also inside proofs), plus the claims of the abstract,
  introduction, remarks, tables and captions, gets a Lean theorem with the same
  statement. Each proof is covered by the Lean proof of its result; undisplayed
  connecting steps are left to the line-by-line reading of the proofs, which
  follows this work.
- Open questions are stated in Lean without proof and marked open. Literature
  results that the documents use are proved in Lean. History, motivation,
  descriptions of software or runs, and literature only mentioned are
  classified as non-claims with a reason.

Progress (`python3 editorial/lean_coverage/check_coverage.py`), 14 October 2026:

| Document | Items | Status |
|---|---|---|
| Article (`paper/`, 15 files) | 616 (221 mechanical, 395 prose) | complete: every item classified; 15 coverage modules, each reviewed by an independent agent, imported by `BfgsArticle.lean` |
| Companion (`companion/`, 18 files) | 573 mechanical; prose items not yet added | waves 1 and 2 in progress on the MacBook (14 October); wave 3 not started |

Article items by status: LEAN 280, SAME_AS 124, NON_CLAIM 89, DEFINITION 51,
PART_OF 34, PROOF 28, DISCREPANCY 9 (manuscript items M7–M11), OPEN 1.

Companion groups (prompts and hints: `editorial/lean_coverage/AGENT_BRIEFS.md`;
how to resume: `HANDOFF.md`). Files are in `companion/`, modules in
`bfgs_lean_article/BfgsArticle/Coverage/Companion/`, pause notes in
`editorial/lean_coverage/pause_notes/<group>.md`.

| Group | Files | Modules | State |
|---|---|---|---|
| compM | `chapters/02_M.tex` | `Ch02M` | done: 95 items (LEAN 41, DEFINITION 6, PART_OF 12, PROOF 6, SAME_AS 11, NON_CLAIM 19), no discrepancy, wording points W1–W5; reviewed, fix pass done |
| compR | `chapters/04_R.tex` | `Ch04R` | wave 1: resumed from its pause note, in progress |
| compC | `chapters/09_C.tex` | `Ch09C` | wave 1: resumed from its pause note, in progress |
| compH | `chapters/07_H.tex` | `Ch07H` | wave 1: resumed from its pause note, in progress |
| compD | `chapters/12_D.tex`, `appendices/seed_certificate.tex` | `Ch12D`, `SeedCertificate` | wave 1: resumed from its pause note, in progress |
| compL | `chapters/13_L.tex` | `Ch13L` | wave 1: resumed from its pause note, in progress |
| compTA | `chapters/03_T.tex`, `chapters/08_A.tex` | `Ch03T`, `Ch08A` | wave 2: in progress |
| compG | `chapters/05_G.tex` | `Ch05G` | wave 2: in progress |
| compFQ | `chapters/06_F.tex`, `chapters/10_Q.tex` | `Ch06F`, `Ch10Q` | wave 2: in progress |
| compU | `chapters/11_U.tex` | `Ch11U` | wave 2: in progress |
| compFront | `chapters/01_I.tex`, `chapters/14_E.tex`, `research_story.tex`, `current_verification.tex`, `correspondence.tex` | `Ch01I`, `Ch14E`, `ResearchStory`, `CurrentVerification`, `Correspondence` | wave 3, after all chapters |

## Open items

- [x] Article: every item classified; the coverage modules
      `bfgs_lean_article/BfgsArticle/Coverage/Article/*.lean` written, reviewed
      independently and imported by `BfgsArticle.lean` (14 October 2026).
- [ ] Companion: the same, `.../Coverage/Companion/*.lean` (groups above).
- [x] The axiom audit includes every Lean name of the registers (audit of
      `a2028c9`: 3862 declarations, PASS).
- [ ] When the companion is done: rerun the axiom audit and the kernel replay
      (the committed replay predates the coverage modules).
- [ ] Discrepancies go to `TODO_MANUSCRIPT_REVIEW.md` (article: M7–M11). When the
      manuscript is corrected, give each `DISCREPANCY` item its final status (for
      example `A/seed_certificate/prose/012` becomes `PROOF` once M11 is fixed)
      and refresh the items whose source changed.
- [x] Non-vacuity follow-up (done 14 October 2026): no admissible run had been
      exhibited on the three-branch objective of Theorem `art:nonradial-example`.
      `bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean` now proves a general
      existence theorem, `AdmissibleRunExistence.exists_admissible_run`: if F is
      convex, bounded below, differentiable at all but countably many points of every
      line through a point of differentiability, and has no point of
      differentiability with gradient zero, then from every point of
      differentiability, for every H₀ ≻ 0 and all 0 < c₁ < c₂ < 1, an infinite
      admissible run exists (each step strict Armijo and strict weak Wolfe). For the
      three-branch objective, `PlanarQuadraticExample.nonradial_example_nonvacuous`
      gives such a run with F(x₀) < 1/100 whose values and iterates converge to zero.
      The registers cite it (`A/local/theorem/art:nonradial-example`,
      `A/global/prose/019`). The theorem does not apply when a kink set contains a
      segment of such a line (for example max(|v|, u − 10)); those objectives keep
      explicit runs.
- [ ] Run `lake build` once no agent runs Lean (before wave 3). `BfgsArticle.lean`
      now imports `BfgsArticle.AdmissibleRunExistence` and each companion coverage
      module as it is committed, but agents run Lean continuously, so these were
      checked only with `lake env lean` (no errors, no warnings). Until the build,
      the axiom audit cannot resolve their names.
