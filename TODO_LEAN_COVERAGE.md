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

Progress (`python3 editorial/lean_coverage/check_coverage.py`), 15 October 2026:

| Document | Items | Status |
|---|---|---|
| Article (`paper/`, 15 files) | 619 (221 mechanical, 398 prose) | complete: every item classified; 15 coverage modules, each reviewed by an independent agent, imported by `BfgsArticle.lean` |
| Companion (`companion/`, 18 files) | 1856 (573 mechanical, 1283 prose) | complete (14 and 15 October, on the MacBook): every item classified; 18 coverage modules in twelve groups, each group reviewed by an independent agent, imported by `BfgsArticle.lean` |

Article items by status: LEAN 286, SAME_AS 128, NON_CLAIM 89, DEFINITION 52,
PART_OF 34, PROOF 29, OPEN 1 (three prose items added with the corrections M30–M41). The nine `DISCREPANCY` items (manuscript items
M7–M11) were resolved by the corrections of 15 October 2026; their register entries
are kept under `resolved_discrepancies`.

Companion items by status: LEAN 834, SAME_AS 372, NON_CLAIM 358, DEFINITION 139,
PART_OF 86, PROOF 56, OPEN 11. The 25 `DISCREPANCY` items (manuscript items M12–M29,
and the recurrences listed under M8, M12 and M24) were resolved by the corrections
of 15 October 2026; their register entries are kept under `resolved_discrepancies`.

Companion groups (prompts and hints: `editorial/lean_coverage/AGENT_BRIEFS.md`;
how to resume: `HANDOFF.md`). Files are in `companion/`, modules in
`bfgs_lean_article/BfgsArticle/Coverage/Companion/`, pause notes in
`editorial/lean_coverage/pause_notes/<group>.md`.

| Group | Files | Modules | State |
|---|---|---|---|
| compM | `chapters/02_M.tex` | `Ch02M` | done: 95 items (LEAN 41, DEFINITION 6, PART_OF 12, PROOF 6, SAME_AS 11, NON_CLAIM 19), no discrepancy, wording points W1–W5; reviewed, fix pass done |
| compR | `chapters/04_R.tex` | `Ch04R` | done: 161 items (LEAN 103, NON_CLAIM 19, SAME_AS 15, DEFINITION 11, PART_OF 8, PROOF 5), no discrepancy; wording points W8, W13, W19–W23; reviewed, fix pass done |
| compC | `chapters/09_C.tex` | `Ch09C` | done: 180 items (LEAN 108, NON_CLAIM 21, SAME_AS 20, DEFINITION 12, PROOF 10, PART_OF 8, DISCREPANCY 1: M20); wording points W8, W14, W15; reviewed, fix pass done |
| compH | `chapters/07_H.tex` | `Ch07H` | done: 118 items (LEAN 73, PROOF 7, SAME_AS 11, NON_CLAIM 11, PART_OF 10, DEFINITION 3, OPEN 2, DISCREPANCY 1: M17); OPEN: lines 142–146 (`ZeroValueIterateQuestion`) and lines 461–463, runs on the common-tilt family (`TiltNoInfiniteRunQuestion`; see `TODO_LEAN_REVIEW.md`); reviewed, fix pass done |
| compD | `chapters/12_D.tex`, `appendices/seed_certificate.tex` | `Ch12D`, `SeedCertificate` | done: `12_D.tex` 133 items (LEAN 77, DEFINITION 15, SAME_AS 23, PART_OF 4, PROOF 3, NON_CLAIM 10, DISCREPANCY 1: M14); `seed_certificate.tex` 43 items (SAME_AS 27, NON_CLAIM 8, LEAN 3, PROOF 2, DISCREPANCY 3: M15, M16); wording points W6–W9; M11 does not recur; reviewed, fix pass done |
| compL | `chapters/13_L.tex` | `Ch13L` | done: 142 items (LEAN 48, DEFINITION 29, PART_OF 3, PROOF 3, SAME_AS 38, NON_CLAIM 17, OPEN 1, DISCREPANCY 3: M8 recurrence, M12, M13); OPEN: line 61, four $C^2$ branches (`FourC2BranchLocalFailure`); reviewed, fix pass done |
| compTA | `chapters/03_T.tex`, `chapters/08_A.tex` | `Ch03T`, `Ch08A` | done: `03_T.tex` 74 items (LEAN 36, DEFINITION 11, SAME_AS 10, NON_CLAIM 8, PART_OF 5, PROOF 1, DISCREPANCY 3: M24–M26); `08_A.tex` 73 items (LEAN 39, NON_CLAIM 15, SAME_AS 8, DEFINITION 5, PART_OF 3, PROOF 2, OPEN 1: the general-dimensional conjecture, `GeneralDimensionalConjecture`); wording points W5, W17, W18; reviewed, fix pass done |
| compG | `chapters/05_G.tex` | `Ch05G` | done: 127 items (LEAN 68, DEFINITION 16, SAME_AS 16, NON_CLAIM 13, PROOF 6, PART_OF 5, DISCREPANCY 3: M21–M23); wording points W11, W13, W16; reviewed, fix pass done |
| compFQ | `chapters/06_F.tex`, `chapters/10_Q.tex` | `Ch06F`, `Ch10Q` | done: `06_F.tex` 99 items (LEAN 62, NON_CLAIM 20, DEFINITION 5, SAME_AS 5, PART_OF 3, PROOF 3, DISCREPANCY 1: M27); `10_Q.tex` 100 items (LEAN 73, DEFINITION 12, NON_CLAIM 6, PART_OF 3, SAME_AS 3, PROOF 2, DISCREPANCY 1: M28); wording points W13, W24–W26; reviewed, fix pass done |
| compU | `chapters/11_U.tex` | `Ch11U` | done: 119 items (LEAN 61, SAME_AS 21, PART_OF 11, NON_CLAIM 11, DEFINITION 8, PROOF 5, DISCREPANCY 2: M18, M19); wording points W8, W10–W13; reviewed, fix pass done |
| compI | `chapters/01_I.tex`, `research_story.tex` | `Ch01I`, `ResearchStory` | done: `01_I.tex` 183 items (SAME_AS 89, NON_CLAIM 48, LEAN 20, PART_OF 11, OPEN 6, DEFINITION 5, PROOF 1, DISCREPANCY 3: recurrences of M8, M12 and M24); `research_story.tex` 36 items (SAME_AS 26, NON_CLAIM 9, DISCREPANCY 1: recurrence of M8); wording points W31–W43; reviewed, fix pass done |
| compE | `chapters/14_E.tex`, `current_verification.tex`, `correspondence.tex` | `Ch14E`, `CurrentVerification`, `Correspondence` | done: `14_E.tex` 106 items (NON_CLAIM 64, SAME_AS 35, LEAN 4, OPEN 1: the questions left open in Chapters 7 and 8, DISCREPANCY 2: M29); `current_verification.tex` 36 items (NON_CLAIM 31, SAME_AS 5); `correspondence.tex` 31 items (NON_CLAIM 28, SAME_AS 3); wording points W27–W30 (W30: stale statements about the verification and the records, refreshed in step 2); reviewed, fix pass done |

## Open items

- [x] Article: every item classified; the coverage modules
      `bfgs_lean_article/BfgsArticle/Coverage/Article/*.lean` written, reviewed
      independently and imported by `BfgsArticle.lean` (14 October 2026).
- [x] Companion: the same (15 October 2026): every item classified; the 18 modules
      `.../Coverage/Companion/*.lean` written, each group reviewed independently,
      and imported by `BfgsArticle.lean` (groups above).
- [x] The axiom audit includes every Lean name of the registers (audit of
      `a2028c9`: 3862 declarations, PASS).
- [x] When the companion is done: rerun the axiom audit and the kernel replay
      (15 October 2026, commit `9f03d7c`, clean tree: audit PASS, 5403
      declarations, standard axioms only; kernel replay PASS, 783 modules;
      `bfgs_lean_article/AXIOM_AUDIT.json`, `KERNEL_REPLAY.json`).
- [x] Discrepancies go to `TODO_MANUSCRIPT_REVIEW.md` (article: M7–M11; companion:
      M12–M29 and the recurrences under M8, M12 and M24; wording points W1–W47). When the
      manuscript is corrected, give each `DISCREPANCY` item its final status and carry
      the registers across the edit (`editorial/lean_coverage/README.md`, "After a
      correction"). Article: done on 15 October 2026 (M7–M11 corrected; the nine items
      resolved, for example `A/seed_certificate/prose/012` is now `PROOF`).
      Companion: done on 15 October 2026 (M12–M29 and the recurrences corrected, the
      25 items resolved, independently reviewed; wording points W1–W11 and W14–W46
      applied, W12 and W13 left for the author, W47 open). Since then
      `check_coverage.py --strict` passes on every file without
      `--allow-discrepancies`.
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
- [x] Run `lake build` once no agent runs Lean (done 15 October 2026, before wave 3).
      `BfgsArticle.lean` imports `BfgsArticle.AdmissibleRunExistence` and each
      companion coverage module as it is committed; while agents ran Lean these were
      checked with `lake env lean` only. The build rebuilt them and the two roots:
      exit 0 in 144 s, no warning from the article package (the main library's 1244
      style warnings stay).
