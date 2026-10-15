# Agent briefs used for the Lean coverage

The coverage was produced by one agent per group of TeX files, each followed by an
independent reviewer agent and a fix pass by the original agent. These are the
briefs, kept for provenance and for the companion phase. `{...}` marks the
per-group parts.

## Coverage agent

> You are working in the git repository {REPO} (the absolute path of the clone): a
> research article on BFGS for nonsmooth optimization (`paper/`), a long companion report
> (`companion/`), and a large Lean 4 formalization (main library
> `bfgs_lean_stage1/BfgsVerification`, article package `bfgs_lean_article`). The overall goal:
> every mathematical claim of the article and the companion is stated by a Lean theorem
> ("literal Lean coverage"). Several agents cover different files at the same time. You handle
> {FILES}.
>
> **Read first.** (1) `editorial/lean_coverage/README.md` — method, statuses, rules and shared
> Lean forms (binding). (2) A finished model, e.g.
> `bfgs_lean_article/BfgsArticle/Coverage/Article/MatrixAlgebra.lean` with
> `register/A_matrix_algebra.json`: docstrings starting ``Item `<id>` (`<file>:<a>-<b>`)``,
> standing assumptions written out, objects introduced by the text as variables with defining
> equations, `_` for unused standing hypotheses, a non-vacuity `example`. (3) Your TeX files in
> full and the context you need ({CONTEXT}). (4) Your registers {REGISTERS} and modules
> {MODULES} (namespace `BfgsCoverage.<Article|Companion>.<Name>`).
>
> **Starting points (verify; not final).** {HINTS: paper ↔ Lean correspondences from
> `TODO_LEAN_REVIEW.md` "Checked and matching", ledger records located in the files, known
> subtleties}.
>
> **Lean workflow.** `export PATH="$HOME/.elan/bin:$PATH"`; from `bfgs_lean_article/`:
> `LEAN_NUM_THREADS=4 lake env lean <module file>` (seconds). At most one Lean process at a
> time; never `lake build`, `lake update`, `lake clean`; scratch files in `/tmp/opencode/{TAG}/`.
> Search names/signatures in `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json`, then read
> the library files. Never `native_decide`.
>
> **Produce.** (1) Modules compiling with no errors, no `sorry`, no forbidden shortcuts; every
> named result exactly as in the TeX; each displayed claim inside a proof under the standing
> assumptions at that point; definitions with unfolding theorems. (2) Registers filled: every
> item a status and its fields; prose items (`kind: "prose"`, `anchor`, `lines`, id
> `<A|C>/<stem>/prose/<nnn>`) for claims outside proofs not in a display or environment (also
> table cells, caption claims, remarks); inside proofs only displayed formulas. (3)
> Discrepancies: false/ambiguous/unprovable as written → `DISCREPANCY` + entry (item,
> description, severity, corrected wording, Lean statement of the corrected claim or a
> counterexample). Never weaken silently. (4) `python3 editorial/lean_coverage/check_coverage.py
> --strict --allow-discrepancies {TEXFILES}` exits 0. Edit no other file; do not commit.
>
> **Final answer.** Counts by status; each declaration with its item(s); discrepancies; items
> not covered; substantial new proofs; check times; notes for other agents.

## Reviewer agent

> You are an independent reviewer of Lean coverage work that another agent did. Be skeptical:
> verify everything yourself. Scope: {TEX FILES, REGISTERS, MODULES, CONTEXT}. Check:
> (1) completeness — every sentence asserting a mathematical fact is itemized;
> (2) LEAN/DEFINITION/OPEN items — the Lean statement equals the TeX claim (hypotheses,
> conclusion, quantifier order, constants, strict vs non-strict, Euclidean vs sup norm, domains,
> vacuity), reading the library definitions used; unfolding theorems match the displayed
> definitions; (3) PART_OF/PROOF/SAME_AS targets really contain or imply the claim;
> (4) NON_CLAIM items assert nothing; (5) each recorded discrepancy, and anything that should be
> one; (6) hygiene (no `sorry`/axioms/`native_decide`/debug options/`unsafe`; imports; docstrings;
> non-vacuity examples). {SPECIFIC POINTS}. You may run Lean (one process at a time, scratch in
> `/tmp/opencode/review_{TAG}/`); edit no repository file. Final answer: counts per category; a
> findings table (item, verdict, problem, fix); confidence and limits.

## Lessons from the article (apply them up front)

- Summaries that drop hypotheses: if false as phrased (a real counterexample), `DISCREPANCY`
  (imprecision); otherwise `SAME_AS` with a note listing the implicit hypotheses. A witness that
  only shows convergence to a different minimizer does not refute a summary.
- `SAME_AS` must not point at a `DISCREPANCY` item; point at the parts that are true.
- "For every run" statements need an exhibited admissible run on that objective (non-vacuity);
  existing runs: `UnexcitedMetric.run` (u²+|v|), the |x| run in `Global.lean` (`absRun`),
  `fourMaxRun` in `Verification.lean`, the quadratic run in `Energy.lean`.
- Statements narrower or wider than the TeX are mismatches: state the paper's version (add a
  specialization when the Lean result is more general).
- Hessian convention: `(∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) ∧ DifferentiableAt ℝ (fderiv ℝ F) x`.
- The specified line search is `NonStrictLineSearch.fromMetric` for every trial budget N ≥ 5;
  "the run of the implementation" uses `implemented_run_unique`.
- Coverage modules cannot import each other; small helpers get duplicated under each namespace.

## Companion coverage agent (binding for every companion group)

The prompt names the files, registers, modules and group hints; this section is the
rest of the brief.

**Read first.** (1) `editorial/lean_coverage/README.md` (method, statuses, rules,
shared Lean forms). (2) "Lessons from the article" above. (3) The model
`bfgs_lean_article/BfgsArticle/Coverage/Article/MatrixAlgebra.lean` with
`register/A_matrix_algebra.json`, and the article coverage modules and registers
closest to your files (named in the prompt). (4) Your TeX files in full, plus
`companion/preamble.tex` (macros), the conventions of `companion/chapters/01_I.tex`
(for example the infinite-admissible-run convention) and whatever your files cite.
(5) Your registers; `lean_module` names your module (file
`bfgs_lean_article/BfgsArticle/Coverage/Companion/<Name>.lean`, namespace
`BfgsCoverage.Companion.<Name>`).

**Companion specifics.**
- The chapters are generated from a frozen corrected edition by
  `editorial/generate_companion.py`; never edit TeX. Each
  `% SOURCE_BEGIN X.span.k` … `% SOURCE_END X.span.k` block is a source span. The
  ledger records of your chapter, with each span's Lean exports, are in
  `editorial/lean_coverage/hints/<stem>.json` (run
  `python3 editorial/lean_coverage/companion_hints.py` first if the folder is
  missing; it is git-ignored derived data). An export list names the library
  theorems written for the span; it is a superset of what an item needs. Find exact
  statements in `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json` and read the
  library files. Corrections relative to the original report: `edits` of each span
  in `bfgs_lean_stage1/master_report/CLAIMS.json`, described in
  `bfgs_lean_stage1/master_report/edits/`.
- The companion asserts more in prose than the article. Itemize every sentence
  outside proofs that asserts a mathematical fact: results stated in prose (with or
  without a prose proof), standard facts (for example "a finite convex function has
  uniformly bounded subgradients on any compact set"), remarks, comparisons between
  results, table cells, captions. Inside proofs only displayed formulas are items.
  Literature results that a proof uses are proved in Lean (Mathlib may have them);
  literature only mentioned is `NON_CLAIM`.
- Sentences about the formalization, the audit or the history of the source are
  `NON_CLAIM` (software or history), but cover any mathematics they assert (for
  example "the original formula is false for t<0").
- A companion item that states exactly an article item's claim (up to notation) may
  be `SAME_AS` the article item (`A/...`), with a note on the notation; check the
  hypotheses word for word, since the companion keeps variants the article drops
  (noncompact, quantitative, other constants). Otherwise write a coverage theorem.
  Your module may import article coverage modules to reuse their results.
- Result headings (`kind: "heading"`, for example "Theorem 7.A") are named results.
- Open questions: a `def … : Prop` without proof, status `OPEN` (model:
  `BfgsCoverage.Article.Verification.C2StronglyConvexLocalFailure`).
- The article discrepancies M7–M11 (`TODO_MANUSCRIPT_REVIEW.md`) may recur in the
  companion; check the parallel passages.
- Aim for every item classified. `TODO` (with a reason) only for what you could not
  finish; say so in the final answer.

**Lean workflow.** `export PATH="$HOME/.elan/bin:$PATH"`; from `bfgs_lean_article/`:
`LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Companion/<Name>.lean`. At most
one Lean process at a time (several agents share the machine's memory); never
`lake build`, `lake update` or `lake clean`; scratch files in `/tmp/opencode/<tag>/`. Never
`native_decide`. Search names in `DECLARATION_INDEX.json` before proving anything
from scratch.

**Pause notes.** If `editorial/lean_coverage/pause_notes/<tag>.md` exists for your
group, read it right after this brief: an earlier agent did the reading for your files
and recorded its item plan and tentative decisions there. Continue from it, verifying
those decisions as you write the Lean statements. The note's instruction to wait for a
RESUME message is lifted: the prompt that sent you here is that message. Scratch files
the note mentions under `/tmp/opencode/<tag>/` are gone; recreate what you need from
the sources quoted in the note.

**Produce.** (1) Modules compiling with no errors and no warnings, no `sorry`, no
forbidden shortcuts; every named result exactly as in the TeX; each displayed claim
inside a proof under the standing assumptions at that point; definitions with
unfolding theorems; a non-vacuity `example`. (2) Registers filled: every item a
status and its fields, prose items added (`kind: "prose"`, `anchor`, `lines`, id
`C/<stem>/prose/<nnn>`). (3) Discrepancies: false, ambiguous or unprovable as written
→ `DISCREPANCY` with an entry (item, description, severity, proposed wording, Lean
statement of the corrected claim or a counterexample). Never weaken silently.
(4) `python3 editorial/lean_coverage/check_coverage.py --strict --allow-discrepancies
<your TeX files>` exits 0. Edit no other file; do not commit.

**Final answer.** Counts by status per file; each declaration with its item(s);
discrepancies; items not covered; substantial new proofs; check times; notes for
other agents.

## Companion groups (the group-specific part of each prompt)

Prompt header used for every companion group (fill the braces):

> You are working in the git repository {REPO}: a research article on BFGS for nonsmooth
> optimization (`paper/`), a long companion report (`companion/`), and a large Lean 4
> formalization (main library `bfgs_lean_stage1/BfgsVerification`, article package
> `bfgs_lean_article`). Goal: every mathematical claim of the article and the companion is
> stated by a Lean theorem ("literal Lean coverage"). The article is finished: 15 modules in
> `bfgs_lean_article/BfgsArticle/Coverage/Article/`, registers
> `editorial/lean_coverage/register/A_*.json`. You now cover {FILES}. Other agents cover
> other companion chapters at the same time.
>
> **Your brief.** Read `editorial/lean_coverage/AGENT_BRIEFS.md`, sections "Lessons from the
> article" and "Companion coverage agent" — they are binding and contain the method,
> workflow, deliverables and final-answer format. Then `editorial/lean_coverage/README.md`.
> {PAUSE NOTE: "Then your group's pause note `editorial/lean_coverage/pause_notes/<tag>.md`."}
>
> **Your files.** TeX, register(s), module(s) (file under
> `bfgs_lean_article/BfgsArticle/Coverage/Companion/`, namespace
> `BfgsCoverage.Companion.<Name>`), ledger hints `editorial/lean_coverage/hints/<stem>.json`,
> scratch `/tmp/opencode/<tag>/`.
>
> **Group hints (verify; not final).** {below}
>
> Do everything the brief says (modules, registers, discrepancies, checker exit 0), edit no
> other file, do not commit, and finish with the final answer the brief describes.

Wave 1 (started 14 October 2026, paused after the reading phase; pause notes exist):

- **compM** — `02_M.tex` (288 lines; 52 items), module `Ch02M`. Article: `Energy.lean`
  (`AdmissibleBFGSRun`, invariants, reference energy, art:minor-hierarchy,
  art:reciprocal-growth, band certificates), `MatrixAlgebra.lean`, `Local.lean`
  (localization). Library: `Localization`, `StrictContours`, `ObjectiveEnergy`,
  `SharpPotentialDegree`, `FoundationEndToEnd`, `PrincipalCombinatorialIdentity`,
  `hessianUpdate`, `hessianInvariants`, `strictContourSteps`,
  `convex_supporting_bound_on_compact`. Notation B_k = H_k⁻¹, q_k, d_k = α_kq_k, t_k, Δ_k,
  c = 1 − c₂; infinite-admissible-run convention (01_I). Prose claims such as bounded
  subgradients on compacts, ∑d_k < ∞. Check for parallels of M10.
- **compR** — `04_R.tex` (443 lines; 54 items), module `Ch04R`. Article: `Global.lean`
  (radial/inward conditions, art:centered, mixed benchmark), `PositivePartition.lean`,
  `Local.lean`. Library: `NuclearSymmetric2`, `NuclearRotatedPairs`,
  `CenteredRectangularNuclear`, `NuclearGram`, `PoweredGaugeRadial`, `AffineKinkAlgebra`.
  Check for parallels of M7 (containment of the compact sublevel).
- **compC** — `09_C.tex` (512 lines; 63 items), module `Ch09C`. Article:
  `PlanarGeometry.lean` (art:planar-field), `Local.lean` (planar cluster and maxima,
  polyhedral, nonradial example). Library: `PlanarQuadraticModel`,
  `PlanarTransportAlgebra`, `PlanarQuadraticPairs`, `PlanarScalarTransport`,
  `PlanarQuadraticCurve`, `PlanarJoinedFrame`.
- **compH** — `07_H.tex` (733 lines; 43 items), module `Ch07H`. Running text: Theorems
  7.A/7.B/7.C are `\subsection` headings (lines 47, 72, 106), "Lemma 7.3" bold text (~405);
  equations numbered by hand. Article: `Global.lean` (homogeneous theorems), `Energy.lean`.
  Theorem `M:average` comes from 02_M (state what is needed; no import of another companion
  module). Library: `EnergyIdentities`, `SeedRecurrentRank`, `HomogeneousBlockAlgebra`,
  `HomogeneousSourceConsequences`, `HomogeneousPotentialConsequences`, `BFGSUpdate`.
- **compD** — `12_D.tex` (502 lines; 62 items) and `appendices/seed_certificate.tex`
  (199 lines; 19 items), modules `Ch12D` and `SeedCertificate`. Article: `Failure.lean`,
  `NegativeUpper.lean`, article `SeedCertificate.lean`. The appendix is generated from the
  article's by `editorial/prepare_shared_appendix.py` (c_∘ → c, d_∘ → d, label renames,
  "Lemma art:seed_cycle" → "the seed and query assertions in Chapter D"): identical items
  are `SAME_AS` the `A/seed_certificate/...` items. M11: Chapter D fixes its constants
  (lines 52, 59, 204, 233); decide each seed/table/query statement and the appendix's closing
  sentence. Library: `DEmbeddingObjective`, `DScalarRamp`, `DScalarAssembly`,
  `AlgebraicSeedCycle`, `DScalarNegative`, `DDisplayPrecision`.
- **compL** — `13_L.tex` (417 lines; 52 items), module `Ch13L`. Article (import and reuse):
  `NegativeLower.lean`, `LowerCurvature.lean`; package `LUniformGlobal.lean`,
  `LUniformLocal.lean`; library `L*` modules. Chapter transformed on 13 October to state
  `L:thm:global`/`L:thm:local` for every pair 0 < c₁ ≤ 1/3, c₁ < c₂ < 1: check leftovers
  such as line 413 ("This chapter uses the fixed line-search pair…"). M8 recurs at line 3.
  φ_b (line 284) vs the article's ψ_b.

Wave 2 (not started):

- **compTA** — `03_T.tex` (249 lines; 30 items) and `08_A.tex` (139 lines; 16 items),
  modules `Ch03T`, `Ch08A`. Library (T): `ParabolicExampleSeparation`,
  `ParabolicExampleContrast`, `AffineCertificates`, `ComparisonEnergyWarning`,
  `TransportedCertificateVariants`, `ParabolicCertificate`; (A): `AffineBarycentricCoordinates`,
  `AffineBarycentricAlgebra`, `AffineDistanceFormula`, `AffineCriticalGeometry`,
  `AffineRankLossGeometry`, `FiniteMaxLocalCorrectness`. Article: `Energy.lean`,
  `Geometry.lean`, `Global.lean`, `Local.lean`.
- **compG** — `05_G.tex` (363 lines; 45 items), module `Ch05G`. Library:
  `ShiftedAbsAccessibility`, `AccessibleJumpGeometry`, `TransportedCertificateVariants`,
  `TransportedCertificateRun`, `TransportedCertificateConvergence`,
  `ReportContinuationEndToEnd`. Article: `Energy.lean` (band certificates), `Geometry.lean`,
  `Global.lean`.
- **compFQ** — `06_F.tex` (216 lines; 32 items) and `10_Q.tex` (324 lines; 45 items),
  modules `Ch06F`, `Ch10Q`. Library (F): `MaxAffineBasin`, `UnexcitedMetric`,
  `FivePieceObstruction`, `ScalarResidualFamilies`, `EuclideanResidualRadial`,
  `EuclideanResidualLineSearch`; (Q): `ParabolicEnvelopePruning`, `ParabolicEnvelopeOrdered`,
  `ParabolicEnvelopePrunedFamily`, `ParabolicExampleScale`, `ParabolicPairs`,
  `ReportFamiliesEndToEnd`. Article: `Local.lean` (run on u²+|v|, nonradial example),
  `Global.lean` (benchmarks), `Geometry.lean`.
- **compU** — `11_U.tex` (492 lines; 38 items; headings Theorem 11.1/11.2), module `Ch11U`.
  Library: `NormalSpikeBump`, `NormalSpikeSeries`, `NormalSpikeOracle`,
  `NormalSpikeRegularity`, `NormalSpikeRational`, `NormalSpikeGeometry`.

Wave 3 (after all chapters; maps to chapter items):

- **compFront** — `01_I.tex` (393 lines; 22 displays), `14_E.tex` (251 lines),
  `research_story.tex`, `current_verification.tex`, `correspondence.tex` (no mechanical
  items: all prose), modules `Ch01I`, `Ch14E`, `ResearchStory`, `CurrentVerification`,
  `Correspondence`. Mostly `SAME_AS` chapter items, plus `NON_CLAIM` for software, audit
  and history sentences. M8 recurs at `01_I.tex:103` and `research_story.tex:52`. Stale
  facts in `current_verification.tex` ("2026 Lean names"; the audit now checks 3862) are
  descriptions of software, to be refreshed when the manuscript is edited.
