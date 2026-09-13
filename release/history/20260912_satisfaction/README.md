# BFGS paper and complete companion — skeptical refinement

The article is **46 pages**, including essential proof appendices; the complete
companion is **107 pages**. Both positive convergence results and deterministic
local counterexamples remain central. The fresh skeptical pass tightened the
introductory hypotheses, removed repetition, clarified two proof deductions and
closed a literal formal correspondence point for actual branch regularity.
This is an author-review manuscript, not an approved submission.

Deliverables are `BFGS_Journal_Article.pdf`, `BFGS_Complete_Companion.pdf` and
`BFGS_paper_companion_sources.zip`. LaTeX entry points are `paper/master.tex`
and `companion/master.tex`. The prior editions and their receipts are preserved
in `history/20260912_initial/` and `history/20260912_narrative/`.

## Validated source freeze

The reviewed source commit is `573306b9fb4f4c66d7214b533b89380c28ceda66`,
committed and pushed after proof/prose milestone `7072ac0`. The source ZIP is
119,243,872 bytes in 4,327 members, with SHA-256
`64633451de2c70cb1b97af49abc5ac65a9d549460d4e597e100a88685403aaba`.
`RELEASE.json` and `SOURCE_MANIFEST.json` record its exact PDFs and source.

Fresh extraction validation passed in
`validation/runs/satisfaction_20260912_01/SUMMARY.json`. Both PDFs rebuilt
byte-identically; all 153 rendered pages and paginated text matched the reviewed
versions. References resolve and there are no overfull boxes. All four Lean
supplements freshly compiled and passed their full structural dependency and
axiom audits, with matching displayed theorem contracts and exact within-run
kernel type/proof-value agreement. Both cache-byte checks passed, with every
recorded ordered search path matching the sealed pinned paths. The current
21-check and unchanged historical-baseline gates passed. All 38 command
receipts and outputs are retained; the temporary extraction was removed.

The archive-only `_archive/RELEASE_SNAPSHOT.json` identifies the exact source
freeze. Committed prior archive/validation receipts inside it remain historical;
this new archive's hash and later validation receipt are external to that
immutable snapshot. This avoids a circular archive-hash or future-execution
claim. The validated release commit `0fcf64f2b40b41829711ec62ab8dee04ee78ac50`
was pushed successfully; `editorial/logs/satisfaction_release_push.json` records
the exact remote check. A later completion-receipt commit only records that
result and closes the status register; the source ZIP remains the fixed freeze.

The ZIP preserves the outer `BFGS-non-smooth/` folder and every committed
relative path. It includes sources, figures, current and historical PDFs,
complete correspondence, actual compiler/audit/review evidence and the Git
history bundle required by immutable historical checks. It excludes dependency
caches, compiled objects, raw `.git`, temporary build files and unrelated
untracked user files. The ZIP itself is ignored by Git; its manifest and the
release PDFs are committed. Its own hash is recorded externally after creation
to avoid a circular archive-hash claim.

## Reproduction

In a fresh extraction, restore history before changing or building files:

```bash
python3 _archive/restore_git_history.py
bash editorial/build.sh
python3 editorial/verify_release_inputs.py
python3 editorial/verify_historical_baseline.py --run-id local_replay
```

Omit the restore command in an existing Git checkout. Python 3, TeX Live,
latexmk/pdflatex and Poppler are required; the historical index check also uses
Node.js. The journal class is included with notices and provenance. Generated
companion sources are checked against frozen corrected-source hashes.

New Lean compilation requires the pinned toolchain and dependencies; follow
`bfgs_lean_stage1/README.md`. Once available, from the repository root run:

```bash
python3 editorial/formal_audit/run.py --run --run-dir editorial/formal_audit/runs/local_replay
python3 editorial/narrative_rebuild/positive_formal/verify.py --run-id local_replay
python3 editorial/narrative_rebuild/negative_formal/verify.py --run-id local_replay
python3 editorial/satisfaction_review/formal/verify.py --run-id local_replay
python3 editorial/satisfaction_review/branch_formal/verify.py --run-id local_replay
```

Use new run names; existing evidence is never overwritten. For the exact sealed
host cache, `editorial/satisfaction_review/cache_binding/README.md` gives the
read-only byte check. A legitimately rebuilt cache can have different bytes;
it needs its own new build/audit evidence rather than a claimed match to the
recorded host cache. The source integrity gate distinguishes retained evidence
from present-cache verification. Archive validation recompiles all four
supplements and performs their full structural audits in fresh output
directories, while reusing the separately checked pinned original libraries.
No empty-cache original-library or Mathlib rebuild is claimed.

## Proof and review scope

All 172 corrected source spans and 3,087 distinct full exports remain in the
companion. Exact hypotheses and proof support are recorded in
`editorial/CLAIM_LEDGER.json`, `companion/PROOF_CORRESPONDENCE.html` and the
original declaration index. All 31 article statement blocks are unchanged by
this refinement. The source/proof selection and supersession ledgers are
preserved. The current review is in `editorial/satisfaction_review/REVIEW_LOG.md`.
All 153 final pages have visual approval; unchanged companion pages are carried
forward only by exact pixel equality with actually inspected prior pages.

The pinned main incremental build/audit checks 9,781 safe declarations in the
main/correction union, including 7,954 theorems. Four supplemental audits check:
benchmark, 3 owned declarations/31,960 transitive declarations; covariance,
11/10,697; geometry, 14/26,496; actual branch regularity, 3/37,525. Counts overlap
and are not additive. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. The audits reject unfinished proof axioms, custom mathematical
axioms and reachable unsafe/partial declarations and compare exact root types
and proof values against the checked environment.

Cache binding additionally seals 8,853 objects, all paired sources and 32,470
cached files. Every available Lake object hash was independently recomputed.
The ordinary pinned build passed. The separate failed `--rehash` experiment
and upstream ProofWidgets metadata diagnosis remain explicit; it is not
reported as a successful build. Cached compiler artifacts and the execution
environment retain their stated trust role. Neither formal checking nor byte
hashing establishes foundational consistency, natural-language equivalence,
novelty or floating-point robustness.

The original public checker is unchanged. Its citation-only diff rule rejects
later editorial Lean additions; the wrapper records this expected failure,
checks 761 frozen inputs and 286 sealed artifacts, then replays the original
checker at its exact frozen baseline. Current document/supplement checks are
separate, without weakening historical policy.

## Human author actions

`editorial/AI_AND_AUTHOR_ACTIONS.md` reserves human mathematical/literature and
novelty review, accurate author metadata, consent, responsibility/declarations,
target/length decisions and any submission/deposit. The 46-page article exceeds
the original 30–35-page editorial aim to preserve the requested positive and
negative theorem set with complete proofs; `editorial/JOURNAL_FIT.md` documents
the exception and current policy. No acceptance, independent human peer review,
human approval, submission or public archival deposit is claimed.
