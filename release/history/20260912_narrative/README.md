# BFGS narrative-rebuild author-review release

The revised article is **47 pages**, including its essential proof appendices;
the complete companion is **107 pages**. The article gives coequal weight to
deterministic counterexamples, global/local convergence families and the actual
BFGS matrix/energy mechanism. The literal `u^2+|v|` whole-sequence result is a
named corollary. The nonradial planar application has a complete article proof.
This is an author-review edition, not an approved submission.

Deliverables: `BFGS_Journal_Article.pdf`, `BFGS_Complete_Companion.pdf`, and
`BFGS_paper_companion_sources.zip`. The previous edition is preserved in
`history/20260912_initial/`. The handoff response is
`editorial/narrative_rebuild/narrative_response.md`.

## Source freeze and validation receipts

The source commit is `252ea5dd5a0dccc9301da4132f98c539f1e2393c`.
The ZIP is 96,721,994 bytes in 3,778 members, with SHA256
`9f34ef3c91096958bd59e812de001a878f44be441541b097359ec5714c47b99f`.
Current PDF and archive hashes are in `RELEASE.json` and `SOURCE_MANIFEST.json`.

Fresh extraction validation passed in
`validation/runs/narrative_20260912_01/SUMMARY.json`. Both PDFs rebuilt
byte-identically; all 154 rendered pages and paginated text matched the reviewed
versions, with resolved references and no overfull boxes. Both new Lean
supplements were freshly compiled and structurally audited in the extraction,
with the same exact types and dependency counts. The current and historical
evidence gates passed, and temporary extraction files were removed. All 34
commands and their output remain in the versioned validation directory.

The ZIP contains the earlier committed source-freeze state. Its
`_archive/RELEASE_SNAPSHOT.json` identifies that snapshot; any committed
`SOURCE_MANIFEST.json` inside it describes a prior package, explicitly labeled
as such. The external receipt here records this ZIP's hash and later validation
without a circular archive-hash claim. All prior validation runs are preserved.

The ZIP preserves the outer `BFGS-non-smooth/` folder and every committed
relative path. It includes the Git history bundle required by historical
checks, sources, exact correspondence, compiler/audit evidence, figures and
PDFs. Dependency caches, compiled Lean objects, raw `.git`, temporary build
files and unrelated untracked user files are excluded. The local ZIP is
ignored by Git; its manifest and release PDFs are committed.

## Reproduction

In a fresh ZIP extraction restore history before changing or building files:

```bash
python3 _archive/restore_git_history.py
bash editorial/build.sh
python3 editorial/verify_release_inputs.py
python3 editorial/verify_historical_baseline.py --run-id local_replay
```

In an existing Git checkout omit the restore command. LaTeX entry points are
`paper/master.tex` and `companion/master.tex`. The build uses Python 3, TeX Live,
latexmk/pdflatex and Poppler; Node.js is needed by the historical index check.
The official journal class is included with its notices and provenance.
Source generation checks all frozen corrected-source hashes.

For new Lean compilation, run `bash scripts/bootstrap.sh` inside
`bfgs_lean_stage1`, then run from the repository root:

```bash
python3 editorial/formal_audit/run.py --run --run-dir editorial/formal_audit/runs/local_replay
python3 editorial/narrative_rebuild/positive_formal/verify.py --run-id local_replay
python3 editorial/narrative_rebuild/negative_formal/verify.py --run-id local_replay
```

Use new run names for repeat execution; evidence directories are not overwritten.
The source-only integrity gate checks retained evidence and reports omitted
compiled caches as such. It does not execute Lean. The release validator also
compiles the new supplements and performs their full structural audits in a
fresh extraction, reusing explicitly checked pinned host libraries. This is
not an empty-cache rebuild of those libraries.

## Mathematical and formal scope

All 172 corrected source spans and 3,087 distinct full exports remain in the
companion. Exact statements, definitions, hypotheses and transitive support
are exposed in `editorial/CLAIM_LEDGER.json`, its component reviews,
`companion/PROOF_CORRESPONDENCE.html` and the original declaration index.
Article selection changes are in
`editorial/narrative_rebuild/ARTICLE_DISPOSITIONS.json`.

The fresh pinned main replay checked 9,781 safe declarations in the main and
correction union, including 7,954 theorems. The preceding fourteen article
geometry declarations retain unchanged audited sources. The new benchmark
supplement has three module-owned theorems and 31,960 checked transitive
dependencies; matched scaling has eleven declarations and 10,697 dependencies.
Counts overlap and are not additive. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted as axioms; unfinished proof axioms, custom
mathematical axioms and reachable unsafe/partial artifacts are rejected.
Formal verification does not certify foundational consistency, natural-language
correspondence, novelty or floating-point behavior.

The historical public checker is unchanged. Its repository-wide citation-only
diff rejects added editorial Lean files at later commits. The wrapper preserves
that expected failure, checks 761 frozen inputs and 286 sealed artifacts, and
replays the original checks at the frozen baseline. Current document and
supplemental verification remain separate checks.

## Human author actions

See `editorial/AI_AND_AUTHOR_ACTIONS.md`. Authors must review the mathematics,
literature and novelty statements, approve the substantive AI-use disclosure,
supply accurate metadata and declarations, and decide the target/length and any
submission or public deposit. The 47-page article exceeds the original 30–35-page
editorial aim to retain the requested broad positive results and complete
proofs; `editorial/JOURNAL_FIT.md` records the rationale and policy. No acceptance,
human approval, independent human peer review, submission, public deposit or
external message is claimed.
