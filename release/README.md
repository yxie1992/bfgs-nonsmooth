# BFGS author-review release

The journal article is **32 pages**; the complete companion is **105 pages**.
This is an author-review-ready research package. Human approval, independent
peer review and journal acceptance are not claimed.

- `BFGS_Journal_Article.pdf`: article, including its essential proof appendices.
- `BFGS_Complete_Companion.pdf`: complete reorganized corrected report.
- `BFGS_paper_companion_sources.zip`: full source archive, 79,008,274 bytes.
- `SOURCE_MANIFEST.json`: source commit, archive/PDF hashes and file counts.
- `validation/SUMMARY.json`: actual fresh-extraction commands and results.

The archive preserves the outer `BFGS-non-smooth/` folder and every committed
repository-relative path. It contains 3,521 source files, final PDFs, a hash
manifest and the Git bundle required by immutable historical checks. Dependency
caches, compiled Lean objects, raw `.git`, temporary build files and unrelated
untracked user files are excluded. The ZIP is a local deliverable excluded from
Git; its manifest and final PDFs are committed.

The frozen source commit is
`7bcce9ae46cb2b3dffcffff218b60d233c45dc15`.
The subsequent release commit records the extraction results and final release
status; this keeps the source snapshot and its validation independently
traceable. The archive's editorial work-state files describe that source
milestone, before the extraction validation recorded here.

## Reproduction

In a fresh ZIP extraction, restore the bundled history **before** building or
editing, because the restore helper validates the original member hashes:

```bash
python3 _archive/restore_git_history.py
bash editorial/build.sh
python3 editorial/verify_release_inputs.py
python3 editorial/verify_historical_baseline.py
```

In an existing Git checkout omit the restore command. LaTeX sources start at
`paper/master.tex` and `companion/master.tex`. The build requires Python 3,
TeX Live with the supplied packages, latexmk/pdflatex and Poppler. Node.js is
also needed by the historical index check. The official journal class is
included unchanged with its provenance and notices.

The source ZIP was actually extracted into a new directory and rebuilt with no
preexisting document build outputs. Both PDFs were byte-identical, every one
of 137 rendered pages matched the previously visually inspected versions,
and paginated extracted text matched. References/citations resolved and there
were no overfull boxes. The temporary extraction was removed after the check;
commands, output and hashes remain under `validation/`.

## Formal scope and evidence

The pinned Lean 4.19.0 project received an actual incremental build and fresh
transitive declaration audits, with 9,781 safe declarations in the main and
correction union (7,954 theorems). The new article geometry audit checked 14
module-owned declarations and 26,496 recursively reached dependencies. Only
`propext`, `Classical.choice` and `Quot.sound` occur as axioms. The audits reject
unfinished proof axioms, custom mathematical axioms and reachable unsafe or
partial implementation artifacts. This is not a proof of foundational
consistency or a new empty-cache build of every dependency.

The historical public checker is unchanged. Its citation-only repository-wide
Git comparison rejects new editorial Lean files at later HEADs. The wrapper
preserves that expected failure, compares all 761 frozen audit inputs and 286
sealed artifacts, and replays all original checks at `00362c0`, where they pass.
Current article/companion integrity and supplemental Lean verification are
separate checks. The archive replay repeated both evidence-validation paths;
it did not represent them as a new Lean compilation.

Exact source/type/hypothesis correspondence and attribution are in
`editorial/CLAIM_LEDGER.json`, its component contract reviews,
`companion/PROOF_CORRESPONDENCE.html`, and `editorial/LITERATURE_LEDGER.json`.
All 172 corrected source spans and 3,087 distinct full exports are preserved.
Conditional hypotheses, definitions, interpretations and open questions are
classified separately. Formal checking does not certify prose translation,
novelty, bibliographic priority or floating-point behavior; the recorded
correspondence and literature reviews address those distinct scopes.

## Reserved author actions

Read `editorial/AI_AND_AUTHOR_ACTIONS.md`. Human authors must supply metadata,
review the cited sources and novelty statements, accept responsibility and the
substantive AI-use disclosure, and decide final submission or archival deposit.
No submission, public deposit or external message has been made by this task.
