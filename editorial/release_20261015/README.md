# `editorial/release_20261015/`: record directory of the October 2026 edition

This directory holds the records of the next author-review release, the October
2026 Lean-coverage and correction edition. It is named after the day the release
preparation started (15 October 2026); the freeze date is recorded here when the
sources are frozen. The plan of the release run is
`editorial/release_plan_20261015/PLAN.md` (D2 = R, D3 = H, D4 = the strict
correspondence revision, D5 = T1, D6 = T3, D7 = freeze only when
`check_coverage.py --strict` exits 0); its Phase 2 and its host are replaced by
"Run order" and "Release host" below. The open release checks C1–C18 are tracked
in `TODO_LEAN_REVIEW.md` ("Release receipts are now stale").

Contents now (release tooling, phase A and its fix pass, and step 4 of the run
order, by AI agents, Claude in OpenCode):

| File | Role |
|---|---|
| `refresh_correspondence.py` | The October correspondence revision (T4): `--snapshot`, `--propose`, `--write`, `--check` |
| `prior_mapping/` | Byte copies of the baseline commit `3e8b5c6`, with `MANIFEST.json` (SHA-256 of each file) |
| `CHANGES.json` | The reviewed table of changes: 77 rows, one per changed unit (step 4 of "Run order") |
| `mapping_refresh.json` | The receipt of `--write` |
| `T4_REVIEW.md` | The independent review of the 77 rows and its fix pass |
| `TOOLING_REVIEW.md` | The independent review of the release tooling and its fix pass |
| `README.md` | This file |

Written by the run (after step 4): the release records, as in
`editorial/scientific_exposition_20260913/`: `REVIEW_LOG.md`, `WORKLOG.md`, the
visual review records, `release_integrity.log`, `package.log`,
`archive_validation.log`, `final_receipt_review.json`, `source_push.json`,
`final_push.json`.

## The October correspondence revision

The three component reviews (`editorial/positive_contract_review.json`,
`negative_contract_review.json`, `root_contract_review.json`) map every named
statement, labeled display, proof passage and prose deduction of the article to
its source spans and Lean contracts; `editorial/assemble_claim_ledger.py` builds
the claim ledger from them. Their file hashes, locations and proof passages date
from the 13 September release. That release's check,
`editorial/scientific_exposition_20260913/refresh_correspondence.py --check`,
rejects every statement change, so it cannot follow the October corrections; it
stays unchanged and is replayed at its own release commit `3e8b5c6`
(`editorial/verify_historical_correspondence.py`, T2). This revision takes over
its current role. Every difference in a checked unit (list below), including the
complete text of the two appendices that the 13 September revision preserved,
must be listed; text outside the units (prose outside root and deduction
passages, unmapped tables and figures and the files they `\input`, headings) is
bound only by the receipt's file hashes, so it needs `--write` but no row.

**Baseline.** Commit `3e8b5c6` (13 September release freeze). `prior_mapping/`
holds the three reviews, the 13 September receipt, the 18 active article TeX
inputs and the two companion files of the root review (`research_story.tex`,
`chapters/13_L.tex`), 24 files, created by `--snapshot` from the commit's blobs.
Every run checks them against `MANIFEST.json` and against `git show 3e8b5c6:…`
(files as git sees them: an ignored `.DS_Store` is not an extra file), and checks
that the 13 September receipt names exactly these reviews as its outputs and the
two appendices of `appendix:` below as its complete-text files. It then
recomputes the reviews from the baseline TeX and requires the result to equal
the baseline reviews byte for byte: the extraction is the one the 13 September
revision reviewed.

**Units.** Each is compared with the baseline after removing whitespace, except
where whitespace separates TeX tokens: one space that ends a control word before
a letter (`\le q` is not `\leq`) and a control space (`a\ b` is not `a\b`) are
kept. There are no notation aliases. A unit found in another file than at the
baseline is a change (`moved`).

| Key | Unit |
|---|---|
| `statement:<label>` | theorem, lemma, proposition, corollary or definition |
| `display:<label>` | labeled `equation`, `align` or `gather` |
| `float:<label>` | a table or figure, caption included, whose label a negative or positive review row maps |
| `algorithm:line_search` | the line-search algorithm block of Section 6 |
| `proof:<label>` | the proof environment of a named statement (positive statements; negative proof environments) |
| `passage:<role>` | a negative-review proof passage between two anchors |
| `root:<id>` | the passage at the anchor of a root-review record |
| `deduction:<n>` | the passage at the anchor of the n-th positive unnumbered deduction |
| `appendix:<path>` | the complete text of `paper/appendices/lower_curvature.tex` and `seed_certificate.tex` (the 13 September receipt's `complete_appendix_notation_preservation`) |
| `macro:<name>` | a macro definition (`\newcommand`, `\renewcommand`, `\providecommand`, `\DeclareMathOperator`, `\def`) in an active input |

A passage at an anchor runs to the end of its paragraph: the first blank line, the
end of the enclosing environment or the next anchor of another record in the same
file. A `\label{…}` anchor stands for its environment; a labeled display, table or
figure with a unit of its own stands for that unit. An edit inside an appendix is
listed twice, as its own unit and as the `appendix:` unit.

**`CHANGES.json`** is `{"schema_version": 1, "revision": "release_20261015",
"baseline_commit": "3e8b5c6…", "changes": [...]}`, one row per changed unit:

    {"id": "C001", "kind": "statement", "key": "art:quadratic_failure",
     "file": "paper/appendices/lower_curvature.tex", "change": "changed",
     "before_sha256": "<normalized baseline text>", "after_sha256": "<current>",
     "correction_items": ["M33"],
     "coverage": [{"item": "A/lower_curvature/proposition/art:quadratic_failure",
                   "status": "LEAN", "sha256": "<current item hash>"}],
     "principal_lean": ["BfgsCoverage.Article.LowerCurvature.quadratic_failure"],
     "review": "One reviewed sentence."}

- `change` is `changed`, `added`, `removed` (displays), `moved` (same text in
  another file; the row gives the earlier file in `before_file`), or `anchor` (an
  anchor rewritten around unchanged text). A changed anchor is given as
  `"anchor": {"old": …, "new": …}` (`"end_anchor"` for the end of a passage); the
  new anchor must occur exactly once. A root row may also give a new
  `scope_review`, which replaces the record's (the old one stays in the baseline).
- `correction_items`: `M<n>` or `W<n>` of `TODO_MANUSCRIPT_REVIEW.md`, or
  `"TODO_LEAN_REVIEW.md: <item title>"` for a change made by the Lean review.
- `coverage`: register items with a final status (not `DISCREPANCY`, not `TODO`) and
  their current hash: for mechanical items the register's `sha256`, which must
  equal the item's current hash; for prose items the hash of their lines, whose
  text must contain the item's anchor. Every cited item lies in the changed unit;
  when register items cover the changed lines, at least one of them is cited; a
  statement, display, table/figure or proof row cites the unit's own register
  item. A `macro:` row cites no register item.
- `principal_lean`: names from the `lean` fields of the cited items or of the items
  they reach through `of`; the axiom audit checks every such name.

**Assertions** (`--write` and `--check`): the snapshot and baseline checks above;
the active TeX inputs are those of the baseline; the statement and display label
sets are unchanged except for listed additions and removals; every unit equals the
baseline, in the same file, except for the listed changes; every row matches
exactly one current change, hashes and earlier file included (a further edit
makes the row stale); every anchor resolves exactly once; the retained evidence
of the 13 September revision (`supplemental_cache_binding` and the rest of its
immutable list), every field the revision does not refresh, and every
unrefreshed field of every row are byte-identical to the baseline; the 13
September component-phase export checks still hold. It recomputes statement
bodies, locations, proof passages (start and end lines, passage hashes) and the
article file hashes, adds an `october_correspondence_revision` block to each
review and an `october_revision_changes` list (row ids) to each touched row. The
receipt `mapping_refresh.json` records the inputs, every preserved and every
listed unit with raw before/after hashes, the verified coverage items, the
retained evidence, the output hashes, and the hashes of `verify_release_inputs.py`,
`assemble_claim_ledger.py`, `active_tex_sources.py` and `extract_items.py`.
`--check` recomputes everything and compares bytes. It builds nothing and runs no
Lean; it needs git history.

**Limits, by design** (the independent row review covers them):

- Text outside every unit (above) needs no row. Examples: the caption and the
  drawing (`paper/figures/gradient_geometry.tex`) of Figure `art:gradient-geometry`,
  section headings, prose between root passages. Review such edits in `git diff
  3e8b5c6` together with the rows.
- Correction items are checked for existence only, not for relevance;
  `--propose` prints the TODO text of every cited item (`correction_item_texts`).
- `TODO_LEAN_REVIEW.md: <title>` is matched against the bold item titles of that
  file: keep a cited title unchanged (closing the item with `[x]` is fine;
  rewording its title makes `--check` fail).
- Refused with an explicit message, and needing an extension of this revision: a
  named statement added or removed, an active TeX input added or removed, a
  proof passage of the negative review moved to another file, a numbered display
  without `\label` (as in September).

**Use, once the sources are final** (see "Run order", step 4):

    python3 editorial/release_20261015/refresh_correspondence.py --propose > $S/propose.json
    # review each proposed row against `git diff 3e8b5c6` and the registers; fill in
    # correction_items, coverage, principal_lean and review; add the rows to CHANGES.json
    python3 editorial/release_20261015/refresh_correspondence.py --write
    (cd editorial && python3 assemble_claim_ledger.py)
    python3 editorial/release_20261015/refresh_correspondence.py --check

`--propose` prints JSON: `uncovered` holds row skeletons (with suggested register
items and Lean names, and empty `correction_items` and `review`), `hints` the old
and new text, a word diff, the changed lines and the candidate register items,
and `correction_item_texts` the TODO text of every cited correction item;
`stale_rows`, `rows_without_a_current_change` and `unresolved_anchors` report rows
to fix. For a lost anchor it proposes a row with `"anchor": {"old": …, "new": ""}`:
fill in the new anchor and run `--propose` again for the hashes. A whitespace-only
edit needs no row, only `--write`. A stale row (its text changed again after the
review) is proposed again under its own id, with its correction items and its
previous review in `hints`, for a new review. The receipt pins the hashes of the TeX
inputs, of `CHANGES.json`, of `verify_release_inputs.py` and
`assemble_claim_ledger.py`, and of the helpers `active_tex_sources.py` and
`extract_items.py`, so run `--write` after every change to them. An independent
reviewer agent then checks every row (plan, T4), including a negative test with an
unlisted edit in a scratch copy.

In the scratch test of the fix pass (HEAD `d066071`), `--propose` found 27 changes
since `3e8b5c6`: statements `art:local-failure-lower`, `art:lower_hyperbolic`,
`art:quadratic_failure`, `art:seed_cycle`; four displays; tables
`art:regularity-map` and `art:trial_table`; six proofs; three negative proof
passages; six root passages (two of them in `research_story.tex`); both
appendices. The article corrections M30–M41 will add more. The table of step 4,
for the sources at `5b5c273`, lists 77 changes; its independent review and fix
pass are `T4_REVIEW.md`.

## Release host

The archive validation and the release workspace need the sealed Lean host cache
of the September checkout H (`/Users/yxie/Documents/ChatGPT/BFGS-non-smooth`,
`bfgs_lean_stage1/.lake` and `.toolchain`, sealed by `cache_binding_04`). Linking
H itself lets every run write into it outside the seal: elan appends to
`.toolchain/elan/known-projects`, and `git status` in the dependency checkouts
refreshes their index files. The release therefore uses an APFS clone of H's cache,
outside the macOS temporary directory (which macOS may purge):

    D=<freeze date>; H=/Users/yxie/Documents/ChatGPT/BFGS-non-smooth
    HOST=/Users/yxie/Projects/release_host_$D/bfgs_lean_stage1
    mkdir -p $HOST
    cp -cR $H/bfgs_lean_stage1/.lake $HOST/.lake             # copy-on-write: seconds, no extra disk
    cp -cR $H/bfgs_lean_stage1/.toolchain $HOST/.toolchain
    # once, in a clone of R whose bfgs_lean_stage1/.lake and .toolchain link to $HOST:
    python3 editorial/satisfaction_review/cache_binding.py --check \
      --manifest editorial/satisfaction_review/cache_binding/runs/cache_binding_04/MANIFEST.json --root $PWD
    # expect "status": "PASS", "object_count": 8853, "sealed_cache_file_count": 32470

The release workspace W links `bfgs_lean_stage1/.lake` and `.toolchain` to
`$HOST`, never to H. Run `validate_archive.py` from W without `--lean-cache-root`:
its default host is W's own `bfgs_lean_stage1`, whose frozen sources, Lake files
and dependency checkouts it compares with the extraction, and it links the
extraction's `.lake` and `.toolchain` to the targets of W's links, the copy. Do not
pass `--lean-cache-root $HOST`: that option expects a complete `bfgs_lean_stage1`
directory (sources, Lake files and caches), and the copy holds only `.lake` and
`.toolchain`. Never run `lake` in `$HOST`. Delete `$HOST` after the release; that
does not touch H.

## Run order

This replaces Phase 2 of `editorial/release_plan_20261015/PLAN.md` §6, from the
independent review (finding MF5). It keeps the October Lean evidence bound (T3)
from the moment it is written: T3 binds the Lean files, Lake configurations,
`bfgs_lean_article/scripts`, the claim ledger and the coverage registers to the
audited commit, and the ledger copies the package signatures from
`AXIOM_AUDIT.json`. Phases 3–4 of the plan stay as they are, with W linked to the
release host above.

1. **Tooling and ledger code first.** Commit the release tooling (it changes
   `verify_release_inputs.py`, which T4 pins). SF6 of the review is done by the
   coordinator before T4's `--write`: `editorial/coverage_index.py` records the
   real provenance of each signature, and `editorial/assemble_claim_ledger.py`
   carries a record's `october_revision_changes` and the receipt into the ledger.
   Every other change to `assemble_claim_ledger.py` also comes before step 4.
2. **D1 (edition date).** `paper/master.tex` l. 29 is in the preamble (no unit,
   no register item: only `--write` later); `companion/master.tex` and
   `companion/preamble.tex` have no register. Build both PDFs and inspect.
3. **Register notes.** Rewrite the notes of `A/introduction/prose/049`,
   `A/verification/prose/027` and `C/current_verification/prose/004` so that they
   stay true at commits A–C, without counts or a state that changes between A and
   C (for example: the release records are refreshed by each release run and
   `release/RELEASE.json` names the edition they describe; the axiom audit and the
   kernel replay are `bfgs_lean_article/AXIOM_AUDIT.json` and `KERNEL_REPLAY.json`,
   bound to the sources by `verify_release_inputs.py`). `check_coverage.py --strict`.
4. **T4.** `--propose`; fill and review the rows; `--write`;
   `assemble_claim_ledger.py`; `--check`.
5. **Printed counts.** Compute the counts the evidence will have, without Lean,
   with the scripts' own collection (as T3 does):

       cd bfgs_lean_article && python3 - <<'EOF'
       import sys; sys.dont_write_bytecode = True; sys.path.insert(0, 'scripts')
       import axiom_audit as a, kernel_replay as k
       principal, article, companion, private = a.ledger_names(); coverage = a.coverage_names()
       print('names', len(set(article) | set(companion) | set(coverage) | set(a.PACKAGE_PRINCIPAL)))
       modules = k.project_modules(); names = sorted(modules)
       prefixes = {m for m in names if any(o.startswith(m + '.') for o in names)}
       only = [m for m in prefixes if all(l.startswith('import ') for l in k.code_lines(modules[m]))]
       print('modules', len(names) - len(only))
       EOF

   Write them and the planned audit date into `companion/current_verification.tex`
   ("checked <N> Lean names", "(<M> modules;", the wording T3 checks) **without
   changing its line structure** (`CurrentVerification.lean` cites its line
   numbers). Build, inspect; `check_coverage.py --strict` (no resync expected).
   Commit 2.
6. **Lean evidence on commit 2** (clean tree; no agent running Lean): `lake build`;
   axiom audit with `--write-guard` (if `BfgsArticleAxioms.lean` changes: commit,
   `lake build`, audit again); kernel replay; copy both reports;
   `assemble_claim_ledger.py`. If the ledger changed (new package signatures),
   commit it and re-run only the axiom audit (the replay binds only Lean files,
   Lake configurations and scripts), copy, re-run the assembler (now unchanged).
   Check that the reports' counts and date equal what step 5 wrote (T3 checks the
   counts); if not, fix the TeX in place (no line shift), no re-run needed.
   Commit 3.
7. **Frozen from here on:** no edit to Lean files, Lake configurations,
   `bfgs_lean_article/scripts`, the ledger, the registers or T4's inputs.
   `TODO_LEAN_REVIEW.md` may be edited, but keep the bold titles that a
   `CHANGES.json` row cites.

Then the plan's Phase 3 (workspace W with the links to the release host, freeze
commit A) and Phase 4 (packaging, validation, commits B and C).

## Release tooling T1–T5 and the checks C1–C18

| Change | Script | Checks |
|---|---|---|
| T1 | `editorial/verify_historical_baseline.py`: added (status `A`) paths under `bfgs_lean_article/` are allowed besides the added editorial Lean files, with the reasons recorded; relative to the citation baseline every path in these scopes is new, so the September editorial Lean files are required unchanged since `3e8b5c6` and the package is bound by T3; a modified, deleted or renamed Lean path of the main library still fails; the diff is read with `-z`; SUMMARY lists the allowed scopes and the diff entries per scope | C4 |
| T2 | `editorial/validate_archive.py`: `04_historical_correspondence` (new `editorial/verify_historical_correspondence.py`: the unchanged 13 September check at `3e8b5c6`, PASS required; its script and inputs unchanged at HEAD, compared as git sees them; its result at HEAD recorded; an existing run directory fails cleanly; run directory copied), `04_current_correspondence` (T4 `--check`), `04_coverage_register` (`check_coverage.py --strict`); SUMMARY scope updated | C1, C2, C11, C12 |
| T3 | `editorial/verify_release_inputs.py`: "October Lean evidence bound to the frozen sources" (reports PASS on a clean tree with the pinned Lean and lean4checker tag; audited commit an ancestor of HEAD; Lean files, Lake configurations, `bfgs_lean_article/scripts`, ledger and registers unchanged since; counts recomputed from the sources by the scripts' own functions; counts stated in `companion/current_verification.tex`; a malformed report is a recorded FAIL) and "Lean coverage register strict check"; 23 checks | C11, C12 |
| T4 | `editorial/release_20261015/refresh_correspondence.py` and this directory | C2, C3 |
| T5 | `editorial/package_release.py`: the archive's `AUTHOR_REVIEW_README.md` gives the correspondence checks and the `bfgs_lean_article` commands (build, axiom audit, kernel replay, coverage check) and what the release gate checks of the recorded reports | C16 |

Every existing check is kept. The 13 September correspondence check no longer runs
at the current commit inside the archive validation (by design it fails there); it
runs unchanged at its release commit, its result at the current commit is
recorded, and its role passes to T4, which keeps its statement, display,
algorithm and complete-appendix assertions (without notation aliases) and adds
tables and figures, proofs and anchored passages. C5 and C6 are handled by the
workspace: W's `.lake` and `.toolchain` link to the APFS clone of the sealed
September host ("Release host"), never to H; no tooling change. C7–C9 pass
unchanged. C10 and C13–C18 are steps of the run.

Until step 4 of the run order, `refresh_correspondence.py --check` fails (no
receipt; the changes are not listed yet), and so do `04_current_correspondence`
and the three "Reviewed source contracts" checks of `verify_release_inputs.py`;
until step 6, so does "October Lean evidence bound to the frozen sources" (until
then the committed reports described `9f03d7c`, whose counts are no longer those
of the sources): expected. Steps 4 to 6 were done on 15 October 2026: the table
of changes and its receipt are committed, and the reports describe `2cfa27a`.
