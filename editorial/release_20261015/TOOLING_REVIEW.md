# Independent review of the release tooling (phase A), and its fix pass

Independent review of the phase-A release tooling (T1–T5: `editorial/verify_historical_baseline.py`,
`validate_archive.py`, `verify_historical_correspondence.py`, `verify_release_inputs.py`,
`package_release.py`, `editorial/release_20261015/`) by Claude in OpenCode, an AI agent, on 15 October 2026,
on scratch clones of commit `d066071`. The review text below is unchanged (`$S/...` and `./` paths in it are
scratch directories of the reviewer, which are not kept). The fix pass, by the agent that wrote the tooling, is the
last section.

---

# Independent review of the release tooling, phase A

Reviewer: Claude (OpenCode subagent), 15 October 2026, 06:23–07:15 PDT. Brief:
`$S/prompts/review_tooling.md`. `S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode`; everything below
is in `$S/review_tooling/` (written `./`). R = `/Users/yxie/Projects/bfgs-nonsmooth` (HEAD `d066071`), H = the September
checkout. Nothing in R or H was edited; no git command that changes R or H was run; git queries of H used
`GIT_OPTIONAL_LOCKS=0`. At most one Lean process ran at a time (only inside the one archive validation); no
`lake build/update/clean/exe`.

## Verdict: sound with fixes

The architecture is right and most of it works: T1 and T2 do what the plan says, T3 binds the evidence correctly
for every source change I tried, T5's text is accurate, and a full packaging + archive validation of a scratch freeze
passes end to end against an APFS clone of the September host (41 commands, 23/23 release-input checks including both
T3 checks, H untouched). But T4, which takes over the September correspondence check's current role, is weaker than
that check in two places and accepts unrelated coverage citations, its whitespace normalization hides a real meaning
change inside a proof, and several texts claim more than is checked. The release order of the plan also breaks the T3
binding unless three register notes and the counts printed in `companion/current_verification.tex` are finalized
before the Lean evidence commit. Tested patches for T1, T3 and T4 are in `./fixes/`.

**Must fix before phase B**

| # | Where | Problem (test) | Fix (tested) |
|---|---|---|---|
| MF1 | T4 `refresh_correspondence.py` `unit_specs`/`detect` (l. 305–346, 505–530) | Two 13 September assertions are no longer made at the current commit: the complete text of `lower_curvature.tex` and `seed_certificate.tex`, and statement placement per file. A prose edit in either appendix (A10, A10b) and a definition or a corollary with its proof moved to another file (A5, A5b) pass with `--write` alone; the September script at `3e8b5c6` rejects both (`Appendix changed beyond reviewed notation`, `Statement label set changed`). | Units `appendix:<path>` for the two files of the September receipt's `complete_appendix_notation_preservation`; change type `moved` (+ row field `before_file`) when a unit's file differs (`fixes/t4_fix.diff`) |
| MF2 | T4 `verify_row` (l. 682–702) | Coverage citations need not concern the change: overlap is tested against the whole unit, not the changed lines (A1: passage row citing `prose/030` [313–317] for a change at 294–295 passes); extra items of other files or of the companion are accepted and may supply the principal Lean names (A2: `statement:art:seed_cycle` citing `C/13_L/theorem/L:thm:global` and `…Ch13L.global_failure` passes). README l. 93 and FINAL_REPORT claim "must overlap the changed text". | Every cited item must lie in the unit; when register items touch the changed lines one of them must be cited; statement/display/float/proof rows must cite the unit's own register item |
| MF3 | T4 `norm` (l. 179–180) | Removing all whitespace merges a control word with the next letters: `$(g_k^Tv)^2\le q_kv^TB_kv$` → `$(g_k^Tv)^2\leq_kv^TB_kv$` (q_k dropped) inside `proof:art:run-invariants` normalizes to the same text; passes with `--write` alone (A8). | Keep one space that ends a control word before a letter |
| MF4 | texts in R | Claims beyond the checks: README l. 40 "with the same strictness: nothing changes unless it is listed"; l. 93 (overlap); l. 162–165 "Every existing check is kept … its role passes to T4"; T1 docstring l. 16–17 "every modified, deleted or renamed Lean path still fails the wrapper" (false: a renamed or deleted September editorial Lean file passes T1, tests `renamed_editorial_lean`, `deleted_editorial_lean`; any file under `bfgs_lean_article/` is "added" relative to the citation baseline). | Reword (exact text below); with MF1–MF3, SF4, SF5 most claims become true; state the remaining out-of-scope text (prose outside units, unmapped floats and figure drawings, headings) |
| MF5 | plan §6 Phase 2–3, `release_20261015/README.md` "What remains" | Sequence: T3 binds `editorial/CLAIM_LEDGER.json` and the registers to the audited commit, but (a) the ledger copies package signatures from `AXIOM_AUDIT.json`, (b) register notes `A/introduction/prose/049`, `A/verification/prose/027` say "currently out of date … (5403 names …, 783 modules)" and `C/current_verification/prose/004` quotes the 15 October counts — all in the ledger's `lean_coverage_records` — and (c) `companion/current_verification.tex` prints 5403 / 783 / "15 October", while the current sources already cite 5417 names. Editing any of these after commit 3 fails T3 at validation; not editing them ships false notes and counts. | Order in "Sequence" below; SF3 makes the counts machine-checked |

**Should fix**: SF1 T3 accepts partial or foreign reports (N22 partial replay, N23 partial audit, N24 wrong
lean4checker tag) and does not bind the audit/replay scripts (N11); SF2 T3 crashes instead of recording FAIL on
malformed report shapes (N19–N21); SF3 no check that the companion states the bound counts; SF4 T1 does not bind the
September editorial Lean files (11 of the 33 are bound by no release check before the October audit commit); SF5 T4
ignores macro definitions (A9: `\newcommand{\R}{\mathbb Q}` passes with `--write`); SF6 the ledger does not carry the
October row ids and mislabels the source of package signatures (outside the six paths); SF7 use an APFS clone of H as
the release host. **Optional**: OP1–OP9 below.

## Integrity of the reviewed files, H and the host copy

- sha256 of the 33 files in the six paths recorded at 06:23 (`sha256_start.txt`) and at the end (`sha256_end.txt`):
  identical (see the last section). The copies in clone `a` were byte-identical (`sha256_clone_a.txt`).
- **APFS copy of the host cache works and is the better host.** `cp -cR $H/bfgs_lean_stage1/.lake` (10.7 s) and
  `.toolchain` (0.7 s) into `./host/bfgs_lean_stage1/` (copy-on-write: disk usage unchanged, 251 GiB before and after;
  one relative symlink inside, no absolute path into H; `settings.toml` has no overrides). With a clone linked to the
  copy, `cache_binding.py --check --manifest …/cache_binding_04/MANIFEST.json`: **PASS, 8853 objects, 32470 files**
  (9.0 s, `cache_check_apfs_copy_1.json`); again before (`e_cache_before.json`) and after (`e_cache_after.json`) the
  full validation: PASS 8853/32470. The validation's elan write went to the copy's `known-projects` (last line now
  `…/review_tooling/e/…/archive-replay-req2enfb/…`), and the dependency `git status` index refreshes happened in the
  copy.
- **H was never linked.** H state with `GIT_OPTIONAL_LOCKS=0` (HEAD, `status --short`, sha256 and line count of
  `.toolchain/elan/known-projects`, mtimes of H, `bfgs_lean_stage1`, `elan`, `known-projects`, `.git`, `.git/index`,
  `.lake`, the nine `.lake/packages/*/.git` and their `index`): `H_state_before.txt` (06:32),
  `H_state_after_copy.txt`, `H_state_after_validation.txt` (06:51): identical. H's `known-projects` (7 lines,
  `264e0c41…`) still holds the three lines the tooling agent's runs appended (`…/tooling/{dry,final,final2}/…`).
  H's untracked files (`"… 2.md"` copies, `audit/scratch/`, `tmp/`, a release JSON) predate this review.

## Findings in detail

### MF1 — T4 drops two September assertions (regression)

`editorial/scientific_exposition_20260913/refresh_correspondence.py` l. 145–153 compares statement label sets per
file, and l. 174–177 requires the complete text of `paper/appendices/lower_curvature.tex` and
`paper/appendices/seed_certificate.tex` to equal the baseline (its receipt's `complete_appendix_notation_preservation`).
T2 replays that script only at `3e8b5c6`; T4 (`unit_specs`, l. 305–346; `detect`, l. 505–530) compares units keyed by
label, ignores the file, and has no whole-file unit. Tests (clone `b`, provisional table, `t4_adversarial.py`, log
`t4_adversarial.log`; each case: edit, `--check`, `--write`, `--check`):

| Case | Original T4 | Sept script at `3e8b5c6` |
|---|---|---|
| A10 `lower_curvature.tex` l. 5 "positive quadratic" → "negative quadratic" | `--check` stale only; `--write` PASS; `--check` PASS | `AssertionError: ('Appendix changed beyond reviewed notation', 'paper/appendices/lower_curvature.tex')` |
| A10b first " the " → " a " in `seed_certificate.tex` | PASS after `--write` | (same assertion) |
| A5 Definition `art:band-certificate` moved verbatim from `energy.tex` to the end of `global.tex` | PASS after `--write` | `AssertionError: ('Statement label set changed', 'paper/sections/energy.tex')` |
| A5b Corollary `art:planar-convergence` and its proof moved from `local.tex` to `global.tex` | PASS after `--write` | (per-file label sets) |

Fix (in `fixes/t4_fix.diff`, file `fixes/refresh_correspondence.py`):

```python
COMPLETE_FILES = ['paper/appendices/lower_curvature.tex', 'paper/appendices/seed_certificate.tex']
KINDS = [..., 'deduction', 'appendix', 'macro']
CHANGE_TYPES = {'changed', 'added', 'removed', 'anchor', 'moved'}
ROW_FIELDS = {..., 'scope_review', 'before_file'}
# unit_specs(), after the algorithm unit:
    for path in COMPLETE_FILES:
        add('appendix:' + path, {'type': 'file', 'file': path})
# compute_units(), new branch:
        elif spec['type'] == 'file':
            text = tree.read(spec['file'])
            units[key] = {'file': spec['file'], 'start': 0, 'end': len(text), 'text': text}
# detect(): between 'changed' and 'anchor'
            elif old['file'] != new['file']:
                change = 'moved'
# ... and after found[key] = {...}:
        if old and new and old['file'] != new['file']:
            found[key]['before_file'] = old['file']
# verify_row(): compare 'before_file' too, with row.get()/detected.get()
# build(): require COMPLETE_FILES == the paths of the Sept receipt's complete_appendix_notation_preservation
# receipt: 'complete_file_preservation': preserved('appendix:')
```

With the patch, `--propose` at `d066071` lists 27 changes (the 25 of the original plus `appendix:` rows for both
appendices, which the corrections M1/M6 changed); A5, A5b, A10, A10b fail (`t4_adversarial_patched_v3.log`).
Alternative if double-listing is unwanted: an `appendix:` unit of the text outside all other units of the file.

### MF2 — coverage citations unrelated to the change

`verify_row` l. 694–699 requires only that *some* cited item overlap the unit's lines; l. 684–693 accept any further
item of any register, and l. 700–702 accept principal Lean names reachable from any cited item. Tests:

- A1: row of `passage:all_query_copy_induction_and_one_fixed_identity_normalization` (unit 281–331, changed lines
  294–295) cites only `A/lower_curvature/prose/030` [313–317] and its names: `--write` PASS, `--check` PASS.
- A2: row of `statement:art:seed_cycle` adds `C/13_L/theorem/L:thm:global` (companion) and sets `principal_lean` to
  `BfgsCoverage.Companion.Ch13L.global_failure`: PASS.

Fix (replaces l. 694–699; `verify_row` and `match_rows` get `base_units`):

```python
    if row['change'] != 'removed' and row['kind'] != 'macro':
        require(coverage, ('A change row needs at least one coverage register item', row['id']))
        unit = cur_units[key]
        first, last = unit['lines']
        for c in coverage:
            require(c['file'] == unit['file'] and c['lines'][0] <= last and first <= c['lines'][1],
                    ('Cited coverage item lies outside the changed unit', row['id'], c['item'], unit['file'], unit['lines']))
        old = base_units.get(key)
        changed = changed_lines(old, unit) if old and row['change'] == 'changed' else set(range(first, last + 1))
        touched = {i['id'] for i in registers.candidates(unit)
                   if any(i['lines'][0] <= n <= i['lines'][1] for n in changed)}
        require(not touched or any(c['item'] in touched for c in coverage),
                ('No cited coverage item overlaps the changed lines', row['id'], sorted(changed)[:12], sorted(touched)))
        if row['kind'] in {'statement', 'display', 'float', 'proof'}:
            own = [i['id'] for i in registers.candidates(unit) if i['kind'] != 'prose' and i['lines'] == unit['lines']]
            require(not own or any(c['item'] in own for c in coverage),
                    ('The register item of the changed unit is not cited', row['id'], own))
```

The `touched` condition matters: line 32 of `geometry.tex` ("The right panel asks a different question:") lies in no
register item, and a stricter rule broke the tooling agent's scenario A. With the rule above, A1 and A2 fail; the
--propose suggestions satisfy it (provisional table of 27 rows passes); the tooling agent's 18 negative tests and 13
scenarios pass (`c_t4_negative_v3.log`, `c_t4_scenarios_v3.log`). This also gives the plan's "status LEAN": for a
statement, the unit's own item carries the statement's status (any final status is still accepted for prose rows,
which is right: root passages contain NON_CLAIM sentences).

### MF3 — whitespace normalization hides a control-word merge

`norm` (l. 179–180) is the September core (`re.sub(r'\s+', '', …)`) without the aliases and without the
`\quad`/`\qquad` removal (both stricter than September). Dropping a space after a control word can turn two tokens into
another macro: A8 replaced `$(g_k^Tv)^2\le q_kv^TB_kv$` by `$(g_k^Tv)^2\leq_kv^TB_kv$` in the proof of
`art:run-invariants` (`energy.tex` l. 70; the factor q_k disappears and "≤" gets a subscript): normalized texts are
equal, `--check` reports only stale bytes, `--write` passes. `a b` vs `ab` in math mode is harmless; in text mode it is
a visible typo. Fix:

```python
def norm(text):
    """Remove whitespace, except one space that ends a control word before a letter (\\le q is not \\leq)."""
    text = re.sub(r'(\\[A-Za-z]+)\s+(?=[A-Za-z])', lambda m: m.group(1) + '\x00', text)
    return re.sub(r'\s+', '', text).replace('\x00', ' ')
```

No change at `d066071` becomes newly visible through it (the 25 detected changes are the same). A8 fails with the patch.
(Corner case left: `\ ` control space; OP8.)

### MF4 — texts that claim more than is checked

Replace in `editorial/release_20261015/README.md`:

- l. 39–40 "This revision takes over its current role, with the same strictness: nothing changes unless it is
  listed." → "This revision takes over its current role. Every difference in a checked unit (list below) must be
  listed; text outside the units (prose outside root and deduction passages, unmapped tables and figures and the
  files they `\input`, headings) is bound only by the receipt's file hashes, so it needs `--write` but no row."
  (After MF1 add: "and the complete text of the two appendices the 13 September revision preserved".)
- l. 93–94 → "Every cited item lies in the changed unit; when register items cover the changed lines, at least one
  of them is cited; a statement, display, table/figure or proof row cites the unit's own register item." (after MF2).
- l. 162–165 → "Every existing check is kept. The 13 September correspondence check no longer runs at the current
  commit … its role passes to T4, which keeps its statement, display, algorithm and complete-appendix assertions
  (without notation aliases) and adds tables/figures, proofs and anchored passages." (true only after MF1).
- `verify_historical_baseline.py` l. 16–17 "and every modified, deleted or renamed Lean path still fails the wrapper"
  → "relative to the citation baseline every path in these scopes is new, so the wrapper cannot see later edits
  there: the September editorial Lean files are required unchanged since the September release `3e8b5c6` (SF4), and
  the October package is bound by `verify_release_inputs.py` (T3). A modified, deleted or renamed Lean path of the
  main library still fails." Same correction for the T1 row of the README table and for FINAL_REPORT wording reused in
  `RELEASE.json`/`release/README.md`.
- `validate_archive.py` l. 84 and docstring l. 9: "(its failure at the current commit recorded)" → "(its result at the
  current commit recorded)": `PASS_AT_CURRENT_COMMIT` is possible (tested at `3e8b5c6`, OP5).

### MF5 — sequence of the run versus the T3 binding

Facts (checked at `d066071`):

- `editorial/ledger_addenda.py` puts `AXIOM_AUDIT.json`'s `package_declarations` into the ledger's index;
  `coverage_index.py` copies their signatures into `lean_coverage_declarations` (10 package names). A new audit whose
  signatures differ changes the ledger.
- The ledger's `lean_coverage_records` contain each item's `note`: `A/introduction/prose/049` and
  `A/verification/prose/027` say "currently out of date … release records … predate the October revisions; the ledger
  proof_locations … for lower_curvature.tex are stale; … the axiom audit of that day (5403 names …) and the kernel
  replay (783 modules …)"; `C/current_verification/prose/004` quotes the 15 October text with 5403/783. After the run
  the first two notes are false and the third is history.
- `companion/current_verification.tex` l. 8–11 print "The axiom audit of 15 October 2026 checked 5403 Lean names" and
  "(783 modules;": the current ledger and registers already cite **5417** names (audit's own collection, recomputed:
  coverage names 3222 vs 3208 in the report); the module closure is still 785/783. Its register prose items carry no
  hash and their anchors do not contain the numbers, so an in-place edit without line shift changes neither register
  nor ledger; a line shift does (and `CurrentVerification.lean` l. 44 cites `current_verification.tex:46-47`, so a
  shift before l. 46 also forces a Lean docstring edit, i.e. a new audit **and** replay).
- T3 binds for the audit: `*.lean`, toolchain, lakefiles, manifests, the ledger, the registers; for the replay only the
  Lean paths. T4's receipt pins the TeX inputs, `CHANGES.json`, `verify_release_inputs.py`, `assemble_claim_ledger.py`,
  `active_tex_sources.py`, `extract_items.py`, the script and the manifest (all confirmed: A16, every pinned file edited
  → `--check` fails).
- `editorial/build.sh` on the scratch freeze regenerated chapters, shared appendix, `SOURCE_CORRESPONDENCE.json`,
  ledger, HTML and figures byte-identically; only `paper_build.log` (and, in another directory, `companion_build.log`,
  `document_checks.json`) changed. `render_review.py` writes only unbound files.

Proposed order (replaces plan §6 Phase 2; Phases 3–4 unchanged):

1. Commit the tooling fixes first (they change `verify_release_inputs.py`, which T4 pins, and
   `bfgs_lean_article/scripts` stays bound by the patched T3). Any change to `assemble_claim_ledger.py` (e.g. SF6) also
   before step 3.
2. D1 (edition date): `paper/master.tex` l. 29 is in the preamble, no unit, no register item → only `--write` later;
   `companion/master.tex`, `preamble.tex` have no register. Build, inspect.
3. Register notes: rewrite the three notes so that they are true at commits A–C without naming counts or a state that
   changes between A and C (e.g. "The release records are refreshed by each release run; `release/RELEASE.json` names
   the edition they describe; the axiom audit and kernel replay are `bfgs_lean_article/AXIOM_AUDIT.json` and
   `KERNEL_REPLAY.json`, bound to the sources by `verify_release_inputs.py`"). `check_coverage.py --strict`.
4. T4 `--propose`, fill and review rows, `--write`; `assemble_claim_ledger.py`; T4 `--check`.
5. Compute the evidence counts without Lean (the patched T3's `expected_audit()` / `expected_replay()`, or the
   scripts' `ledger_names()`, `coverage_names()`, `PACKAGE_PRINCIPAL`, `project_modules()`), and write them and the
   planned audit date into `companion/current_verification.tex` **without changing its line structure**; build,
   inspect; `check_coverage.py --strict` (no resync expected). Commit 2.
6. Lean evidence on commit 2 (clean tree): `lake build`; axiom audit `--write-guard` (if `BfgsArticleAxioms.lean`
   changes: commit, `lake build`, audit again); kernel replay; copy both reports; `assemble_claim_ledger.py`. If the
   ledger changed (new package signatures): commit it and re-run **only the axiom audit** (the replay binds Lean paths
   only), copy, re-run the assembler (now unchanged). Check that the reports' counts and date equal what step 5 wrote
   (patched T3 checks the counts); if not, fix the TeX in place (no line shift) — no re-run needed. Commit 3.
7. From here on, no edit to Lean files, lakefiles, the ledger, the registers or T4's inputs. `TODO_LEAN_REVIEW.md`
   may be edited, but keep the bold titles a CHANGES row cites (A17: rewording a cited title fails `--check`; closing
   with `[x]` does not).

## Should fix and optional, in detail

**SF1 — T3 accepts partial or foreign evidence** (`verify_release_inputs.py` l. 391–433). Tests in clone `d`
(`t3_tests.py`; evidence relabeled in scratch as audits of a scratch commit `X`, log `t3_tests.log`, `t3_tests_2.log`):
N22 `modules_replayed: 1, modules_in_closure: 3` → PASS; N23 `declarations_checked: 1` → PASS; N24 checker tag
`v4.9.0` → PASS; N11 `bfgs_lean_article/scripts/axiom_audit.py` changed and committed after the audit → PASS (scripts
not bound). Fix (`fixes/t3_fix.diff`, tested): bind `bfgs_lean_article/scripts`; recompute with the scripts' own
functions (no Lean) and compare `declarations_checked`, the four `ledger_*`/`coverage_register_names` counts,
`private_names_not_referable`, and `modules_in_closure`, `modules_replayed`, `imports_only_modules_not_replayed`,
`modules_by_root`; require `checker.tag == 'v' + pinned`. With the patch the relabeled real report of `9f03d7c` fails
honestly (`declarations_checked [5403, 5417]`, `coverage_register_names [3208, 3222]`); with counts set to the
recomputed values (scratch) P0 passes and N1–N27 fail (`t3_tests_patched.log`, `t3_tests_patched_2.log`). Update the
T3 docstring (l. 4–13) to name the scripts and the recount.

**SF2 — T3 crashes on malformed shapes.** N19 report is `[]`, N20 `checker` is a string, N21 `lean_version` null:
uncaught `AttributeError`, exit 1, no `release_integrity.json`, the other 22 results lost. Fix: l. 432
`except (KeyError,TypeError,ValueError,OSError) as error:` → `except Exception as error:` and record
`type(error).__name__+': '+str(error)` (tested: recorded FAIL).

**SF3 — printed counts unchecked.** N27: nothing compares `companion/current_verification.tex` with the bound reports.
Fix (in `t3_fix.diff`, inside the T3(a) try): require `'checked <declarations_checked> Lean names'` and
`'(<modules_replayed> modules;'` in the whitespace-normalized text (tested: an in-place edit back to 5403 fails with
"does not state the counts of the bound reports"). Wording changes then need the check updated (fail-closed). The date
("of 15 October 2026") stays a manual check.

**SF4 — T1 does not bind the September editorial Lean files.** The citation baseline predates them, so a rename
(`R100`) or deletion of `editorial/**/*.lean` passes the wrapper (tests `renamed_editorial_lean`,
`deleted_editorial_lean`: PASS, diff count 33→32 only recorded); an added `editorial/reviewer_extra.lean` passes (the
September scope). 11 of the 33 files (`editorial/formal_audit/runs/2026091*/scope_sources/*.lean`,
`cache_binding_03/ObjectHashCheck.lean`) are bound by no `verify_release_inputs.py` hash and by T3 only from the
October audit commit on. Fix (`fixes/t1_fix.diff`, tested: positive PASS, rename → `FAIL Editorial Lean files changed
since the 13 September release: R100 …`):

```python
SEPTEMBER_RELEASE = '3e8b5c6ff5f4ef663718c74776ecc78ca3527db4'
# in main(), after summary['current_global_lean_diff'] = changed:
        git('cat-file', '-e', SEPTEMBER_RELEASE + '^{commit}', label='08b_september_release_history')
        since_september = git('diff', '--name-status', SEPTEMBER_RELEASE, current_commit, '--', 'editorial/*.lean',
                              label='08c_editorial_lean_since_september_release')
        require(not since_september, 'Editorial Lean files changed since the 13 September release: '
                + since_september[:400])
        summary['editorial_lean_unchanged_since_september_release'] = SEPTEMBER_RELEASE
```

**SF5 — macro definitions.** A9: `\newcommand{\R}{\mathbb R}` → `{\mathbb Q}` in `paper/master.tex` passes with
`--write` (every statement using `\R` changes meaning). Fix (in `t4_fix.diff`, tested: A9 → `Unlisted change
macro:\R`): `macro:<name>` units for `\newcommand`, `\renewcommand`, `\providecommand`, `\DeclareMathOperator`, `\def`
in every active input (definition to end of line, extended while its braces are open; 10 definitions at
`d066071`, none changed since `3e8b5c6`); macro rows need correction items and a review, no register item. D1's
`\date` line is not a macro, so D1 still needs only `--write`.

**SF6 — ledger records (outside the six paths; coordinator's files).** (a) `assemble_claim_ledger.py` copies
specific review fields; the October row ids (`october_revision_changes`) and the receipt are not carried, so
`CLAIM_LEDGER.json`/`PROOF_CORRESPONDENCE.html` show only the September review status
("reviewed_against_corrected_source_and_exact_formal_contracts") for the four changed statements. Fix: in l. 39, 41,
43, 82 add `'october_revision':{'changes':row['october_revision_changes'],'receipt':'editorial/release_20261015/mapping_refresh.json'}`
when present (before T4 `--write`, which pins the assembler). (b) `coverage_index.py` l. 96–98 labels every signature
found in the assembler's merged index with source `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json`, but 24 of
the 1495 so labeled at `d066071` are not in that file (supplement declarations from `editorial/…/declarations.json`, and
package declarations copied from `AXIOM_AUDIT.json` by `ledger_addenda`), e.g.
`ArticleBranchRegularity.branch_not_twice_differentiable_zero`: record the real provenance.

**SF7 — host.** Plan D2/D3 and README l. 166 link H itself; linked runs write H's `known-projects` and refresh index
files in H's dependency checkouts (tooling agent's report). An APFS clone (`cp -cR`, 11 s, no space) passes the same
binding check and absorbed all writes in my full validation. Put it outside `T/` (macOS may purge it), e.g.
`/Users/yxie/Projects/release_host_$D/bfgs_lean_stage1/{.lake,.toolchain}`, run the binding check once on it, and link
W's `bfgs_lean_stage1/.lake` and `.toolchain` to the copy.

**Optional**

- OP1 `.DS_Store` (ignored by git) inside `scientific_exposition_20260913/prior_mapping/` fails T2 ("The working tree
  changes the historical correspondence script or its inputs", test `ignored_DS_Store`; it also broke my
  `PASS_AT_CURRENT_COMMIT` test until removed), and inside `release_20261015/prior_mapping/` fails T4's file-set check.
  Fail-closed; filter `.DS_Store` or compare only `git ls-files` + untracked-not-ignored files.
- OP2 T2: an existing run directory raises `FileExistsError` before the `try` (exit 1, traceback, no SUMMARY; test
  `existing_run`). Move `run.mkdir` into a checked message.
- OP3 T4 out of scope by design: unmapped figures (A11: caption of `art:gradient-geometry` "excludes zero" → "contains
  zero"; A11b: `figures/gradient_geometry.tex`, which R's working tree changes now), headings, prose outside root and
  deduction passages, and `\input` files inside float units pass with `--write`. Document (MF4); optionally inline
  `\input` targets into float units and make every labeled float a unit.
- OP4 T4 cites `TODO_LEAN_REVIEW.md: <title>` by substring: keep titles stable (A17).
- OP5 validate_archive scope wording (MF4 last item).
- OP6 T5 `package_release.py` l. 227–230: "checks that no Lean file, Lake configuration, claim ledger or coverage
  register changed since that commit" → add "(for the kernel replay: Lean files and Lake configuration)"; mention that
  on macOS 26 lean4checker is built with the system linker (HANDOFF).
- OP7 T1 uses `git diff --name-status` without `-z`: a non-ASCII path is quoted (`"bfgs_lean_article/\303\244.lean"`) and
  rejected (false failure, fail-closed).
- OP8 T4 `norm`: `\ ` (control space) followed by letters can still merge; replace `\\ ` by a placeholder too.
- OP9 Correction items are checked for existence only (A4: `W1` on `statement:art:seed_cycle` passes): the independent
  row review must check relevance; `--propose` could print each cited item's TODO text.

## Answers to the brief's points

**1. Diffs line by line.** T1 (`+40/−3`): `ADDED_LEAN_SCOPES`, `added_scope` (exact first-component match; status `A`
only; prefix tricks `bfgs_lean_article_x/`, `bfgs_lean_article.lean`, `Editorial/`, `paper/x.lean`, main-library
additions, `M/D/T/R100` all rejected — unit test of 19 cases), new message, SUMMARY scopes; every September assertion
kept; fail-closed (all git errors raise). Gap: SF4, text MF4. T2 wrapper: requires `3e8b5c6` in history and as ancestor,
`git diff --quiet` of script, `prior_mapping`, N-reviews, receipt and `active_tex_sources.py`, byte equality of working
tree and worktree (catches uncommitted and untracked changes), exact PASS line at `3e8b5c6`, clean worktree after, HEAD
failure only as an `AssertionError` of the script; fail-closed except OP1/OP2. validate_archive: the old conditional
`04_focused_correspondence` (`if focused.is_file()`) is replaced by three unconditional steps; run directory copied;
SUMMARY fields and asserts added; everything else unchanged (diff confined to docstring, scope text and l. 307–327).
T3: 21 checks unchanged, two appended; fail-closed except SF2; gaps SF1, SF3. T4: as specified except the plan's
"coverage item with status LEAN" (MF2 fixes it for statements) and MF1–MF3, SF5. T5: template only, packaging
unchanged; text true (OP6).

**2. Adversarial tests.** T1: 9 end-to-end cases + 19-case unit test (`t1_t2_tests.log`): positive PASS 14 s;
`bfgs_lean_article_x/Foo.lean`, `bfgs_lean_article.lean`, `paper/x.lean` FAIL (7 s, new message); modified
`BfgsVerification.lean` FAIL at the frozen inputs; renamed or deleted editorial Lean PASS (SF4); added editorial Lean PASS
(September scope); modified package file PASS (by design: always "added" vs the citation baseline; T3 binds it). T2:
positive PASS 2 s; committed script change, committed `active_tex_sources.py` change → FAIL "changed after the release
commit"; uncommitted `MANIFEST.json` change, untracked extra input → FAIL "working tree changes"; stale work directory
→ FAIL "File exists"; existing run id → exit 1 traceback (OP2); `.DS_Store` → FAIL (OP1); `python3 -O` refused (T1 and
T2). **`PASS_AT_CURRENT_COMMIT`** (branch at `3e8b5c6` + wrapper): PASS, recorded with the PASS line; safe, because
`04_current_correspondence` (T4 `--check`) runs unconditionally after it and at an October HEAD the September check
cannot pass (its receipt names the September review bytes). **What `04_focused_correspondence` checked and where it is
now:** snapshot manifest (→ T2 at `3e8b5c6`, inputs unchanged at HEAD); no new active input (→ T4); statement label sets
per file, kinds, bodies modulo aliases (→ T4 bodies without aliases, label set global: MF1); labeled displays, no
removal, exactly three new labels (→ T4 rows); algorithm (→ T4); **complete text of the two appendices (→ nowhere: MF1)**;
N2/N3/N4 signatures against the declaration index (→ rows byte-identical by `assert_bounded`, index and CLAIMS frozen
by `BASELINE.json` and the sealed manifest: equivalent); root anchors (→ T4, stronger: passages compared); immutable
subtrees (→ T4); component-phase exports (→ T4 `assert_exports`); byte-equal outputs with active-input, N-review and
checker hashes (→ T4 receipt; N-reviews by T2). T3: 31 cases (P0, N1–N27 with N3b, N4b, N4c; above). T4: the
agent's 18 negative tests pass on my freeze (`b_t4_negative.log`); my 27 scripted cases (`t4_adversarial.log`) and two
manual ones: false passes A1, A2, A5, A5b, A8, A9, A10, A10b; by
design A4, A11, A11b, headings; correct FAIL for label rename (A7), mapped figure caption (A13), table
`art:positive-outcomes` cell (root unit), edits in proofs, statements, algorithm; A6 (display `art:local-l1-decomposition`
moved to `global.tex`) and A12 (display edit) were caught only through the surrounding deduction passage and statement
— a labeled display moved alone to another file is not detected by the original T4 (nor by September), and is by the
patch (`moved`); determinism (A15: committed bytes =
first `--write` = second `--write`, `--check` PASS, tree clean); all ten pinned inputs → stale (A16);
`prior_mapping/MANIFEST.json` equals `git show 3e8b5c6:` blobs for all 24 files, no extra file, canonical encoding.
Scope: 18 active article TeX files + `research_story.tex` + `13_L.tex`; every key of the three reviews'
`article_sha256`/`article_file_sha256` (7 + 5 + 7 files) is inside it. Companion chapters other than `13_L.tex` are
outside T4 and covered by `generate_companion.py --check` and the registers.

**3. Honesty.** See MF4 and OP5/OP6. True as written: T3's scope sentences ("bound … by git history; not re-run
here"), T2's SUMMARY scope, T5's README (it says the archive validation does not compile the package),
`HISTORICAL_FIELDS` in the receipt.

**4. Sequence.** See MF5 and the proposed order. Summary: after commit 3, D1 must already be done (it only needs
`--write`); T4 `--write` and the ledger regeneration come before the evidence; the counts in
`current_verification.tex` are predictable and go in before the evidence, without line shifts; the three register
notes must be rewritten before commit 2; if the new audit changes package signatures, commit the ledger and re-run the
axiom audit only; `build.sh` in Phase 3 reproduces chapters, shared appendix and ledger byte for byte (verified on the
scratch freeze); `render_review.py` touches nothing bound.

**5. Robustness.** Standard library only (`tomllib` is in the scripts T3 patch imports; 3.11+). `python3.11` parses
all six scripts; T4 `--check`/`--propose`, the T2 wrapper and `verify_release_inputs.py` (23/23) ran under 3.11.
Clone in a directory with a space, run from `/`: T4 `--check` PASS, T2 PASS, T1 PASS (13.8 s). `verify_release_inputs.py`
from `/`: 23/23. `python3 -O`: T1, T2, T4, validate_archive, package_release refuse; `verify_release_inputs.py` has no
`assert` (unaffected).

**6. Full validation** (clone `e` = `…/e/BFGS-non-smooth`, scratch freeze `c23eee9`: provisional T4 table, ledger,
build logs, release PDFs, render manifest, freeze-shape `RELEASE.json`, AXIOM/KERNEL reports relabeled in scratch as
audits of `aceec20` so that T3 can pass — a simulation, not evidence). APFS copy linked. `cache_binding --check` PASS
(06:48). `verify_release_inputs.py` pre-flight **23/23 PASS**, `current_cache_bytes_verified: true` (9.4 s).
`package_release.py` PASS 18.4 s, 159,342,536 B, 4965 members. `validate_archive.py --run-id rev_01` **PASS in 2 min 20 s,
41 commands**: documents byte- and pixel-identical (49 + 108 pages), `04_companion_preservation`,
`04_historical_correspondence` (PASS at `3e8b5c6`, HEAD failure `('Existing mathematical display changed',
'paper/sections/global.tex', 'art:inward-to-radial')` recorded, 31 unchanged input files), `04_current_correspondence`,
`04_coverage_register` exit 0; four supplements PASS (3, 11, 14, 3 module-owned declarations); cache before/after PASS;
**`09_release_inputs` 23/23 inside the extraction**, including "October Lean evidence bound" (restored history is
enough for the ancestry and diff checks; the extraction's untracked `.lake`/`.toolchain` links and run directories do
not match the Lean pathspecs) and the cache check with bytes verified; historical gate PASS; extraction removed,
`release/work/` empty. Cache check after: PASS. H unchanged.

## Tests run (commands from the clone root unless noted; times on this MacBook)

| Test | Command / script | Result | Time |
|---|---|---|---|
| T4 empty table at `d066071` | `python3 editorial/release_20261015/refresh_correspondence.py --check` | exit 1 `Unlisted change display:art:inward-to-radial` (expected) | 0.5 s |
| T4 propose | `--propose` | 25 uncovered (23 of the agent + `root:companion.story.negative`/`.positive`) | 0.5 s |
| provisional freeze (clone b) | `fill_provisional.py`, `--write`, `assemble_claim_ledger.py`, `--check` | PASS (27 statements, 51 displays unchanged; 25 rows); scratch commit `e537d10` | 1 s |
| agent's negatives | `bash t4_negative_tests.sh` | 18/18 | — |
| my T4 cases | `python3 t4_adversarial.py` | see MF1–MF3, SF5, OP3 | 30 s |
| Sept script at `3e8b5c6` (worktree) | A10 and A5 edits, `--check` | both AssertionError | — |
| patched T4 (clone c) | propose/fill/write/check; negatives; scenarios; my cases | PASS; 18/18; 13/13; A1, A2, A5, A5b, A8, A9, A10, A10b FAIL | — |
| T1/T2 | `bash t1_t2_tests.sh` | as in point 2 | 1 min 44 s |
| T1 patch | `fixes/t1_fix.diff` positive / rename | PASS / FAIL | 14 s / 8 s |
| T2 at `3e8b5c6` | wrapper copied onto a branch at `3e8b5c6` | PASS, `PASS_AT_CURRENT_COMMIT` | 2 s |
| T3 original (clone d) | `python3 t3_tests.py` (after `build.sh`, 5.8 s) | P0 PASS; FAIL N1–N10, N12–N18, N25, N26; PASS N3b (ignored dir), N11, N22, N23, N24, N27; crash N19–N21 | 31 s + 32 s |
| T3 patched | `T3_FULL=1 python3 t3_tests.py` | P0 PASS; all N FAIL (N3b PASS by design); TeX count mismatch FAIL | ≈ 1 min |
| full validation | build, render, vri, package, validate (clone e) | PASS (point 6) | 4 min |
| APFS copy + binding | `cp -cR`; `cache_binding.py --check` ×3 | PASS 8853/32470 | 11 s + 3 × 9 s |
| 3.11, spaces, cwd, -O | point 5 | all as expected | — |

Scratch layout: `a/` (tooling as in R, `b278a26`), `b/` (provisional T4 table), `c/` (patched T4), `d/` (T3 tests,
patched T3 at `acc4700`), `e/` (full validation, `release/validation/runs/rev_01/`), `space dir/`, `host/` (APFS copy of
H's cache, ~7.4 GB logical, copy-on-write), `fixes/` (patched files and diffs), logs and JSON results at the top level.
Delete `host/` when done (it shares blocks with H; deleting it does not touch H).

## sha256 check of the six paths

Recorded at 06:23 (`sha256_start.txt`, 33 files) and at 07:11 (`sha256_end.txt`): **identical, 33 files**; no file
was added to `editorial/release_20261015/` (no `mapping_refresh.json` in R). H state at the end (`H_state_end.txt`)
equals the state before (06:32). No scratch clone keeps a git worktree; `e/…/release/work/` is empty.

---

## Fix pass

By the agent that wrote the tooling (Claude in OpenCode), 15 October 2026, 07:20–07:55, on scratch clones of
`d066071` with the six paths as placed in the repository. The reviewer's tested patches (`fixes/`) were applied
unchanged and extended where noted. Tests: the tooling agent's 18 negative tests and 13 scenarios, the reviewer's
`t4_adversarial.py`, `t1_t2_tests.sh` and `t3_tests.py`, six new fix-pass tests (`t4_fix_extra_tests.sh`), and one full
packaging and archive validation against an APFS copy of the September host cache (results below; scratch logs not
kept).

| Finding | Change (file, function) | Test that shows it |
|---|---|---|
| MF1 | `refresh_correspondence.py`: `COMPLETE_FILES`; `unit_specs` adds `appendix:<path>` units, `compute_units` reads them (`'file'`); `detect` classifies `moved` and records `before_file`; `verify_row` compares `before_file`; `build` requires `COMPLETE_FILES` = the 13 September receipt's `complete_appendix_notation_preservation`; receipt `complete_file_preservation`; `refresh` also puts the paths of positive statements and proofs into `article_files` (a listed move) | A5, A5b, A10, A10b fail (`--check` and `--write`); a labeled display moved alone to another file is proposed as `moved` with its earlier file; `--propose` at `d066071` lists 27 changes (both appendices included) |
| MF2 | `refresh_correspondence.py`: `verify_row` (every cited item lies in the changed unit; when register items cover the changed lines, one of them is cited; statement, display, float and proof rows cite the unit's own item); `match_rows` and `propose` pass `base_units` | A1, A2 fail; the 27-row provisional table from `--propose` passes; 18/18 negative tests, 13/13 scenarios |
| MF3, OP8 | `refresh_correspondence.py`: `norm` with `CONTROL`: one pass over control sequences keeps a space that ends a control word before a letter and a control space (`\ `, backslash-newline); a control symbol such as `\\` is read first | A8 fails; unit test: 4 pairs kept apart (`\le q`/`\leq`, `a\ b`/`a\b`, backslash-newline, `\alpha b`/`\alphab`), 7 pairs identified (reflow, `\\ x`/`\\x`, `\alpha }`, `\alpha 1`, `\quad`, `\,`) |
| MF4, OP5 | Texts: `release_20261015/README.md` (role paragraph, coverage rule, the paragraph "Every existing check is kept …", the T1 row), `verify_historical_baseline.py` docstring, `validate_archive.py` docstring and SUMMARY scope ("its result at the current commit recorded"), `refresh_correspondence.py` docstring (units, normalization, coverage rule, what needs no row); the tooling agent's FINAL_REPORT corrected in its fix-pass section | The claims now hold: renamed, deleted and added editorial Lean files fail T1 (`t1_t2_tests.sh`); the coverage rule is MF2's |
| MF5 | `release_20261015/README.md`: section "Run order" (the review's order, with the release host of SF7, SF6 as the coordinator's step 1, the printed counts set in step 5 with a no-Lean snippet) | The snippet gives 5417 names and 783 modules at `d066071`, the values T3 recomputes |
| SF1 | `verify_release_inputs.py`: `LEAN_INPUTS` binds `bfgs_lean_article/scripts`; `load_script`, `expected_audit`, `expected_replay` recompute the audit's name counts and the replay's module closure with the scripts' own functions; checker tag = `v` + pinned Lean; the history and working-tree checks now run before the recount, so a changed source is reported as such | `t3_tests.py`: N11, N22, N23, N24, N27 fail; P0 passes on reports relabeled with the recomputed counts (simulation); the real reports of `9f03d7c` relabeled to a scratch commit fail with `declarations_checked [5403, 5417]`, `coverage_register_names [3208, 3222]` |
| SF2 | `verify_release_inputs.py`: `except Exception`, recorded with the exception type | N17–N21 are recorded FAILs; the other 22 results are kept |
| SF3 | `verify_release_inputs.py`: `companion/current_verification.tex` must state "checked <N> Lean names" and "(<M> modules;" of the bound reports | the printed count set back to 5403 fails with "does not state the counts of the bound reports" |
| SF4 | `verify_historical_baseline.py`: `SEPTEMBER_RELEASE`; `git diff --name-status 3e8b5c6 HEAD -- 'editorial/*.lean'` must be empty (labels `08b`, `08c`) | `t1_t2_tests.sh`: renamed, deleted and added editorial Lean files fail ("Editorial Lean files changed since the 13 September release: R100 …"); the positive case passes |
| SF5 | `refresh_correspondence.py`: `MACRO`, `macro_definitions`, `macro:<name>` units in `compute_units`; macro rows cite no register item; receipt `macro_definition_preservation` | A9 fails (`Unlisted change macro:\R`) |
| SF6 | Outside the six paths (coordinator, before T4's `--write`); recorded as step 1 of "Run order" | — |
| SF7 | `release_20261015/README.md`: section "Release host" (APFS clone of H's `.lake` and `.toolchain` outside the temporary directory, one binding check, W links to the copy, never to H) and C5/C6 in the T1–T5 table | Full validation below ran against the reviewer's APFS copy; H's recorded state identical before and after |
| OP1 | `verify_historical_correspondence.py`: `tree_files` hashes the files that `git ls-files --cached --others --exclude-standard` lists (a tracked file missing in the working tree counts as changed; every input must exist at the release commit); `refresh_correspondence.py`: `verify_snapshot` takes the snapshot's file set from git the same way | `t1_t2_tests.sh` `ignored_DS_Store`: PASS; an untracked `extra.txt` still fails (T2 and T4); an ignored `.DS_Store` in T4's `prior_mapping/` passes |
| OP2 | `verify_historical_correspondence.py`: `main` reports an existing run directory as `{"status": "FAIL", …}`, exit 1, without touching it | `t1_t2_tests.sh` `existing_run`: FAIL with the message, no traceback |
| OP3, OP4 | `release_20261015/README.md`: "Limits, by design"; `refresh_correspondence.py` docstring | A4, A11, A11b still pass after `--write`, by design (documented) |
| OP6 | `package_release.py`: the archive README says what the gate binds for the replay (Lean files, Lake configurations, scripts), that the counts are recomputed, and how lean4checker is built on macOS 26 | The `AUTHOR_REVIEW_README.md` of the scratch ZIP |
| OP7 | `verify_historical_baseline.py`: `name_status` parses `git diff --name-status -z` (renames and copies as `old<TAB>new`, as before) | Unit test: an added non-ASCII package path and a rename parse correctly, a truncated record fails; T1 positive unchanged (33 + 46 added paths) |
| OP9 | `refresh_correspondence.py`: `correction_text`; `--propose` prints `correction_item_texts` (the TODO paragraph of every correction item that a row cites) | Fix-pass test: the texts of M33, W39 and the `TODO_LEAN_REVIEW.md` item are printed |

**Final run** (`fix_final_run.sh`, 07:33–07:41): a fresh clone of the repository at `d066071` with the six
paths exactly as placed there (scratch commit `c1fc8bc`).

- T4 with the repository's empty `CHANGES.json`: `--check` fails ("Unlisted change", expected); `--propose`
  lists 27 changes (4 statements, 4 displays, 2 tables, 6 proofs, 3 negative passages, 6 root passages, 2 appendices).
- T1: PASS, 13 s (33 + 46 added paths; editorial Lean files unchanged since `3e8b5c6`; frozen inputs 761/286). T2:
  PASS, 2 s (31 unchanged inputs; the September check passes at `3e8b5c6`, its failure at the current commit is
  recorded).
- T3 at `d066071` with the tooling, without cache links: 19/23, as expected (the three "Reviewed source contracts"
  checks until T4's `--write`, and the October Lean evidence, whose reports describe `9f03d7c`).
- Scratch freeze `f5e8cd1`: the 27-row provisional table (not reviewed) written, ledger rebuilt;
  `AXIOM_AUDIT.json` and `KERNEL_REPLAY.json` relabeled as audits of a scratch commit with the recomputed counts,
  and `companion/current_verification.tex` stating them (a simulation, as in the review, not evidence); PDFs and
  render manifest. T4 `--check`: PASS; T3: 23/23.
- On the freeze: 18/18 negative tests, 13/13 scenarios, 6/6 fix-pass tests; `t4_adversarial.py`: A1, A2, A5, A5b,
  A6, A7, A8, A9, A10, A10b, A12, A13, A16 (ten pinned inputs) and A17 fail, A4, A11, A11b pass after `--write` (by
  design), A15 deterministic; `t1_t2_tests.sh`: as in the table (T1: prefix and outside-scope paths, the modified
  main library, renamed, deleted and added editorial Lean files fail; a modified package file passes, being bound by
  T3; T2: every negative case fails, `.DS_Store` passes, an existing run directory fails cleanly; `python3 -O`
  refused by both); `t3_tests.py`: P0 PASS, N1–N27 FAIL (N3b, an untracked file in an ignored directory, PASS by
  design).
- Packaging and validation, with the cache links pointing to the reviewer's APFS copy `host/bfgs_lean_stage1/`
  (never to H): `cache_binding.py --check` before: PASS (8853 objects, 32470 files); `verify_release_inputs.py`
  23/23 with `current_cache_bytes_verified: true`; `package_release.py` PASS (159,340,499 bytes, 4965 members);
  `validate_archive.py` **PASS** in 2 min 16 s, 41 commands: both documents byte- and pixel-identical (49 + 108
  pages); `04_historical_correspondence`, `04_current_correspondence`, `04_coverage_register` exit 0; four
  supplements PASS (3, 11, 14, 3 module-owned declarations); cache checks before and after library use PASS;
  `09_release_inputs` 23/23; historical gate PASS; extraction removed. `cache_binding.py --check` after: PASS.
- H, read with `GIT_OPTIONAL_LOCKS=0` (HEAD `db4dc37`, status, `known-projects` hash `264e0c41…` and 7 lines,
  mtimes of H, `bfgs_lean_stage1`, `elan`, `known-projects`, `.git`, `.git/index`, `.lake` and the nine
  dependency checkouts and their indexes): identical before (07:32) and after (07:40) the fix pass, and identical to
  the reviewer's last record (07:11). Its `known-projects` still lists the three scratch paths that the phase-A dry
  runs added before this review; removing those lines is harmless.
