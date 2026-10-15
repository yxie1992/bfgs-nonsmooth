# Plan for the next release run (October 2026 edition)

Study of 15 October 2026 by a read-only subagent; nothing in the repository was changed.
Evidence, scratch tools and logs: this directory (`PROGRESS.md`, `tools/`, `*.json`, `*.err`).
Repository state studied: `1abfe07` (HEAD) plus the uncommitted step-2 corrections in the
working tree (61 modified files at 04:40).

Notation used below:

    R=/Users/yxie/Projects/bfgs-nonsmooth                 # main repository
    H=/Users/yxie/Documents/ChatGPT/BFGS-non-smooth        # September checkout (sealed Lean host cache, all old ZIPs); never modify
    S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/release    # scratch
    D=YYYYMMDD                                             # freeze date, e.g. 20261016
    W=/Users/yxie/Projects/release_$D/BFGS-non-smooth      # release workspace (recommended, see D2)
    ED=editorial/release_$D                                # new editorial record directory
    RUN=coverage_${D}_01                                   # validation run id

---

## 0. Summary

1. The 13 September release was made **on this MacBook**, in `$H`. That checkout still
   exists, at `db4dc37`, with the sealed Lean host cache (`bfgs_lean_stage1/.lake` 5.9 GB,
   `.toolchain` 1.5 GB) and the git-ignored ZIPs of all four editions (13 September ZIP
   `b76bd245…` verified). The release depends on it: keep it untouched.
2. Three parts of the archive replay fail today because of legitimate October changes, and a
   fourth because of the machine set-up:
   - the 13 September correspondence check `refresh_correspondence.py --check` (stale since
     `f8ca4cc`; statement changes since `5476ba7`);
   - three "Reviewed source contracts" checks of `verify_release_inputs.py` (12 article/companion
     file hashes);
   - `verify_historical_baseline.py` ("Current history differs beyond added editorial Lean files;
     investigate explicitly": the new package `bfgs_lean_article/`);
   - the default Lean host of `validate_archive.py` (the main repo's `.lake` was rebuilt on
     14 October and fails the seal; there is no `.toolchain`).
   All other parts were dry-run in scratch and pass: build (PDFs byte-identical across
   directories), packaging (17 s, 154.6 MB), extraction, page-pixel comparison, companion
   check, cache binding against the September host.
3. Honest fixes: a new bounded correspondence revision for October (the September check is
   then replayed unchanged at its own release commit `3e8b5c6`, where it passes); extend the
   historical-gate wrapper to added files under `bfgs_lean_article/`; use the sealed September
   host cache; add read-only checks that bind the October axiom audit, kernel replay and
   coverage register to the frozen sources. No frozen baseline (`BASELINE.json`, audit inputs,
   the cache seal) is re-hashed, every recomputed review hash comes with an explicit list of
   the changes it covers, and no check is dropped.
4. Lean: the archive replay compiles and audits only the four September supplements (about
   75 s, against the sealed host). The October evidence is re-run in the main repo on the
   final commit before the freeze: `lake build` (about 3 min, incremental), axiom audit
   (6.5 min), kernel replay (27 min).
5. Time: about one working day, of which roughly one hour of machine time; the tooling
   (about 4 h of agent work, mostly the correspondence revision) and the visual review of
   about 157 pages (1–2 h) dominate.

---

## 1. The release tooling and how the 13 September release ran

### 1.1 What each script does

Times measured on this MacBook (Apple M5) in scratch copies, unless marked "Sept" (from
`release/validation/runs/exposition_20260913_01/commands.json`).

| Script | What it does | Reads | Writes | Time |
|---|---|---|---|---|
| `editorial/build.sh` | Regenerates figures, companion chapters, shared appendix, ledger; builds both PDFs with `latexmk -g` (`SOURCE_DATE_EPOCH=1789199005` = 12 Sep 2026 07:43:25 UTC, `FORCE_SOURCE_DATE=1`); runs `check_documents.py` | everything below | `paper/figures/*.{tex,pdf}`, `companion/chapters/*.tex`, `companion/SOURCE_CORRESPONDENCE.json`, `companion/appendices/seed_certificate.tex`, `editorial/CLAIM_LEDGER.json`, `companion/PROOF_CORRESPONDENCE.html`, `editorial/logs/{figure_build,paper_build,companion_build}.log`, `editorial/logs/document_checks.json`, `paper/build/`, `companion/build/` | 5.3 s (clean) |
| `paper/figures/generate_figures.py` | Exact-arithmetic TikZ figures, compiled with pdflatex | `seed_data.json` | `cycle_trials.*`, `shrinking_scales.*`, `paper/figures/build/` | in build.sh |
| `editorial/generate_companion.py [--check]` | Companion chapters from the frozen sources of `bfgs_lean_stage1/master_report` through logged transformations; frozen-source SHA guard against `editorial/BASELINE.json` | frozen sources, `BASELINE.json` | chapters, `SOURCE_CORRESPONDENCE.json` (`--check`: nothing) | 0.2 s |
| `editorial/prepare_shared_appendix.py` | Article seed appendix → companion appendix (with companion-only corrections) | `paper/appendices/seed_certificate.tex` | `companion/appendices/seed_certificate.tex` | <0.1 s |
| `editorial/assemble_claim_ledger.py` (+ `ledger_addenda.py`, `companion_statement_inventory.py`, `active_tex_sources.py`) | Claim ledger and HTML correspondence; statement locations recomputed, proof locations and root/deduction locations copied from the three component reviews; October addenda from `editorial/lean_review_20261013/LEDGER_ADDITIONS.json` with signatures from `bfgs_lean_article/AXIOM_AUDIT.json` | contract reviews, CLAIMS, DECLARATION_INDEX, supplement declarations, AXIOM_AUDIT.json | `CLAIM_LEDGER.json`, `PROOF_CORRESPONDENCE.html` | ~1 s |
| `editorial/check_documents.py` | Rejects undefined/multiply defined references and TeX errors; records pages, hashes, overfull boxes | `*/build/master.{pdf,log}` | `editorial/logs/document_checks.json` | <1 s |
| `editorial/render_review.py` | Renders every page at 100 dpi (`pdftoppm`), contact sheets, page hashes; copies the previous manifest to `render_history/` | `*/build/master.pdf` | `editorial/reviews/render_manifest.json` (status `PENDING_VISUAL_REVIEW`), `render_history/<16hex>.json` (tracked), `rendered/`, `contact_sheets/` (ignored) | 19.6 s; **needs Pillow: `~/.venvs/pdf/bin/python`** (Homebrew `python3` has no PIL) |
| `editorial/verify_release_inputs.py` | 21 read-only checks: BASELINE files, main-audit inputs, article-only audit, 4 supplement receipts, cache binding (runs `cache_binding.py --check` if `.lake` and `.toolchain` both exist; source-only scope if neither; FAIL if only one), the three component reviews' article hashes, ledger mapping, 172 spans / 3087 exports, root obligations, PDF = document_checks, no TODO/TBD/FIXME/placeholder | as listed | `editorial/logs/release_integrity.json` (so it is not read-only on the tree) | 1.7 s source-only, +9 s with the cache check |
| `editorial/scientific_exposition_20260913/refresh_correspondence.py --check/--write` | 13 September bounded refresh: from the 91d30da snapshot (`prior_mapping/`) it re-derives the three component reviews, asserting statements and displays equal modulo scoped notation aliases, and compares bytes; pins hashes of `verify_release_inputs.py` and `assemble_claim_ledger.py` | TeX, `prior_mapping/`, N-reviews | `--write`: the three reviews + `mapping_refresh.json` | 0.1 s |
| `editorial/satisfaction_review/cache_binding.py --check` | Read-only byte check of the sealed host cache (`cache_binding_04`: 8853 `.olean` objects, 32470 files incl. Lake traces, compiler files, 9 dependency checkouts) | `<root>/bfgs_lean_stage1/{.lake,.toolchain}` | nothing | 9 s |
| `editorial/package_release.py` | Requires a clean tracked tree, `RELEASE.json` status `SOURCE_REVIEWED_AWAITING_ARCHIVE_VALIDATION` with null archive/validation, release PDFs committed and equal to `*/build/master.pdf`, render manifest and document checks agreeing; writes the ZIP (git archive of HEAD + `_archive/history.bundle` + restore helper + `RELEASE_SNAPSHOT.json` + `AUTHOR_REVIEW_README.md` + `CONTENTS.json`); archive root = `ROOT.name` | git, release files | `release/BFGS_paper_companion_sources.zip` (ignored), `release/SOURCE_MANIFEST.json` | 17 s (154.6 MB, 4904 members for the HEAD tree) |
| `packaging/restore_git_history.py` (`_archive/…` in the ZIP) | Restores `.git` from the bundle in a fresh extraction | `_archive/*` | `.git` in the extraction | 3 s |
| `editorial/validate_archive.py --run-id … [--lean-cache-root …]` | Fresh extraction under `release/work/`, member hashes, history restore, `build.sh`, text + page-pixel comparison against the render manifest, `generate_companion.py --check`, the 13 Sep correspondence check, cache-binding authentication, links `.lake`/`.toolchain` of the host, cache check before/after, 4 supplement replays, `verify_release_inputs.py`, `verify_historical_baseline.py` | ZIP, SOURCE_MANIFEST, host cache | `release/validation/runs/<run>/` (logs, SUMMARY, copies of the supplement and historical-gate runs) | Sept 2.3 min (39 commands); dry run of the non-Lean part here: 40 s |
| `editorial/narrative_rebuild/{positive,negative}_formal/verify.py`, `editorial/satisfaction_review/{formal,branch_formal}/verify.py` | Fresh compile of each supplement (`lake env lean -R … -o …`) and a full structural/axiom dependency audit (`DependencyAudit.lean`); uses `bfgs_lean_stage1/.toolchain/elan` if present | supplement sources, host `.lake` | `runs/<id>/` (in the extraction) | Sept 19, 10, 24, 18 s |
| `editorial/verify_historical_baseline.py --run-id …` | Worktrees at HEAD and at `00362c0`; compares 761 frozen audit inputs and 286 sealed artifacts; runs the unchanged legacy gate (`bfgs_lean_stage1/scripts/verify_rigorous_master_report.py`, Node.js) at HEAD (expected failure) and at `00362c0` (must pass); no Lean | git history, node | `editorial/historical_baseline/runs/<id>/`, worktrees under `release/work/` | 6.6 s failing / 13.5 s passing; Sept 17.7 s |
| `bfgs_lean_article/scripts/axiom_audit.py`, `kernel_replay.py` | October evidence (not called by any release script) | built `.lake`, ledger, registers | `--report` files | 6.5 min / 27 min |
| `editorial/lean_coverage/check_coverage.py [--strict [--allow-discrepancies]]` | October coverage register check (not called by any release script) | registers, TeX, Lean sources | nothing | 0.3 s |
| `paper/figures/check_trial_display.py`, `packaging/make_archives.py` | Diagnostic / the 12 Sep `dist/` archives; not part of the release chain | | | |

### 1.2 The 13 September sequence

From `git log -- release/`, the diffs of `release/RELEASE.json`, `editorial/scientific_exposition_20260913/{WORKLOG.md,package.log,archive_validation.log,*push.json,final_receipt_review.json}` and the run's `commands.json`. Times PDT.

1. Work commits up to `5df9c95` (13:12).
2. Uncommitted preparation, committed in the freeze: `refresh_correspondence.py --write`;
   `bash editorial/build.sh` (ledger, PDFs, logs); PDFs copied to `release/`;
   `render_review.py` and the visual reviews (`VISUAL_ARTICLE.json`, `COMPANION_VISUAL.json`,
   inspection status in `render_manifest.json`); `verify_release_inputs.py`
   (`release_integrity.json`, copy `release_integrity.log`); the 12 Sep edition preserved in
   `release/history/20260912_satisfaction/` with `PRESERVATION.json` (incl. the ZIP hash; the
   ZIP itself git-ignored); `RELEASE.json` = `SOURCE_REVIEWED_AWAITING_ARCHIVE_VALIDATION`,
   `source_commit`/`source_archive`/`extraction_validation` null; README.
3. **Commit A** `3e8b5c6` (13:34:26), pushed (`source_push.json`, 20:34:47Z).
4. `python3 editorial/package_release.py` → ZIP and `SOURCE_MANIFEST.json` (`package.log`).
5. `python3 editorial/validate_archive.py --run-id exposition_20260913_01`
   (20:36:03–20:38:21Z, 39 commands, PASS; `archive_validation.log`).
6. `final_receipt_review.json` (read-only re-hash of ZIP, manifest, summary, 78 command logs);
   `RELEASE.json` → `VALIDATED_AUTHOR_REVIEW_RELEASE_AWAITING_RECEIPT_PUSH` with commit, archive,
   validation, `formal_status`, `source_push` PASS, `release_push` PENDING; README paragraph;
   STATUS/NEXT_STATE/WORKLOG/REVIEW_LOG/RESPONSE.
7. **Commit B** `fa54d6a` (13:45:43), pushed (`final_push.json`; GitHub warned about a 56.72 MB
   dependency graph, non-blocking).
8. **Commit C** `db4dc37` (13:46:43): `COMPLETE_AUTHOR_REVIEW_RELEASE`, `release_push`,
   `release_commit`, README last paragraph, status files; pushed.

The host was `$H` with Homebrew Python 3.14, TeX Live 2025/Homebrew (pdfTeX 1.40.27,
latexmk 4.86a) and Node v22.22.0: the same versions as now. Poppler is now 26.04 (irrelevant:
the render manifest and the replay use the same `pdftoppm`).

---

## 2. Checks that fail or need updating, and the honest fix

State "now" = HEAD `1abfe07` in scratch, unless marked "working tree".

| # | Check | State now (evidence) | Cause | Honest fix |
|---|---|---|---|---|
| C1 | `refresh_correspondence.py --check` (13 Sep), run by `validate_archive.py` as `04_focused_correspondence` | FAIL: `('Existing mathematical display changed', 'paper/sections/global.tex', 'art:inward-to-radial')`. PASS at `3e8b5c6`, `db4dc37`, `c76e663`; byte-stale from `f8ca4cc` (pins the hash of `assemble_claim_ledger.py`); statement change from `5476ba7` | By design it rejects every non-alias statement change (TODO_LEAN_REVIEW.md, second pass) | **Retire as historical, replayed:** a wrapper runs the unchanged script in a detached worktree at `3e8b5c6` (must PASS: "31 named contracts; 52 existing labeled displays"), asserts that the script and its inputs (`prior_mapping/`, N-reviews, `mapping_refresh.json`) are unchanged at HEAD, and records the expected failure at HEAD. **Replace its current role** by the October revision's `--check` (C2). Recorded in README, `RELEASE.json`, validator SUMMARY |
| C2 | `verify_release_inputs.py` "Reviewed source contracts" ×3 | FAIL: positive (planar_geometry, energy, global, local), negative (negative_lower, failure, seed_certificate, lower_curvature), root (master, energy, verification, `companion/chapters/13_L.tex`; working tree adds `companion/research_story.tex`) | Hash maps of the reviewed files; the manuscripts changed (M1–M11 so far; M12–M41, W-items to come) | **New bounded correspondence revision** (T4 below), baseline `3e8b5c6`: explicit list of changed statements/displays with their correction items and LEAN register items, recomputed locations, proof passages and hashes, immutable evidence unchanged, receipt with `--check`. The check itself stays unchanged and passes again. Changes so far (Sept normalizer): statements `art:seed_cycle`, `art:local-failure-lower`, `art:lower_hyperbolic`, `art:quadratic_failure`; displays `art:inward-to-radial`, `art:lower_return`; all 65 anchors still resolve uniquely (32 moved) |
| C3 | Ledger `proof_locations` (lower_curvature.tex) and other copied locations | stale lines (AGENTS.md "Known stale") | Copied from the 13 Sep reviews | Fixed by C2's revision, then `assemble_claim_ledger.py` |
| C4 | `verify_historical_baseline.py` (`10_historical_gate`) | FAIL: "Current history differs beyond added editorial Lean files; investigate explicitly" (79 added Lean-ish paths; 46 under `bfgs_lean_article/`, incl. `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`). Frozen inputs PASS (761/286); legacy gate fails at HEAD at the expected assertion | The wrapper allows only added `editorial/**/*.lean` | **Extend with a recorded reason:** also allow *added* (status `A`) paths under `bfgs_lean_article/` (the October package; requires the unchanged main library by path; `git diff 3e8b5c6 HEAD -- bfgs_lean_stage1` is empty). Keep every other requirement. Tested in scratch: PASS in 13.5 s, legacy gate PASS at `00362c0` |
| C5 | Lean host of `validate_archive.py` (default `--lean-cache-root $ROOT/bfgs_lean_stage1`) | main repo: `.toolchain` missing → bare `AssertionError` (empty failure message); with a `.toolchain` added, the cache check fails "Project traces changed since the binding run" | The main repo's `.lake` was rebuilt on 14 Oct: all 736 main-library `.olean` files (and a 300-file Mathlib sample) are byte-identical to September's, but the Lake trace logs differ (toolchain path, LEAN_PATH via `../bfgs_lean_stage1`) | **Use the sealed September host** `$H/bfgs_lean_stage1` (PASS, 8853 objects / 32470 files, 9 s). No re-seal: `cache_binding.py --seal` insists on the 12 Sep trace baseline, so a new seal would need new tooling. Old toolchain binaries are byte-identical to `~/.elan`'s, so they run on macOS 26 |
| C6 | `verify_release_inputs.py` cache check in the main repo | FAIL "only partially available" (`.lake` without `.toolchain`) | as C5 | Environment, not source: run it where `.lake`/`.toolchain` link to `$H` (release workspace, D2) or where both are absent; document in README. Do not relax the partial-cache rule |
| C7 | `editorial/BASELINE.json` (42 files), main-audit inputs, supplement receipts, `master_report/audit/fresh/INPUTS.json` | PASS | — | Nothing. Do not re-baseline |
| C8 | `generate_companion.py --check` | PASS at HEAD | — | Must pass on the freeze (commit regenerated outputs with the transformations) |
| C9 | `check_documents.py`, overfull boxes, page counts | PASS at HEAD; 49 + 108 pages (Sept 49 + 107) | October paragraph in the companion etc. | Must stay overfull-free; new counts go into README/RELEASE.json |
| C10 | Render manifest and visual review | stale (13 Sep PDFs) | new PDFs | Regenerate (`render_review.py`), all-page visual review, new records (D8) |
| C11 | Bound October Lean evidence | **not checked by any release script**; `AXIOM_AUDIT.json`/`KERNEL_REPLAY.json` describe `9f03d7c`; 18 coverage modules modified since (working tree) | new evidence, never wired in | **Add the October evidence:** re-run on the final pre-freeze commit; add read-only checks (T3) that the audited commit is an ancestor of HEAD and no Lean input, ledger or register changed since; `check_coverage.py --strict` |
| C12 | `check_coverage.py --strict` | exit 1 at HEAD (open companion discrepancies); 0 with `--allow-discrepancies` | step 2 in progress | Freeze only when `--strict` exits 0, or record the open items (D7) |
| C13 | `release/README.md` statements | stale | October work | Rewrite (section 4): "49 pages … 107 pages"; "The revision adds no Lean theorem, custom axiom or weakened guard" (false now); "All 31 named article statements, 52 existing labeled displays … agree with the baseline under explicit scoped notation aliases" (false now); reproduction command `refresh_correspondence.py --check` (fails); "preceding 12 September edition … `history/20260912_satisfaction/`"; "three self-review passes and N1–N6"; outer directory `BFGS-non-smooth/` (see D2); requirements omit Node.js, Pillow, elan |
| C14 | `RELEASE.json`, `SOURCE_MANIFEST.json`, `editorial/logs/*` | describe 13 Sep (`editorial/logs/*_build.log` still contain the September path) | — | Regenerated by the run (section 4) |
| C15 | Printed edition date | "Author-review edition, 13 September 2026" in `paper/master.tex:29`, `companion/master.tex:16`; companion footers `companion/preamble.tex:62,65` (every page) | — | D1: change to the freeze date (not a coverage item; no line shift) |
| C16 | `AUTHOR_REVIEW_README.md` inside the ZIP (template in `package_release.py`) | silent about the October package | — | T5: add the `bfgs_lean_article` build, axiom audit and kernel replay commands |
| C17 | `editorial/STATUS.json`, `NEXT_STATE.json`, `COMPLETION_GATES.json`, `AI_AND_AUTHOR_ACTIONS.md` | 13 Sep records; AI statement names only ChatGPT/Codex (M37) | not machine-checked | Update as records (keep history); M36/M37 are manuscript items of step 2 |
| C18 | HANDOFF.md / AGENTS.md "Known stale", TODO_LEAN_REVIEW.md "Release receipts are now stale" | open | — | Close after the release (commit C) |

Record C1–C18 as TODO items before starting (e.g. sub-items of "Release receipts are now
stale (expected)" in `TODO_LEAN_REVIEW.md`), commit and push (AGENTS.md).

---

## 3. Lean runs

| Run | Where | What it checks | Weight | Caches |
|---|---|---|---|---|
| 4 supplement replays (inside `validate_archive.py`) | fresh extraction | fresh compile + full structural/axiom audit of `MixedBenchmark`, `negative_scaling`, `ArticleGeometry`+`ConvexBalance`, `ArticleBranchRegularity`; declarations, types and axioms must equal the recorded audits (3/11/14/3 module-owned declarations) | ~75 s, sequential, ~4–5 GB RSS each | **must** reuse the sealed September host through the extraction's `.lake`/`.toolchain` symlinks; no main-library or Mathlib build |
| Cache-binding check before/after | extraction | host bytes unchanged | 2 × 9 s | September host |
| Main-library audit | — | authenticated from the 12 Sep receipts only (no replay) | — | — |
| Historical gate | extraction | no Lean (`fresh_lean_compilation: false`) | 15 s | — |
| October: `lake build` in `bfgs_lean_article` | main repo, before the freeze | coverage modules (docstrings changed by the corrections), guard file, root | ~3 min incremental (12.5 min from scratch) | main repo `.lake` |
| October: `axiom_audit.py --jobs 6 --write-guard` | main repo, clean committed tree | every ledger, register and package name: only `propext`, `Classical.choice`, `Quot.sound` | 6.5 min | main repo `.lake` |
| October: `kernel_replay.py --self-test --jobs 8` | main repo, clean committed tree | lean4checker v4.19.0 on every project module (783) | 27 min | main repo `.lake`; checker built at `/private/var/folders/9b/…/T/opencode/lean4checker` (macOS may purge `T/`; rebuild with `LIBRARY_PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.19.0/lib LEAN_CC=/usr/bin/clang lake build`) |

Optional (not recommended for this run): a fresh build of the October package inside the
extraction. Its main-library dependency would resolve through the symlinked September `.lake`;
if Lake judged anything stale it would write into the sealed cache and break the seal. Only
with an APFS clone of the host (`cp -cR`), as a separate reviewed extension (+5–15 min).

---

## 4. What to preserve, and what the new release files must say

### 4.1 Preserve

- **The 13 September edition** in `release/history/20260913_exposition/`: `git show
  db4dc37:release/<f>` for `BFGS_Journal_Article.pdf` (668968 B, `ed49ff10…`),
  `BFGS_Complete_Companion.pdf` (883126 B, `3566ec4f…`), `README.md` (5544 B, `cc1e1756…`),
  `RELEASE.json` (3322 B, `5a23456b…`), `SOURCE_MANIFEST.json` (2743 B, `07718f65…`), plus
  `PRESERVATION.json` (format of `history/20260912_satisfaction/PRESERVATION.json`, with the ZIP
  entry 134645123 B, `b76bd245…`). Copy the ZIP itself from `$H/release/` (git-ignored, local).
  Optionally copy the three older ZIPs from `$H/release/history/*/` into the corresponding local
  history folders (hashes match their receipts: `e80514f1…`, `9f34ef3c…`, `64633451…`).
- Keep `release/validation/runs/exposition_20260913_01/` and the older runs where they are.
- Keep `editorial/scientific_exposition_20260913/` unchanged (historical; replayed at `3e8b5c6`).
- `render_review.py` keeps the old render manifest in `render_history/` automatically.
- Keep `$H` (sealed host cache and ZIPs). Optional backup: `cp -cR` of
  `$H/bfgs_lean_stage1/{.lake,.toolchain}` (APFS clone, instant).

### 4.2 `release/README.md` (outline; numbers from the final build)

1. Title: "BFGS article and complete companion — <D> October 2026 Lean-coverage and correction
   edition".
2. Summary: pages (article N, companion M); architecture and positive/negative theorem
   selection unchanged; what changed since 13 September: Lean coverage of every claim of both
   documents (616 article items, 1856 companion items, 33 coverage modules), manuscript
   corrections M1–M41 and companion wording points W1–W43 (`TODO_MANUSCRIPT_REVIEW.md`), the
   strengthened statements (e.g. Proposition `art:quadratic_failure` and Theorem
   `art:local-failure-lower` for every `0<c₁≤1/3`, `c₁<c₂<1`), line-by-line reading.
3. Files and entry points; "preceding 13 September edition … `history/20260913_exposition/`".
4. Reproduction: `bash editorial/build.sh`; `python3 $ED/refresh_correspondence.py --check`;
   `python3 editorial/lean_coverage/check_coverage.py --strict`;
   `python3 editorial/verify_historical_correspondence.py` (the 13 Sep check at `3e8b5c6`);
   `python3 editorial/verify_release_inputs.py` (with a note: needs restored git history; the
   cache check needs `.lake`+`.toolchain` matching the `cache_binding_04` seal, or neither; a
   rebuilt cache fails by design); Lean: `cd bfgs_lean_article && lake build`, axiom audit,
   kernel replay commands. Archive paragraph with the outer directory (D2). Requirements:
   Python ≥ 3.11, TeX Live + latexmk, Poppler, Node.js, Pillow for `render_review.py`,
   elan/Lean 4.19.0 for Lean.
5. Proof and review scope (replaces "adds no Lean theorem"): the main library and the four
   September supplements are unchanged; new Lean code is the package `bfgs_lean_article`
   (supplements compiled in place, new modules, coverage modules), no custom axiom; axiom audit
   (N names) and kernel replay (M modules) of `<commit>`, bound to the frozen sources; the
   correspondence revision lists the K changed named statements and L changed displays with
   their correction items, the others unchanged; 172 spans and 3087 exports preserved; the
   September correspondence check is historical and passes at `3e8b5c6`; release-tooling
   changes listed. Reviews: Lean review passes 1–4, Lean coverage with independent reviewer
   agents, six-reader line-by-line reading, corrections, visual review; all by AI agents
   (Claude in OpenCode); author's expert check pending.
6. Validation paragraph (added in commit B) and push paragraph (commit C), as on 13 Sep.
7. Author decisions: as before, plus the AI-use statement now covering the October work (M37).

### 4.3 `release/RELEASE.json`

Freeze (commit A). `package_release.py` and `validate_archive.py` require the status, the two
null fields and a `pdfs` block equal to the delivered PDFs; the other fields are records:

    "status": "SOURCE_REVIEWED_AWAITING_ARCHIVE_VALIDATION",
    "edition": "<D> October 2026 Lean-coverage and correction edition",
    "source_commit": null,
    "source_commit_policy": "The source freeze is identified by the Git commit recorded by the package snapshot after this metadata is committed.",
    "pdfs": {"BFGS_Journal_Article.pdf": {"bytes", "sha256", "pages"}, "BFGS_Complete_Companion.pdf": {…}},
    "source_archive": null,
    "extraction_validation": null,
    "previous_release": "release/history/20260913_exposition/RELEASE.json",
    "article_source": "paper/master.tex", "companion_source": "companion/master.tex",
    "formal_status": "<main library and September supplements unchanged; October package; audit/replay commit and counts; what the archive replay will and will not compile>",
    "lean_evidence": {"axiom_audit": "bfgs_lean_article/AXIOM_AUDIT.json", "kernel_replay": "bfgs_lean_article/KERNEL_REPLAY.json", "audited_commit": "<sha>", "coverage_register": "editorial/lean_coverage/register/"},
    "review_record": "$ED/REVIEW_LOG.md", "review_kind": "<AI-agent reviews; no human review or approval>",
    "source_correspondence": "$ED/mapping_refresh.json",
    "manuscript_corrections": "TODO_MANUSCRIPT_REVIEW.md",
    "release_tooling_changes": ["<T1>", "<T2>", "<T3>", "<T4>", "<T5>"],
    "author_actions": "editorial/AI_AND_AUTHOR_ACTIONS.md",
    "milestones_pushed": {…}

Commit B adds `source_commit`, `source_archive` {archive, bytes, sha256, members,
original_directory_structure_preserved}, `extraction_validation` {summary, summary_sha256,
status, run_id, commands, both_pdfs_byte_identical, all_rendered_pages_matched,
fresh_supplements: 4, scope}, `source_push`, `release_push: PENDING`, status
`VALIDATED_AUTHOR_REVIEW_RELEASE_AWAITING_RECEIPT_PUSH`. Commit C: `COMPLETE_AUTHOR_REVIEW_RELEASE`,
`release_push` {status, commit, evidence}, `release_commit`.

### 4.4 `release/SOURCE_MANIFEST.json`

Written only by `package_release.py`; never by hand. Expect: schema 2, PASS, `source_commit` =
commit A, `root_directory` (D2), ZIP bytes ≈ 155–160 MB, `members` = tracked files + 5,
`committed_prior_package_receipts` = 5 entries: `release/SOURCE_MANIFEST.json` (`07718f65…`,
`3e8b5c6`), `history/20260912_initial` (`7bcce9a`), `20260912_narrative` (`252ea5d`),
`20260912_satisfaction` (`573306b`), `20260913_exposition` (`3e8b5c6`).

---

## 5. Decisions needed (coordinator, with the author where marked)

- **D1 (author)** Edition label/date: replace "13 September 2026" (C15) by the freeze date.
  Recommended. Keep `SOURCE_DATE_EPOCH=1789199005` (fixed since 12 Sep; PDF metadata date).
- **D2** Workspace and archive root. Recommended **R**: a fresh clone `$W` named
  `BFGS-non-smooth` with `bfgs_lean_stage1/.lake` and `.toolchain` symlinked to `$H` (exactly the
  September layout; archive root keeps `BFGS-non-smooth/`; `verify_release_inputs.py` passes with
  cache bytes verified; the main repo stays untouched until `git pull --ff-only`).
  Alternative **M**: release from `$R`; archive root becomes `bfgs-nonsmooth/` (README must say
  so); pass `--lean-cache-root $H/bfgs_lean_stage1`; run the pre-flight `verify_release_inputs.py`
  in a clone with the symlinks and copy its `release_integrity.json` back.
- **D3** Host cache: `$H` (required; see C5).
- **D4** Correspondence: the strict October revision (T4). A bare re-hash would be a silent
  re-baseline; not acceptable.
- **D5** Historical gate: extend to added `bfgs_lean_article/**` (T1).
- **D6** October Lean evidence in the gates: T3 (read-only binding + coverage). The fresh
  in-extraction build stays optional (section 3).
- **D7 (author)** Freeze only with every DISCREPANCY corrected (`check_coverage.py --strict`
  exit 0), or list the open items in README and use `--allow-discrepancies` in T2/T3.
- **D8** Visual review: every page of both documents on contact sheets, every changed page at
  full size (with D1 every companion footer changes).

---

## 6. Step-by-step sequence

### Phase 0 — preconditions (main repo, ~10 min)

    cd $R && export PATH="$HOME/.elan/bin:$PATH"
    git status --porcelain                 # empty: all step-2 work committed
    git fetch origin && git status -sb     # main == origin/main
    pgrep -fl 'lean|lake'                  # no agent Lean processes
    python3 editorial/lean_coverage/check_coverage.py --strict    # exit 0 (else D7)
    python3 editorial/generate_companion.py --check               # PASS
    shasum -a 256 $H/release/BFGS_paper_companion_sources.zip      # b76bd245…
    # sealed host still intact (read-only, 9 s):
    git clone -q --no-hardlinks $R $S/hostcheck && cd $S/hostcheck
    ln -s $H/bfgs_lean_stage1/.lake bfgs_lean_stage1/.lake
    ln -s $H/bfgs_lean_stage1/.toolchain bfgs_lean_stage1/.toolchain
    python3 editorial/satisfaction_review/cache_binding.py --check \
      --manifest editorial/satisfaction_review/cache_binding/runs/cache_binding_04/MANIFEST.json --root $PWD
    # expect "status": "PASS", "object_count": 8853, "sealed_cache_file_count": 32470

Commit 0 (main repo): "Record the release-run issues C1–C18" (TODO_LEAN_REVIEW.md), push.

### Phase 1 — release tooling (main repo; agents; ~4 h incl. review)

Each change keeps every existing assertion and is named in the commit, README and
`RELEASE.json`:

- **T1** `editorial/verify_historical_baseline.py`: allowed added paths =
  `editorial/**/*.lean` ∪ `bfgs_lean_article/**`, status `A` only; failure text "…beyond added
  editorial Lean files and the added article package; investigate explicitly"; record the allowed
  scopes in SUMMARY; docstring with the reason. (Scratch patch tested: PASS.)
- **T2** `editorial/validate_archive.py`: replace `04_focused_correspondence` by
  `04_historical_correspondence` (new wrapper `editorial/verify_historical_correspondence.py
  --run-id archive_validation_<run>`; detached worktree at `3e8b5c6` under `release/work/`, PASS
  required; `git diff --quiet 3e8b5c6 HEAD -- editorial/scientific_exposition_20260913/refresh_correspondence.py
  editorial/scientific_exposition_20260913/prior_mapping editorial/scientific_exposition_20260913/N*_review.json
  editorial/scientific_exposition_20260913/mapping_refresh.json`; expected failure at HEAD
  recorded; copy its run directory into the validation output), `04_current_correspondence`
  (`python3 $ED/refresh_correspondence.py --check`) and `04_coverage_register`
  (`check_coverage.py --strict`); update the SUMMARY scope text.
- **T3** `editorial/verify_release_inputs.py`: two checks — (a) `AXIOM_AUDIT.json` and
  `KERNEL_REPLAY.json`: PASS, no missing/nonstandard/failures, `source_tree_clean`, Lean 4.19.0;
  their `source_commit` is an ancestor of HEAD and `git diff --name-only <commit> HEAD --
  '*.lean' '*lean-toolchain' '*lakefile.toml' '*lake-manifest.json' editorial/CLAIM_LEDGER.json
  editorial/lean_coverage/register` is empty (the replay only for the Lean paths); (b)
  `check_coverage.py --strict` exits 0. Both need git history (present in the repo and, after
  restore, in the extraction). The gate becomes 23 checks.
- **T4** `$ED/refresh_correspondence.py --write/--check` (the October correspondence revision),
  modelled on the 13 Sep script: baseline `3e8b5c6`, snapshot `$ED/prior_mapping/` (three
  reviews, `mapping_refresh.json`, every active article TeX file, `companion/research_story.tex`,
  `companion/chapters/13_L.tex`) with a hash MANIFEST; an explicit CHANGES table (label/anchor,
  file, correction items, coverage register item with status LEAN and current item hash,
  principal Lean exports, one reviewed sentence); asserts: statement and display label sets
  unchanged unless an addition or removal is listed, every statement body and labeled display
  equal to the baseline after whitespace normalization unless listed, the line-search
  algorithm block unchanged unless listed, every
  root/deduction anchor unique (changed anchors listed), the Sept immutable subtrees
  (`supplemental_cache_binding` etc.) byte-identical; recomputes locations, statement bodies,
  proof passages (start/end lines, passage hashes), `article_sha256`/`article_file_sha256`;
  receipt `$ED/mapping_refresh.json` (inputs, changes, preservation lists, output hashes, hashes
  of `verify_release_inputs.py` and `assemble_claim_ledger.py`, so T3 comes first). An
  independent reviewer agent checks every CHANGES row against `git diff 3e8b5c6` and the
  register, and a negative test (an unlisted edit in a scratch copy makes `--check` fail).
- **T5** `editorial/package_release.py`: extend the `AUTHOR_REVIEW_README.md` template with the
  October package commands.

Commit 1: "Release tooling for the October edition: …" (with `$ED/TOOLING_REVIEW.md`), push.

### Phase 2 — final sources and Lean evidence (main repo; ~1 h, 40 min machine)

1. D1 edits (if adopted): build both PDFs (AGENTS.md commands), inspect the changed pages,
   compare the LaTeX warnings, `resync_register.py` (no line shift expected).
2. `python3 $ED/refresh_correspondence.py --write`, then `python3 editorial/assemble_claim_ledger.py`;
   `--check` passes; `verify_release_inputs.py` in a scratch clone (it writes a log, and T3 needs
   git history; without cache links the cache check runs in source-only scope) → all PASS except
   T3(a), which can only pass after step 3.
   Commit 2: "October correspondence revision: component reviews, ledger and proof locations
   refreshed (corrections M…)", push.
3. Lean evidence on commit 2 (no agents running Lean):

        cd $R/bfgs_lean_article && lake build 2>&1 | tee $S/lake_build.log   # no warnings from BfgsArticle/Coverage
        git -C $R status --porcelain                                          # empty
        LEAN_NUM_THREADS=10 python3 scripts/axiom_audit.py --jobs 6 --write-guard --report $S/AXIOM_AUDIT.json
        git -C $R status --porcelain    # BfgsArticleAxioms.lean must be unchanged; if changed: commit, lake build, re-run
        python3 scripts/kernel_replay.py --checker-repo /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/lean4checker \
          --self-test --jobs 8 --report $S/KERNEL_REPLAY.json
        cp $S/AXIOM_AUDIT.json $S/KERNEL_REPLAY.json .
        cd $R && python3 editorial/assemble_claim_ledger.py && git status --porcelain   # ledger unchanged

   Update `bfgs_lean_article/README.md` counts, TODO_LEAN_COVERAGE.md, TODO_LEAN_REVIEW.md.
   Commit 3: "Axiom audit (N names) and kernel replay (M modules) of <commit 2>", push.

### Phase 3 — release workspace and freeze (D2 = R; ~2–3 h, mostly visual review)

    mkdir -p "$(dirname $W)"
    git clone -q https://github.com/yxie1992/bfgs-nonsmooth.git $W && cd $W   # or clone $R and set origin
    git log -1 --format=%H                       # = commit 3
    ln -s $H/bfgs_lean_stage1/.lake bfgs_lean_stage1/.lake
    ln -s $H/bfgs_lean_stage1/.toolchain bfgs_lean_stage1/.toolchain       # appear as untracked: expected

1. Preserve the 13 September edition (snippet A.1) → `release/history/20260913_exposition/`.
2. Build: `rm -rf paper/build companion/build && bash editorial/build.sh`. Expected: PASS, no
   overfull boxes; `git status --porcelain --untracked-files=no` shows only
   `editorial/logs/{paper_build.log,companion_build.log,document_checks.json}` (logs hold the
   absolute path, so they change in every checkout). Anything else (chapters, ledger, figures):
   stop, the sources were not regenerated before commit 3.
3. `cp paper/build/master.pdf release/BFGS_Journal_Article.pdf; cp companion/build/master.pdf release/BFGS_Complete_Companion.pdf`.
4. `~/.venvs/pdf/bin/python editorial/render_review.py` (≈20 s).
5. Visual review (D8): changed pages against the 13 Sep PDFs (snippet A.3; at HEAD already 22/49
   article and 21/108 companion pages), contact sheets in `editorial/reviews/contact_sheets/`;
   records `$ED/VISUAL_ARTICLE.json`, `$ED/VISUAL_COMPANION.json` (format of the 13 Sep ones);
   then set `inspection_status`/`inspection_record` (and per-page notes) in
   `render_manifest.json` without touching any hash. Any rebuild afterwards invalidates this.
6. Pre-flight: `python3 editorial/verify_release_inputs.py` → 23/23 PASS with
   `current_cache_bytes_verified: true` (writes `editorial/logs/release_integrity.json`; copy to
   `$ED/release_integrity.log`); `python3 $ED/refresh_correspondence.py --check`;
   `python3 editorial/verify_historical_correspondence.py` and the historical gate in a scratch
   clone of `$W` (they write run directories); safe-name check of the tracked tree (snippet A.4).
7. Write `release/README.md` and `release/RELEASE.json` (freeze shape, 4.3), `$ED/REVIEW_LOG.md`,
   `$ED/WORKLOG.md`; update `editorial/STATUS.json`, `NEXT_STATE.json` (awaiting validation).
8. **Commit A** "Freeze the <D> October 2026 edition: PDFs, logs, render and visual review,
   13 September edition preserved". Expected content: release PDFs, README, RELEASE.json,
   `release/history/20260913_exposition/*` (not the ZIP), `editorial/logs/*`, render manifest +
   new `render_history/*.json`, `$ED/*`, status files. Push; write `$ED/source_push.json`
   (snippet A.5). Do **not** run `build.sh` again before packaging.

### Phase 4 — package and validate (~10 min)

Right after commit A, in `$W`: HEAD = commit A, `git status --porcelain --untracked-files=no`
empty, `paper/build/master.pdf` and `companion/build/master.pdf` still the step-2 build.

    python3 editorial/package_release.py | tee $S/package.log            # never with -O; ~20 s
    python3 editorial/validate_archive.py --run-id $RUN | tee $S/archive_validation.log   # ~3 min
    # mode M only: add --lean-cache-root $H/bfgs_lean_stage1
    ls release/work/                                                      # empty afterwards

Expected `SUMMARY.json`: PASS; ≈42–45 commands; both documents `byte_identical: true`, every
page pixel-identical; `04_historical_correspondence`, `04_current_correspondence`,
`04_coverage_register` PASS; `cache_binding.checks` before/after PASS (8853/32470);
`fresh_supplemental_audits` 4 × PASS (3, 11, 14, 3 declarations); `09_release_inputs` 23/23;
`historical_gate` PASS; `temporary_extraction_removed: true`.

Then: `python3 $S/receipt_review.py $W $RUN > $ED/final_receipt_review.json` (copy
`tools/receipt_review.py` from this directory to `$S`, or commit it as `$ED/receipt_review.py`
so the receipt is reproducible; snippet A.2; it reproduces the 13 Sep numbers); copy
`package.log`, `archive_validation.log` into `$ED/`;
update RELEASE.json (commit-B shape), README validation paragraph, WORKLOG/REVIEW_LOG, STATUS/NEXT_STATE.

**Commit B** "Validate the <D> October release from the immutable source archive"
(`release/SOURCE_MANIFEST.json`, `release/validation/runs/$RUN/**`, `$ED/*`, RELEASE/README,
status files). Push; write `$ED/final_push.json` (expect GitHub's >50 MB warning for the
branch-regularity dependency graph, 59,479,629 bytes = 56.7 MiB, as on 13 Sep; blocking only
above 100 MB).

**Commit C** "Record the completed <D> October release and verified push": RELEASE.json
`COMPLETE_AUTHOR_REVIEW_RELEASE` + `release_push` + `release_commit`, README last paragraph,
status files, HANDOFF.md/AGENTS.md ("Known stale": release current, 13 Sep correspondence
historical, ledger locations current), TODO_LEAN_REVIEW.md item closed. Push.

Finally in the main repo: `cd $R && git pull --ff-only`; copy the new ZIP and the history ZIPs
into `$R/release/` if wanted (ignored); delete `$S/hostcheck` and scratch clones.

---

## 7. Failure modes

| Symptom | Cause | Response |
|---|---|---|
| `AssertionError` with empty message in `attach_pinned_library_cache` | host without `.toolchain` (main repo) | use `$H` (D2/C5) |
| "Project traces changed since the binding run" | host `.lake` is the rebuilt October cache | use `$H`; never run lake in `$H` |
| "Pinned cache/toolchain is only partially available" | `verify_release_inputs.py` in the main repo | run it in `$W` or a clone with both links (C6) |
| "Commit tracked source changes before packaging" | `build.sh` or an edit after commit A (logs carry absolute paths) | commit or revert; never rebuild between A and packaging |
| "Tracked release PDF differs from current build" / "Stale release metadata" | PDFs not copied, RELEASE.json pdfs stale, build outputs deleted | rebuild before commit A, copy, update RELEASE.json |
| "page pixels differ" / text differs | render manifest from another build, or a rebuild after rendering | render from the final build; redo the visual review |
| "Preserve the previous ZIP under release/history before replacing it" | a ZIP from a failed attempt exists | it was never receipted: delete it and restore `release/SOURCE_MANIFEST.json` from git before repackaging |
| `FileExistsError` on the run directory | reused run id | new id (`_02`); keep and document failed run directories (as `cache_binding_01`) |
| "Run without Python optimization" | `-O` or `PYTHONOPTIMIZE` | unset |
| `ModuleNotFoundError: PIL` | Homebrew python | `~/.venvs/pdf/bin/python editorial/render_review.py` |
| Node.js missing | historical gate | `brew install node` or `--node` |
| `overfull_warnings` non-empty | TeX edits | fix before the freeze |
| `check_coverage.py --strict` exit 1 | open discrepancy or stale register lines | finish step 2 or D7 |
| Axiom/kernel binding check fails | Lean file, ledger or register changed after the audited commit (e.g. `--write-guard` rewrote the guard) | re-run Phase 2 step 3 on the new commit |
| `source_tree_clean: false` in the reports | untracked files in `$R` (the scripts use `git status --porcelain`, untracked included) | remove or commit them, re-run the audit/replay |
| lean4checker missing | macOS purged the temp directory | rebuild it (HANDOFF.md) |
| Old host gone or modified | `$H` deleted/changed | no fallback without new sealing tooling; protect `$H` (APFS clone) |
| Unexpected files in `release/work/` after validation | leftovers (seen in `$H/release/work/` after 13 Sep) | inspect, delete (ignored), never commit |
| `safe_name` assertion on `bfgs_lean_stage1/.lake` in `package_release.py` | the `.lake`/`.toolchain` symlinks of `$W` were committed (they are *not* ignored: the pattern `.lake/` matches directories only) | never `git add -A` in `$W`; add explicit paths (new files: `release/history/20260913_exposition/`, `editorial/reviews/render_history/<new>.json`, `$ED/`) |

---

## 8. Time estimate

| Phase | Agent/coordinator | Machine |
|---|---|---|
| 0 preconditions, TODO commit | 15 min | 1 min |
| 1 tooling T1–T5 + review | ~4 h (T4 ≈ 2–3 h) | seconds |
| 2 sources + Lean evidence | 30 min | ~40 min (lake 3, audit 6.5, replay 27) |
| 3 freeze (preservation, build, render, visual review, docs) | 2–3 h | 1 min |
| 4 package, validate, receipts, 3 pushes | 30 min | ~4 min |

---

## Appendix A — snippets (tested where marked)

**A.1 Preserve the 13 September edition** (run in the workspace; tested in the scratch clone:
the five files and `PRESERVATION.json` appear as untracked, the ZIP is ignored by
`release/.gitignore`):

    python3 - <<'EOF'
    import hashlib, json, subprocess
    from pathlib import Path
    H = Path('/Users/yxie/Documents/ChatGPT/BFGS-non-smooth')
    dst = Path('release/history/20260913_exposition'); dst.mkdir(parents=True, exist_ok=False)
    files = {}
    for name in ['SOURCE_MANIFEST.json', 'README.md', 'RELEASE.json', 'BFGS_Complete_Companion.pdf', 'BFGS_Journal_Article.pdf']:
        data = subprocess.check_output(['git', 'show', 'db4dc37:release/' + name])
        (dst / name).write_bytes(data)
        files[name] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    data = (H / 'release/BFGS_paper_companion_sources.zip').read_bytes()
    assert hashlib.sha256(data).hexdigest() == 'b76bd245c8942b9162e60e1a0ba459f40d836c4a4ab6714b69750c0d65785e99'
    (dst / 'BFGS_paper_companion_sources.zip').write_bytes(data)          # git-ignored
    files['BFGS_paper_companion_sources.zip'] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    (dst / 'PRESERVATION.json').write_text(json.dumps({
        'scope': 'Unchanged preceding 13 September 2026 author-review release (focused scientific-exposition revision), preserved before replacement',
        'source': 'git show db4dc37:release/<file>; the git-ignored ZIP copied from the 13 September checkout',
        'files': files}, indent=2) + '\n')
    EOF

**A.2 Receipt review** — `tools/receipt_review.py` in this directory (tested on the 13 Sep
receipts: 39 commands, 78 logs re-hashed, 156 pages, 4 supplements, PASS):
`python3 tools/receipt_review.py <root> <run_id> [<zip>]`.

**A.3 Changed pages** — `tools/changed_pages.py` (PyMuPDF; tested):
`~/.venvs/pdf/bin/python tools/changed_pages.py <old.pdf> <new.pdf>`.

**A.4 Safe names** (package_release rules; tested on HEAD: no violations):

    python3 - <<'EOF'
    import subprocess; from pathlib import PurePosixPath as P
    F = {'.git','.lake','.toolchain','.cache','tmp','scratch','__pycache__','.DS_Store','work'}
    X = {'.olean','.ilean','.pyc','.aux','.fls','.fdb_latexmk','.toc'}
    n = subprocess.check_output(['git','ls-tree','-r','--name-only','-z','HEAD']).decode().strip('\0').split('\0')
    print([x for x in n if F & set(P(x).parts) or P(x).suffix in X or x.startswith('_archive/') or x == 'AUTHOR_REVIEW_README.md'])
    EOF

**A.5 Push receipt** (fields of the 13 Sep `source_push.json` / `final_push.json`; the Python
part tested with sample values):

    out=$(git -c credential.helper='!gh auth git-credential' push origin main 2>&1); code=$?
    ver=$(git ls-remote origin refs/heads/main)
    python3 - "$code" "$out" "$ver" > $ED/source_push.json <<'EOF'
    import json, sys, subprocess, datetime
    code, out, ver = int(sys.argv[1]), sys.argv[2], sys.argv[3].strip()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    print(json.dumps({'status': 'PASS' if code == 0 and ver.startswith(head) else 'FAIL', 'commit': head,
      'remote': 'origin', 'branch': 'main', 'push_exit_code': code, 'push_output': out,
      'remote_verification': ver, 'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}, indent=2))
    EOF

## Appendix B — scratch evidence (this directory)

- `head/BFGS-non-smooth`: `git archive` of `1abfe07`; `build.sh` PASS (5.3 s; 49 + 108 pages;
  regenerated sources identical to HEAD except the three logs); `vri_head.json` (3 FAIL);
  `render_review.py` 19.6 s.
- `stmt_diff_vs_3e8b5c6.json`: changed statements and displays (Sept normalizer).
- `hist_gate_head.json` (FAIL, unpatched), `hist_gate_head_patched.json` (PASS with T1's filter).
- `cache_check_oldhost.json` (PASS, `$H`), `cache_check_newlake.json` (FAIL, main repo `.lake`).
- `clone/BFGS-non-smooth`: scratch commit `8cdc06e`; `dry_package.json` (PASS, 17 s, 154,641,216 B,
  4904 members); `dry_validate.json` (validator stopped before Lean: documents byte- and
  pixel-identical, companion check PASS, 13 Sep correspondence FAIL, cache checks PASS, extraction
  removed; 40 s).
- `cov_*.txt`: coverage check outputs at HEAD.
