# Resume M44 without conversation history

**18 October 2026. Paused, not finished.** Read `AGENTS.md`, the active-checkpoint
section at the top of `HANDOFF.md`, and this file. Paths below are relative to
the repository root. No previous chat, agent session, temporary directory or
external service is needed to understand the checkpoint.

## 1. Established state; do not redo

The repository was pulled from `4350777` to
`66de81d3d80183effb245863cc4fd58792a29899` (45 MacBook commits). Its main library,
pins, toolchains and Lake manifests were unchanged. The Linux package build,
strict coverage and generator checks passed before M44. The historical
package-wide evidence is at `74900ef`: 5506 audited declarations, 786 replayed
project modules, standard axioms only. This is **not** evidence of the current
edited sources.

Applied M44 changes:

1. Twelve article files: `paper/master.tex`; sections `introduction`, `geometry`,
   `energy`, `global`, `local`, `failure`, `verification`; appendices
   `hypothesis_examples`, `lower_curvature`, `planar_geometry`, `seed_certificate`.
   `checkpoint/article_edits.json` records 71 initial replacements. The final
   source diff against `66de81d` is authoritative for the follow-ups: the centered
   theorem's two summands need not separately attain their minima at its center;
   failure prose/010 now points forward to the positive-lower-curvature theorem.
2. The companion generator reads `companion_edits.json`: 299 edits, from 298
   original proposals minus D-07H-14 plus two coordinator GL/LO attribution
   replacements. Overrides B-04R-10, C-05G-08 and E-14E-25 are already in that file.
   Nine chapter introductions and the Chapter 14 title were revised; the common
   bibliographic-disclaimer sentence was deleted from 13 chapter endings.
   Chapters were regenerated; do not edit generated TeX by hand.
3. Hand-written `companion/{research_story,master,current_verification,
   correspondence,bibliography}.tex` were revised. RS1, MS1, CV1, CR1 and the
   bibliography header were hand edits; the remainder is in the archived
   `checkpoint/handwritten/apply_handwritten.py`. The AI-use paragraph is
   deliberately unchanged. The article bibliography had only access comments,
   not rendered access disclaimers, so no bibliography edit was needed there.
4. `prepare_shared_appendix.py` regenerated the companion seed appendix.
5. **One resync write has run**, for 30 registered edited TeX files, with all 20
   reviewed wording-only hash changes accepted. Full output:
   `checkpoint/resync_write1.txt`; post-edit TeX snapshot: `checkpoint/snap1/`.
   This changed register lines/hashes and Lean comment references, but **not**
   anchors/statuses/retirements. Do not rerun the original resync, even if a later
   commit makes its dirty-tree guard accept it.

The old dry run reported 338 ANCHOR, 725 EDITED, 20 CHANGED, 28 LOST, 41 EDITREF
and one LOSTREF. The exact IDs are in `checkpoint/resync_dry2.txt`. No mechanical
item was added, removed or renumbered.

## 2. Immediate next action: write the prepared register migration

The canonical script is **inside this repository**, not `/tmp`:

```sh
python3 editorial/defensive_wording_20261018/checkpoint/reg/apply_actions.py
# Read its plan, then, ONCE:
python3 editorial/defensive_wording_20261018/checkpoint/reg/apply_actions.py --write
```

**The write command above has NOT been run.** Default execution only writes its
report, not registers or Lean files. The script locates the repository relative
to itself and refuses to proceed if any of the 30 edited TeX files differs from
the saved resync snapshot. It also refuses missing anchors/`of` targets. After
its write, do not run it a second time; the retired IDs will already be absent.

The reviewed decisions are executable in the script and readable in
`checkpoint/reg/action_report.json`: 477 unique affected items, comprising 205
re-anchors, 140 keeps and 132 retirements. Duplicate proposal decisions are
merged, and final-text overrides are included. Existing mathematical
declarations must remain, even when their prose item is retired.

Four additions are prepared:

| Item | Classification |
|---|---|
| `A/verification/prose/031` | SAME_AS both local-failure theorems: the failing starts form a sequence. |
| `C/01_I/prose/162` | NON_CLAIM: certificates/frames/comparison energies are proof devices. |
| `C/09_C/prose/118` | NON_CLAIM: description of the curved-interface convergence proof. |
| `C/07_H/prose/081` | SAME_AS `C/07_H/prose/011`: the many-piece infinite-run value conclusion. |

The dry run has zero missing anchors and zero broken `of` targets. It also
corrects 52 surviving-anchor line ranges. The planned total after retirement
and addition is 2401 items; **do not publish that count until the final checks**.

Important prepared reclassifications/references:

- `A/failure/prose/010` becomes SAME_AS
  `A/negative_lower/theorem/art:local-failure-lower`; it is now a forward pointer,
  not the former no-uniform-lower-curvature claim.
- `C/13_L/prose/001` points instead to `C/12_D/prose/047`, which still covers
  `Failure.no_uniform_lower_curvature`.
- `C/06_F/prose/040` becomes SAME_AS `C/06_F/prose/042` (initial-matrix-dependent
  matrix limits).
- `C/research_story/prose/017` becomes SAME_AS `C/07_H/heading/001` (Theorem 7.A).
  Keep `ResearchStory.value_convergence_unbounded_iterates` as an example, not as
  a proof of the new sentence.
- `Ch12D.starts_null` is added to the Lean list of `C/12_D/theorem/D:main` to keep
  the proved fact after retiring `C/12_D/prose/008`.
- Overrides: C/04_R/053 says “supporting errors repeat”; C/05_G/046 is re-anchored,
  not retired; C/05_G/047 uses “needs neither continuity nor boundedness”; C/14_E/047
  states arbitrary finite dimension. D-07H-14's register action is retained.

## 3. Required hand fixes after the migration

### Six docstrings citing retired items

These are expected dry-run findings, **not** current compiler errors. Drop or
repoint their Item/file citation, keep every theorem and proof:

| Coverage module | Old item |
|---|---|
| `Article/Energy.lean` | `A/energy/prose/035` |
| `Article/Failure.lean` | `A/failure/prose/009` |
| `Article/HypothesisExamples.lean` | `A/hypothesis_examples/prose/006` |
| `Article/Local.lean` | `A/local/prose/015` |
| `Article/Verification.lean` | `A/verification/prose/022` |
| `Companion/Ch12D.lean` | `C/12_D/prose/008` |

The module paths above are under `bfgs_lean_article/BfgsArticle/Coverage/`.
`ResearchStory.lean` also needs its module-docstring section about the old RS3
sentence and the docstring of `value_convergence_unbounded_iterates` rewritten:
keep the exponential-objective example, remove the obsolete quote and Item
association. `Article/Failure.lean`'s discussion of old prose/010 must reflect the
new forward pointer, not confuse it with the retained no-lower-curvature theorem.

### Stale quotes and explanations

The action script appends proposal notes; it does not fully rewrite the earlier
notes/reasons. Do the following reading pass. Numbers below are old approximate
Lean line numbers, so search by theorem or item rather than using them blindly.

- Article: update `Local.lean`'s quotes around
  `quadratic_max_no_polyhedral_cells` (~774–786); remove the deleted methodological
  clause from `A/lower_curvature/prose/037`'s note. Repair the sole LOSTREF:
  `A/geometry/prose/029` cites deleted `local.tex:136`. Fix the C_09_C note citing
  `A/local/prose/043`, `local.tex:439-440` and the nonlinear-coordinate clause.
- `Ch05G.lean`: introduction (~62, 363, 2891), `psd_seminorm_triangle` (~1219),
  `limiting_gradients_at_kink` (~1580), `accessible_span_differs` (~1683),
  `small_crossing_no_certificate` (~2062).
- `Ch06F.lean` (~689); `Ch10Q.lean` (~2086, 2339, 2440).
- `Ch07H.lean`: `ZeroValueIterateQuestion` (~443), `alternative_arrangement`
  (~1054), `tilt_model_gradients` (~1352), `two_piece_finite_termination` (~1360),
  `TiltNoInfiniteRunQuestion` (~1674), `no_stationary_point` (~2205).
- `Ch11U.lean`: `smooth_hyperplane_witness` (~2331).
- `Ch09C.lean`: prose/066 (~3836), prose/094 (~4319), prose/101 (~4443–4445).
  Prose/101's last conjunct already proves convergence on the quadratic example.
- `Ch14E.lean`: title in its module docstring, prose/067 (~139), prose/076 (~186).
  Keep its explicitly historical record at ~42–43 unchanged.
- `Ch12D.lean`: ~514, 554, 1204, 2239, 2303, 2631. The M14 resolved-discrepancy
  history stays historical. `Ch13L.lean`: `local_failure` (~437–446),
  `not_four_C2_branches` (~649), `FourC2BranchLocalFailure` (~659).

Register reasons/notes to reread (all IDs here have `/prose/` unless stated):

| Register | Items |
|---|---|
| C/01_I | 005, 026, 028, 029, 057, 112, 122, 133, 134, 135, 153, 156 |
| C/03_T | 021 |
| C/04_R | 102 (old attribution-check wording), 103–104 |
| C/05_G | 002, 052, 077, 082 |
| C/06_F | 001, 006, 028, 033, 039, 063, 064, 067 |
| C/07_H | 001, 033, 045–046, 072–073; disp/027 |
| C/08_A | 005, 027, 032, 050 |
| C/09_C | 070, 081, 105 |
| C/10_Q | 001–002, 048, 055 |
| C/14_E | 013, 084, 087–088 |
| C/research_story | 017, 024, 036 |

Particular obsolete references: C/01_I/029 cites retired 145 and quotes the old
four-C² question; C/01_I/026,135 and C/14_E/013,088 name retired C/13_L/044;
C/14_E/087 names retired C/07_H/012; C/14_E/088 names retired C/12_D/008.
C/01_I/057 remains NON_CLAIM (a question in prose, not a newly authored Lean Prop).
The H introduction no longer quotes the two retired scope items 012 and 019.

Regenerate the 95 flagged proposal notes by inspecting their `register[].note`
for `reason|docstring|\.lean|quote|obsolete|update|needs|NEW SENTENCE|should|cited by|referenc|COORDINATOR|reword`.
Search every retired ID from `action_report.json` in current registers, Lean
docstrings and current editorial JSON. Historical reviews, release records,
resolved discrepancies and this checkpoint may intentionally quote retired IDs;
do not erase history to silence a global grep.

Review all 41 EDITREFs in `resync_write1.txt`, not just the LOSTREF. Examples:
the local theorem wrappers cite the edited end of `failure.tex`; Ch06F/Ch10Q
references to proof ranges; C/01_I/024 to the Chapter 13 root; C/14_E/050 and 067;
Ch03T to the adjacent-degree hierarchy; Ch11U to the radial example. Resync moves
references, but does not decide whether their quoted claim still matches.

After the hand fixes, synchronize changed Item/file ranges with
`resync_register.item_ref_edits` if needed. A docstring's file range must equal
its register item's range. Independently check anchors **inside their ranges**;
`check_coverage.py --strict` alone does not do this.

## 4. Finish validation, correspondence and records

1. Compile affected coverage modules and run the full package build, following
   `AGENTS.md` (one Lean process per agent; never `lake update`, never touch the
   hash-pinned `bfgs_lean_stage1`). Strict coverage must pass without
   `--allow-discrepancies`; run the companion generator check again.
2. Refresh current correspondence **after** register prose ranges are final:

   ```sh
   python3 editorial/release_20261015/refresh_correspondence.py --propose > /path/to/scratch/m44_propose.json
   # Review and fill the M44 rows in CHANGES.json, including anchor changes.
   python3 editorial/release_20261015/refresh_correspondence.py --write
   (cd editorial && python3 assemble_claim_ledger.py)
   python3 editorial/release_20261015/refresh_correspondence.py --check
   ```

   Renew `editorial/main_results_scope_20261016/ADDITIONS.json`: raw hash of
   `hypothesis_examples.tex`, and the raw geometry-scope passage hash/coverage
   list (remove retired `A/geometry/prose/059`). Keep the hard-coded start/end
   anchors in `editorial/coverage_additions.py`: “Checking the hypotheses”, the
   local “actual witnesses” tail, and the Chapter 7 existence passage. M44 did
   not alter the latter two passages. Add/renew root rows for research-story
   RS2/RS3/RS5/RS6/RS7 and Chapter 13 F-13L-17. The root paragraph now calls the
   quadratic-plus-maximum example a global failure. Do not reattribute a
   positive-Armijo-parameter scalar theorem to Lewis–Overton.
3. Build both PDFs. Baseline PDFs/logs are in `checkpoint/baseline/`. Use the
   reproducible `latexmk` invocation in `AGENTS.md`; compare per-page text with
   PyMuPDF, render every changed page at 110 dpi and actually inspect the images.
   Compare warnings, overfull boxes and undefined references against baseline.
   The old `/tmp/opencode/m44/venv` may disappear; recreate a PyMuPDF environment
   if needed. `editorial/check_documents.py` additionally needs `pdfinfo`, which
   was absent on this Linux host.
4. Obtain independent review of the final wording, coverage and correspondence
   as appropriate under the project's reviewer/fix-pass workflow. Do not treat
   proposal validation or the dry-run anchor checks as that final review.
5. Produce fresh package-wide axiom audit and kernel replay on the final clean,
   committed source, writing reports outside the repository before copying in.
   Use lean4checker **v4.19.0** (rebuild if the old temporary checkout is gone),
   run its self-test, and keep the 182-name principal guard unchanged. Commands
   are in `HANDOFF.md`, `AGENTS.md`, and `bfgs_lean_article/README.md`.
   Determine the current counts before final source-bound evidence: the literal
   “checked 5506 Lean names” and “(786 modules;” in current_verification were not
   altered during this wording pass. If the counts need changing, carry that
   edit through its register too, and ensure the final evidence binds the final
   inputs rather than an earlier text. Do not present old audit reports as new.
6. Close M44 only after these checks. Update its final counts/evidence in the
   README, TODOs and HANDOFF; regenerate ledger/HTML as needed; commit and push.
   The archived 15 October `release/` remains historical. A full new release
   run is separate work and requires the Mac-specific release host.

## 5. Checkpoint integrity and housekeeping

Before resuming, the saved inputs and paused working-file fingerprints can be
verified without any network or temporary-directory access:

```sh
python3 editorial/defensive_wording_20261018/checkpoint/checks/verify_checkpoint.py --working-tree
```

After intentionally resuming/editing, `--working-tree` will naturally cease to
match; the checkpoint asset hashes remain a record of the paused inputs.
Archived diffs, logs and source snapshots preserve their original bytes,
including diff-context spaces and inherited trailing whitespace. A blanket
`git diff --check` over these newly archived files reports that whitespace;
do not rewrite the byte-preserved evidence to silence it. The production-source
and new documentation changes pass the check when the checkpoint archive is
excluded.

Current actual results are in `checkpoint/checks/`: strict coverage exit 0 on
the **old** 2529 items, generator PASS, and a comment-only comparison for all
28 changed Lean files. There has been no post-M44 build, PDF inspection, audit,
kernel replay or refreshed correspondence. No background work was started for
this pause.

The action script's source snapshot and all its JSON inputs are saved locally.
Other archived exploratory helpers may retain hard-coded `/tmp` paths and
`git show HEAD`; use the explicit baseline `66de81d` when reusing them. Neither
the already-applied article/handwritten scripts nor the original resync should
be rerun. If further TeX edits are needed before completing this migration,
review and resync only the incremental change using `checkpoint/snap1` as the
base, then update the snapshot/plan deliberately.

The outstanding summary of the pulled MacBook changes is saved in
`UPDATE_4350777_66de81d.md`. Include that overview in the eventual user report,
unless the author asks for a narrower response. M43 remains pending the author's
choice of narrative stage; do not silently start its structural reorganization.
