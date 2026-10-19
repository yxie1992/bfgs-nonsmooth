# M44: confident authorial wording — checkpoint, 18 October 2026

**Paused at the author's request. M44 is not complete.** Start with
[RESUME.md](RESUME.md). All necessary decisions, proposal inputs, scripts, logs,
baseline PDFs and the post-edit TeX snapshot are saved under this directory;
resuming must not depend on the previous conversation or on `/tmp/opencode`.

## Request and scope

The author asked to change defensive or over-qualifying writing in **both** the
article and companion, keeping a qualification only when it addresses a common
misunderstanding and helps a reader. In particular: be confident, promote the
contribution, and write as authors rather than critics. This has priority over
the pending M43 narrative reorganization. The verbatim instruction is preserved
in [checkpoint/companion/BRIEF.md](checkpoint/companion/BRIEF.md).

The pass removes redundant disclaimers and guard words, states contributions
and attributions directly, and collects recurring scope points in one place.
Hypotheses, conclusions, proved negative facts, open questions and explanations
of why the counterexamples evade positive theorems are retained. Prior results
are still attributed to their authors. The AI-use paragraph is left for the
author (Q1), not silently rewritten as part of this pass.

## Exact stopping point

| Unit | State |
|---|---|
| Article wording | Applied in 12 TeX files; 71 initial edits and the recorded small follow-ups. |
| Generated companion chapters | Applied through the generator: 299 logged data-file edits, chapter introductions, Chapter 14 title, and deletion of the repetitive relation-to-literature preface. |
| Hand-written companion files and bibliography | Applied; AI-use paragraph unchanged. |
| Shared seed appendix | Regenerated from the revised article appendix. |
| First register resync | **Applied once** to 30 registered edited TeX files; 20 reviewed mechanical hashes accepted. Do not repeat it. |
| Prose-item actions | Encoded and dry-run only. **`apply_actions.py --write` has not run.** |
| Notes, docstrings, current correspondence/ledger | Unfinished. |
| Post-edit PDF builds, visual review and warning comparison | Not run. Baselines are saved. |
| Post-edit Lean build, axiom audit and kernel replay | Not run. Old reports remain evidence of their old source commit only. |
| Release archive | Untouched; this checkpoint is not a release. |

The action dry run covers 477 unique items: 205 re-anchors, 140 keeps and 132
retirements, plus four new prose items. It finds **zero missing new anchors and
zero missing `of` targets**. Six Lean docstrings will need explicit repair after
the retirements. These are plans, not already-applied register changes.

## Checks actually run at the checkpoint

- `generate_companion.py --check`: PASS, 17 managed outputs; 14 chapters, 172
  source spans, 3087 preserved formal exports.
- `check_coverage.py --strict`: exit 0, the existing 2529 items. **This does not
  establish that the prose migration is complete:** this checker does not test
  anchors against their text; the old anchors and deleted-sentence items remain
  until the action pass is written.
- Lexical comparison of all 28 changed Lean files against `66de81d`: the code
  outside comments is identical. The changes so far are line references in
  comments/docstrings; no Lean declaration or proof has changed. This is not a
  new compiler run.
- The portable register-action dry run passes its anchor/target checks. Its six
  expected stale docstring citations are listed in `RESUME.md` and its log.

Logs and inputs are inventoried in
[checkpoint/MANIFEST.json](checkpoint/MANIFEST.json). The machine-readable state
is [checkpoint/STATE.json](checkpoint/STATE.json).

## Files

- [companion_edits.json](companion_edits.json): the **production input** read by
  `editorial/generate_companion.py`. Keep this file when moving the work.
- [RESUME.md](RESUME.md): ordered next steps and the remaining note/docstring
  decisions, with exact commands.
- [UPDATE_4350777_66de81d.md](UPDATE_4350777_66de81d.md): the requested overview of
  the MacBook changes pulled on 18 October, still owed in the final task report.
- `checkpoint/reg/apply_actions.py`: portable, one-shot action script; default is
  a dry run, `--write` applies. Its required inputs are included locally.
- `checkpoint/reg/action_report.json`: the action plan and retired-item records
  from the dry run, including the original coverage and references.
- `checkpoint/companion/proposals_{A..F}.json`: the six proposal groups, with the
  per-proposal register decisions. These are historical inputs; final wording
  and override texts are in the production data file.
- `checkpoint/handwritten/apply_handwritten.py`, `checkpoint/article_edits.json`,
  `checkpoint/apply_article_edits.py`: records of edits already applied. **Do not
  rerun their write modes.** Some archived exploratory helpers retain their old
  absolute scratch paths; the portable action script is the resumption entry.
- `checkpoint/resync_{dry2,write1}.txt`: full first-resync reports, including all
  accepted mechanical IDs, edited references and the one lost reference.
- `checkpoint/snap1/`: the 30 TeX files at the already-applied resync. A later
  source edit can be resynced using this as `--base-dir`, rather than applying
  the original line mapping a second time.
- `checkpoint/baseline/{paper,companion}.pdf` and `.log`: before-M44 builds at
  `66de81d`; `baseline/tex/` preserves their TeX inputs.
- `checkpoint/checks/`: actual checkpoint logs and a repeatable comment-only
  Lean-source comparison.

The pre-edit source base is
`66de81d3d80183effb245863cc4fd58792a29899`, not whatever `HEAD` becomes after this
checkpoint is committed. `release/` and the earlier audit/review records are
historical and must not be relabeled as fresh evidence.
