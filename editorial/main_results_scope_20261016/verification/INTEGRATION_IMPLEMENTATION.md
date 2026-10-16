# M42 editorial infrastructure — final report

**Ready for independent review.** Baseline:
`61453638c9e86c7fce2cba0078da9fa0fe6f0e16`. Date: 16 October 2026.
Implementation is in R (`/Users/yxie/Projects/bfgs-nonsmooth`); all writing
commands/tests ran only in this scratch directory's `clone/`.

## Exact files changed in R

| Path | Change |
|---|---|
| `editorial/assemble_claim_ledger.py` | Validate additions, append current-coverage article records, render their actual declarations/proof provenance; retain historical index/export handling. |
| `editorial/coverage_additions.py` **new** | Shared explicit manifest, active-source and strict coverage/relationship gate; current-package signature preference; new records and receipt evidence. |
| `editorial/release_20261015/refresh_correspondence.py` | Explicit additions units/proposals and M42 rows; retain snapshot, bounded-field, export, normalization, overlap and receipt guards. |
| `editorial/release_20261015/README.md` | Document additions, current receipt versus archived release, bounds and integration instructions. |
| `editorial/main_results_scope_20261016/ADDITIONS.json` **new** | Safe **empty** authorization template, with fixed baseline/revision/M42 metadata. |
| `editorial/main_results_scope_20261016/INTEGRATION.md` **new** | Design limits and exact coordinator commands for manifest, CHANGES, write/ledger/check and audit-boundary verification. |

Final hashes of these six files are in `CHECKSUMS.json` beside this report.
The three runtime Python files in R are byte-identical to those exercised in the
scratch clone. Python syntax checks and owned-file whitespace checks pass;
`git diff --check` on the tracked owned paths passes.

No TeX, Lean, registers, TODOs, HANDOFF, AGENTS, generated ledger/HTML, existing
CHANGES/receipt/component JSONs, release files, stage1, or `verify_release_inputs.py`
were edited by this agent in R. No git add/commit/checkout/push, Lean or lake ran
in R; no Lean/lake ran anywhere. The coordinator's concurrent work is untouched.

## Design and retained boundaries

1. **Explicit authorization.** The manifest lists exact new active input paths
   with full raw-file SHA-256 and every new label with its file. It is compared
   against the actual input graph and fixed M42 baseline. Old inputs/labels
   cannot disappear or move; inactive/unlisted inputs or labels fail. New inputs
   must also be in `extract_items.ARTICLE`.
2. **Current coverage, not row existence.** The shared helper invokes the existing
   strict checker and verifies current mechanical hashes/lines/placement, prose
   anchors, final statuses, reference closure/cycles, declaration lookup and
   module ownership. New named proved results require `LEAN` and a theorem in
   their coverage module. Their following source proof must be `PROOF` of that
   exact statement. Definitions require `DEFINITION`. A new unattached proof is
   refused. All mechanical and registered prose items of affected files are
   checked, not merely the statement row.
3. **Reviewed change units.** New named statements, proofs, displays (including
   unnumbered ones) and the complete new input require CHANGES rows citing M42
   and current coverage. New/changed displays in old inputs are detected against
   the M42 base, even outside an old mapped passage. A changed old unnumbered
   display conservatively becomes a newly checked current-coverage unit. Old
   display removals are refused. The complete-input row plus raw manifest hash
   prevents an unlisted prose edit from passing with `--write` alone.
4. **Historical evidence stays historical.** New claims add no component-review
   rows, September spans, or September export sets. The old `assert_bounded`,
   `assert_exports`, snapshot/git-blob checks, whole historical appendix checks,
   macro checks, TeX token-aware normalization and coverage-overlap checks remain.
   The original 77 rows still match when their text is unchanged. Current
   component source hashes/locations may refresh as before.
5. **Fresh provenance.** New ledger records carry current TeX/proof locations and
   hashes, coverage item/status/hash, registered Lean statements and actual source
   hashes. Package citations prefer current `.lean` text over any old audit
   signature. SF6's real provenance for sealed/supplement/audit signatures is
   preserved; the legacy index is not relabeled. New records have status
   `CURRENT_COVERAGE_SOURCE_CORRESPONDENCE`.
6. **Audit guard.** New records have empty `source_spans`, their registered names
   in `full_formal_exports`, and **no `principal_exports`**. `ledger_names()` sees
   their cited names, all of which are already collected by `coverage_names()`.
   The union of legacy principal names and `PACKAGE_PRINCIPAL` remains exactly
   the existing **182** names in `BfgsArticleAxioms.lean` (tested).
7. **Receipt versus release.** The current October receipt also pins the helper,
   coverage index/checker, additions manifest, checked registers and cited Lean
   declaration sources. A new `--write` refreshes this current receipt and the
   bounded component fields. The Oct15 commit/archive receipts and `release/`
   remain historical; this work performs no release/repackaging.

These are textual source-correspondence checks. They do not discover every prose
assertion, establish TeX/Lean semantic equivalence, verify full joint hypotheses,
elaborate imports, or check proof terms/axioms. Independent mathematical coverage
and row review, the real package build, axiom audit and kernel replay retain those
roles. The source-text signatures retain the existing coverage index's section
variable/open-namespace conventions. The assembler validates coverage separately
from the October checker's CHANGES/receipt validation; the coordinator runs both.

## Checks and negative-test matrix

**115/115 checks passed:** `run_tests.py` = 103, completed before the server
restart and not repeated afterwards; `extra_tests.py` = 12 targeted checks of
previously untested display/guard edges. Totals: 21 successful command checks,
76 expected command rejections, 18 explicit invariant assertions. Results:
`TEST_RESULTS.json`, `EXTRA_TEST_RESULTS.json`, `tests.log`, `logs/`.

The scratch `.lean` fixtures supplied textual declaration lookup only; they were
**never compiled or kernel checked** and are not evidence for any article claim.

| Area | Cases and outcome |
|---|---|
| Empty manifest / old sources | `--propose`: exactly 77 matching rows, no stale/uncovered/unresolved rows. Old receipt correctly stale after tooling edits; fresh write/check pass. Ledger, HTML and component reviews byte-identical to baseline. Repeated write/assembler deterministic. |
| Explicit toy appendix | Proposition/lemma, proofs, labeled and unnumbered displays, section anchor, prose; strict coverage, propose/write/ledger/check pass. Two new ledger records have current declarations/proof locations/hashes; every old article record remains identical. Component reviews change only the active master-file hash. |
| Inputs/labels | Unlisted active input, unlisted named claim (new or old input), inactive declared input, unindexed new input, removed old input, removed/renamed old label: rejected by both entry points. |
| Coverage completeness | Missing register, missing/wrong mechanical hash, missing/TODO status, named result downgraded to NON_CLAIM, missing target, cyclic relationship: rejected. |
| Actual proof/declaration link | Wrong proof target, foreign first name, unresolved name, forged foreign coverage module: rejected. Unassociated new proof: rejected. |
| CHANGES requirements | Drop a new statement/display/proof/input row; omit M42; alter status/hash; empty principal list; cite reachable supporting name but omit governing coverage declaration: rejected. |
| Whole-input prose | Unlisted prose edit rejected with stale manifest; after updating only the manifest hash, still rejected by the stale complete-input row. |
| Old-input unnumbered display | Appended display outside every old unit, with complete current coverage: rejected until its explicit M42 row is installed; proposal, reviewed write, ledger and check then pass. Old unnumbered display removal rejected. |
| Original T4 negative guards | Unlisted old statement/macro edit, changes to either complete historical appendix, control-word merge, dropped old proof/appendix/macro rows, wrong before/coverage hashes/type/principal, coverage outside unit, own proof item omitted, only untouched coverage cited, unknown correction id, scope_review on non-root, changed baseline snapshot: rejected. |
| Binding/provenance | Changed component output, pinned checker/helper, or cited Lean source makes `--check` fail. Rebuilding the ledger after a source signature edit reads the new signature. Artificial stale package-index entry is filtered without mutating the legacy index. |
| Compatibility/limits | 182-name guard exactly equal to pinned file; every new name in full audit/register collection. Control-word/control-space normalization pairs preserved. `python -O` refused by T4. An existing but irrelevant correction id on an old row remains a documented human-review issue. |

## Pending real manifest configuration and coordinator commands

The real appendix was read only to confirm compatible source shape: the six
intended results each have a following proof in the same input. As the coordinator
reported, the active input and `extract_items.ARTICLE` entry are already added.
The real `A_hypothesis_examples.json` and coverage module are pending; no test
assumes that they exist yet. The manifest therefore remains empty intentionally.

After final TeX/coverage, the expected labels are the six supplied by the
coordinator, plus the section label (and any further display labels actually
present at that time):

- `art:examples-mixed`
- `art:examples-full-rank`
- `art:examples-run-existence`
- `art:examples-two-quadratics`
- `art:examples-nonradial-runs`
- `art:examples-no-step`
- `art:hypothesis-examples`

They map to `paper/appendices/hypothesis_examples.tex`. Use its **final** raw
SHA-256. No placeholder declaration names or theorem labels were installed.

Exact manifest-install and reviewed-row merge commands are in
`editorial/main_results_scope_20261016/INTEGRATION.md`, sections 1–4. Core sequence,
from the repository root after the real coverage is complete:

```sh
python3 editorial/lean_coverage/check_coverage.py --strict
S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/integration
python3 editorial/release_20261015/refresh_correspondence.py --propose > "$S/m42-propose.json"
# Review/install coverage_additions.proposed_manifest using INTEGRATION.md §2.
python3 editorial/release_20261015/refresh_correspondence.py --propose > "$S/m42-reviewed-rows.json"
# Independently review/merge uncovered and stale rows using INTEGRATION.md §3.
python3 editorial/release_20261015/refresh_correspondence.py --write
(cd editorial && python3 assemble_claim_ledger.py)
python3 editorial/release_20261015/refresh_correspondence.py --check
```

For stale old rows retain their ids and earlier correction items, adding M42 for
the new edit. New row skeletons already suggest M42. Proposal mode is read-only
and intentionally can describe incomplete/unapproved additions; it is not a
successful verification. Final build/audit/replay and PDF inspection are the
coordinator's separate tasks. The guard check command is in INTEGRATION.md §4.

**Blockers:** no infrastructure blocker found. Final real-source integration is
intentionally pending the real coverage, reviewed manifest/rows, and independent
review/fix pass. The existing current receipt will remain stale until the
coordinator's authorized `--write` after those inputs settle.

## Fix pass

16 October 2026. Implemented the coordinator's acceptance of **I1, I2, I3, S1,
S2 and O1**, after reading the independent review in full, both prototype diffs
and all associated tests. The original findings are preserved verbatim in
`editorial/main_results_scope_20261016/verification/INTEGRATION_REVIEW.md`, with a
provenance header and appended dispositions. The original review's SHA-256 is
`ea742723f620b4576874fadcf9cb5f21572314ebc08c1c04337de38aa143414a`;
the embedded original body was byte-compared successfully.

### Changed paths

The original six paths above, plus these two explicitly authorized files:

- **New** `editorial/lean_source.py`: lexical public declaration and complete
  current statement lookup.
- **New** `editorial/main_results_scope_20261016/verification/INTEGRATION_REVIEW.md`:
  preserved review and fix dispositions.

`ADDITIONS.json` is now an **empty schema-v2** template, with `active_inputs`,
`labels` and `passages` all empty. The real manifest/table and generated outputs
were not installed in R. The frozen/shared `active_tex_sources.py`, extractor,
registers, TeX, Lean, root imports, TODO/HANDOFF, existing CHANGES/receipt/ledger,
release and stage1 files were not edited by this agent. No git mutations in R;
no Lean/lake anywhere. All writing runs used fresh clones under `integration/fix/`.

### Production fixes

| Finding | Implemented behavior |
|---|---|
| I1 | Shared canonical TeX guard runs for the literal document graphs before treating them as complete. Noncanonical input/include/label/begin/end spellings, unbraced/dynamic arguments, unsupported starred claim environments and TeX character translation are rejected. The existing companion `StartModule` label template is accepted only on its exact fixed-baseline definition line. The frozen resolver is unchanged. |
| I2 | Track the loaded register path and require canonical path/module ownership for every recursively visited item, not merely the initially selected files. Sources must be active indexed document inputs. |
| I3 | Mask nested Lean comments, strings and characters; distinguish namespace and section scopes; resolve public qualification including `_root_.Name`; refuse private or unsupported/generated names. Extract complete headers through balanced binders and simple type-level lets, and complete definition/structure bodies. Current statements are fed to the existing renderer with real file/line provenance, then explicitly marked `statement`; the sealed index is unchanged. The existing strict checker's structural rules remain, using the lexical source-name callback for additions. |
| S1 | `unit_hash` uses raw file SHA-256 for new complete-input rows and raw byte-slice hashes for explicit passages. Every historical unit retains its previous normalization. Comment/newline and CRLF changes now stale these raw rows even after manifest-only hash updates. |
| S2 | Explicit passage schema and required M42 change rows cover the geometry/local tails and the Chapter 7 existence caveat. Boundaries are uniquely anchored; paths are existing active indexed sources; every overlapping registered prose item must lie in the passage, have its anchor there, and be listed. Its whole file and reference closure are checked. A row must cite all and only those current prose items. |
| O1 | Both proposal levels report `status: "PROPOSAL"`, `verification_performed: false`; exit 0 is proposal generation, not coverage verification. |

The production parser supports the actual type-level `let` in
`quadratic_history_decrease` and the full structure-valued `Quadratic.run`
definition. The conservative prototype alone would not have sufficed for those
production shapes. No synthetic fixture behavior was installed as production
evidence.

### Tests and outcomes

**188/188 matched checks:** 58 accepted command checks, 101 expected command
rejections, 29 invariant assertions. Scripts and artifacts:

- `fix/test_fix.py`, `fix/resume_tests.py`, `fix/finish_tests.py`,
  `fix/final_grammar_tests.py`;
- `fix/FIX_RESULTS.json`, `fix/SUMMARY.json`, `fix/logs/`;
- initial traces/results retained as `FIX_RESULTS_INITIAL.json`,
  `FIX_RESULTS_PRE_FINISH.json`, `test_fix.log`, `resume_tests.log`;
- `fix/PRODUCTION_INPUTS.json`: hashes of the captured real production sources;
- `fix/CHECKSUMS.json`: final eight owned-file hashes;
- persistent `fix/fixture/` and `fix/production_fixture/` checkpoints.

The fresh clones started at `1ef18d9c64a11f281a9f14950ca420a468782105`.
The production clone received hash-recorded copies of the coordinator's real
appendix, geometry/local additions, coverage files, generator outputs and Chapter
7 caveat. Its proposal found **77 matching historical rows and 26 new units**,
including exactly the three requested passages. Production write/assembler/check
passed, with the six intended new article records. The Chapter 7 passage included
exactly `C/07_H/prose/076`–`080`.

| Check group | Outcome |
|---|---|
| Historical/ordinary compatibility | Empty-manifest ledger/HTML/component bytes identical; 77 rows unchanged; normal toy addition and deterministic repeat write/assembler pass. |
| I1 | Spaced/newline/unbraced inputs and includes, noncanonical label/begin/end, starred claims, `@` filename spelling, character translation and altered companion label template reject through both entry points. Commented input syntax remains harmless. |
| I2 | Forged transitive module and renamed transitive register reject; correctly owned closure write/assembler/check passes. |
| I3 negatives | Nested-comment/string/raw-string fake declaration, private name, unclosed comment, wrong anonymous-section qualification, indented scope, bare `_root_` namespace, unsupported type-level tactic, command quotation, repeated same-line attributes, unknown column-zero commands and inline/wrapped scope commands reject. |
| I3 positives | Default binder, type-level let, correctly qualified anonymous-section declaration, absolute declaration/namespace restoration and a header beyond 80 lines pass with complete current source statements. Real core/article/companion shapes pass. |
| S1 | Input row equals the full raw file hash; comment/newline and CRLF changes require re-review; manifest-only update does not suffice; re-reviewed row write/check passes. |
| S2 | All three undeclared passages/missing rows reject; stale raw passage, manifest-only rehash, omitted authorized/row prose, non-M42 row, duplicate anchor, arbitrary/traversing path and non-final coverage reject. |
| Old guard regressions | Unlisted old statement/macro, control-word merge, edits to either complete historical appendix, dropped old proof/appendix/macro rows, outside-unit citation, stale coverage hash, unknown correction, snapshot tampering, removed old input/label, unlisted new claim, bad proof target, missing hash, TODO and optimized T4 execution reject. |
| Provenance/audit | Every sealed-index declaration record compared with the historical ledger is identical. New names enter the complete audit through registers; new article records have no principal exports. The principal guard is exactly the existing **182** names. |
| Determinism | Production write/assembler repeated under different Python hash seeds is byte-identical. Final production `--check` passes. |

Two harness diagnostics were refined after correct early rejections: deleting a
theorem label hit the unlabeled-statement guard before the expected old-label
message; omitting the open-question prose citation left an unreachable principal
name, so the fixture was adjusted to isolate the new all-prose-items guard. No
production check was weakened. Passed cases were retained and only the remaining
work resumed. The final results have no unmatched expectation.

The final runtime Python files in R equal those in both tested clones. Syntax,
owned-file whitespace and tracked `git diff --check` checks pass. These are
source-tooling tests; neither fixture nor production mathematical proof terms
were compiled, audited or replayed by this agent.

### Supported grammar and remaining limits

- Literal, adjacent, braced TeX input/include/label/begin/end forms with the
  documented literal argument sets. General macro/conditional/catcode execution
  is outside this inventory. The fixed baseline companion label template is the
  narrowly bound existing exception; `^^` translation is refused.
- Current Lean declarations and namespace/section/end commands start at column
  zero. Ordinary/raw strings, character literals, nested comments, named and
  anonymous/noncomputable sections, public `_root_.Name` qualification, ordinary
  declaration modifiers, single-line attribute lists (one per line), balanced
  headers, default binders and simple type-level lets are supported. Definition
  bodies/`where` fields are retained without an 80-line cap.
- Indented declaration/scope commands, quoted identifiers, bare `_root_`
  namespaces, quotations, interpolated strings, multiline/repeated same-line
  attributes, mutual blocks, command-generating macros/elaborators/exports, unknown
  column-zero commands or identifier-led unindented continuations, inline/wrapped
  scope commands, BOMs,
  and ambiguous/incomplete headers are unsupported. Type-level `by`/`have`/`do`,
  `letI` and recursive lets need an extension. Generated instance names and
  projections are not inferred as current literal declarations. Sealed-index
  records remain authoritative historical evidence with their real provenance.
- This is lexical/source correspondence, not TeX/Lean semantic equivalence,
  declaration elaboration, import completeness, axiom checking or kernel evidence.
  Section variables/opens/notation still apply. Unregistered prose cannot be
  discovered mechanically. Outside explicit/detected review units, the old
  file-hash-only boundary remains. Final actual manifest/row/manuscript review is
  the later separate pass requested by the coordinator.

### Schema and exact coordinator sequence

The v2 header retains the fixed baseline/revision/M42 fields and adds
`"passages": {}`. Each entry is exactly:

```json
{
  "file": "paper/sections/local.tex",
  "start_anchor": "The infinite-run quantifier here has actual witnesses",
  "end_anchor": null,
  "sha256": "<raw slice SHA-256 supplied by the proposal>",
  "coverage": ["<all current contained registered prose ids>"]
}
```

Start is inclusive; end is inclusive through its anchor or exact EOF when null.
Both anchors must occur exactly once in raw and uncommented source. Required
candidate keys/boundaries:

- `m42-geometry-scope`: `paper/sections/geometry.tex`,
  `\paragraph{Checking the hypotheses.}` → EOF.
- `m42-local-witnesses`: `paper/sections/local.tex`, the start above → EOF.
- `m42-ch07h-existence`: `companion/chapters/07_H.tex`,
  `Existence of an infinite admissible run is a separate issue.` → inclusive
  `remains open here.`; all five new prose ids are required.

Use the generated final hashes/lists, not this explanatory placeholder. The real
manifest in R remains empty. After the final coverage/manuscript review:

```sh
python3 editorial/lean_coverage/check_coverage.py --strict
S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/integration
python3 editorial/release_20261015/refresh_correspondence.py --propose > "$S/m42-propose.json"
# Review the complete v2 manifest, including the three passages, then:
python3 - "$S/m42-propose.json" <<'PY'
import json, pathlib, sys
p = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert p['status'] == 'PROPOSAL' and p['verification_performed'] is False
m = p['coverage_additions']['proposed_manifest']
assert m['schema_version'] == 2
pathlib.Path('editorial/main_results_scope_20261016/ADDITIONS.json').write_text(
    json.dumps(m, indent=2) + '\n')
PY
python3 editorial/release_20261015/refresh_correspondence.py --propose > "$S/m42-reviewed-rows.json"
# Independently review and merge rows by id with INTEGRATION.md §3's command.
python3 editorial/release_20261015/refresh_correspondence.py --write
(cd editorial && python3 assemble_claim_ledger.py)
python3 editorial/release_20261015/refresh_correspondence.py --check
```

New input/passage row `after_sha256` values are raw hashes; historical row hashes
and ids remain unchanged where old text is unchanged. Passage rows cite M42 and
all authorized prose items; source-only lookup is not successful mathematical
review. A later release still needs its own normal evidence/freeze/validation;
the Oct15 archive/history is untouched.

**Remaining infrastructure blockers:** none found in this matrix. Real manifest,
CHANGES, generated outputs and mathematical/release evidence remain the
coordinator's separate integration/review unit. Stop here as requested.

## Final small fix pass

16 October 2026; R HEAD `dde6824c13e56a43b7b711132a8b09d24f8b5292`.
Read `review_integration/FIX_REVIEW.md`, the remaining-fix prototype, and its
focused tests/counterexamples. Applied **F1 and F2 exactly as proposed**;
`integration/final_small/APPLIED_RUNTIME.diff` is byte-identical to
`review_integration/production_fix_review/REMAINING_FIX_PROPOSAL.diff`.
Clarified D1 in the current boundary documentation. No further runtime change
or broad 188-case rerun was made.

### Paths and current hashes

Only these five repository paths changed in this small pass:

| Path | Change | Current SHA-256 |
|---|---|---|
| `editorial/coverage_additions.py` | F1: reject bare CR before TeX comment masking; explicit LF/CRLF diagnostic | `9cf6c3c41e00da7311ec8eae5e7c657fd2452c67940c6fdbc2eb7c15288e6157` |
| `editorial/lean_source.py` | F2: separate literal-masked syntax recognition from comment-only trailing-body trimming | `823795a178ee5dc80a286ebf1e6ce0cb6c3c070a001bce259b6207432fbe9413` |
| `editorial/main_results_scope_20261016/INTEGRATION.md` | LF/CRLF profile, complete literal bodies, D1 delimiter-depth-zero clarification | `81184a1a7e8108b5a5e5175d0c5f28b8ceed8c7c2d2f15e722efcf392f64625c` |
| `editorial/release_20261015/README.md` | Matching boundary wording and new archived-review link | `4807a84bfee8dd8f9784a29f4e30bae92b8549017fee337d5ef8df7267500ebc` |
| `editorial/main_results_scope_20261016/verification/INTEGRATION_FIX_REVIEW.md` | Exact new independent report, provenance header and appended final dispositions | `34b99f9c4dc73c250e1960510ba8b48277df40562a5119ac61ba047fc75b15d5` |

The copied review's original body hash is
`032fc6677b686c59254e6b98f7dad3786ef7a38623a0fc9d891a193a37f4bc06`;
its embedded bytes were compared with `FIX_REVIEW.md`. The old
`verification/INTEGRATION_REVIEW.md` is untouched. Full nine-path hashes and
validation flags are in `final_small/CHECKSUMS.json` and `SUMMARY.json`.

The assembler, October checker, frozen `active_tex_sources.py`, mathematical
sources, registers, extractor, root imports, real CHANGES/receipt/generated
outputs, release, TODO/HANDOFF/AGENTS and H/HOST were not changed or used for
writing runs. The coordinator's `TODO_LEAN_COVERAGE.md` edit is untouched.
No git mutations in R and no Lean/lake commands occurred. R's real schema-v2
manifest remains empty, with its unchanged hash
`18380c1fb005893f5ffdd9101fae84392da8ace8217c915e8c2ff4071a8d53c8`.

### Focused results

Fresh `final_small/production/` and `final_small/synthetic/` clones were used.
The committed TeX/core/coverage inputs were checked unchanged from `caf00d3`.
The reviewer's 31-case focused regression design was retained as the basis;
additional invariants check the explicitly requested approved production inputs
and exact output differences. Results: **43/43 matched focused checks**
(12 accepted commands, 4 expected rejections, 27 invariants), plus **3 successful
pre-fix baseline commands**. Files: `focused_tests.py`, `FOCUSED_RESULTS.json`,
`BASELINE_RESULTS.json`, `focused_tests.log`, and `logs/`.

- **F1:** the live input after `% ...\r` rejects through both write and assembler;
  LF works in the production cycle, and a re-reviewed CRLF input completes
  write/assembler/check. The frozen resolver remains byte-identical.
- **F2:** ordinary/raw String, Char, string-equality Prop and a structure's final
  literal field are extracted completely. Numeric and theorem-literal controls
  are unchanged. Trailing nested comments are removed, comment-looking literal
  contents survive, literal text cannot create declarations, and comment-only
  declarations still reject. The literal proposition is complete in both the
  new article record and `lean_coverage_declarations` through the full pipeline.
- **D1:** the reviewer’s `(by exact True)` type is retained exactly. Documentation
  now says that the `by`/`have`/`do`/`letI`/recursive-let token refusals apply at
  **delimiter depth zero**. Balanced subterms are retained lexically, subject to
  the other lexical restrictions, without semantic validation or elaboration.
- **Real production:** write/assembler/check passes, with the 77 historical rows,
  26 new units (6 statements, 6 proofs, 10 displays, 3 passages, 1 input), six new
  source-only article records and exactly 182 principal-guard names preserved.
  The actual spectral headers, type-level-let header and complete structure-valued
  run definition match their source controls. Mathematical sources and the frozen
  library are unmodified. Repeated outputs under different hash seeds are identical.

These are source-tooling checks; no synthetic or real mathematical proof term was
compiled, axiom-audited or kernel-replayed in this pass.

### Approved inputs and exact production-output comparison

Only the production scratch clone received the independently reviewed candidate
metadata, with the four governing-citation corrections. Both provided hashes were
verified before use and remain byte-exact after the cycle:

- `metadata/ADDITIONS.reviewed.json`:
  `10a582f0888c35830c4cfb5717b73bd280ff47869f46bde81d55081f4482499a`.
- `metadata/CHANGES.reviewed.json`:
  `fe941216c6cf87a918d5a75eb1e6178243101468140ea1e4319b8f77dec5d283`.

The same approved inputs were run with the preserved pre-fix tooling, then with
F1/F2. The real `CLAIM_LEDGER.json`, `PROOF_CORRESPONDENCE.html`, and all three
component review JSON files are **byte-identical**. No mathematical record or
statement changed. The receipt differs **only** in these two values:

| Receipt JSON path | Before | After |
|---|---|---|
| `helper_sha256["editorial/coverage_additions.py"]` | `001dde6c0e96f6d3d1b6f285932298a263cec76e8fbb8f0db145acec2195c5d1` | `9cf6c3c41e00da7311ec8eae5e7c657fd2452c67940c6fdbc2eb7c15288e6157` |
| `helper_sha256["editorial/lean_source.py"]` | `6ef07b45f802a5147ed147348de579a83b8724e75aba1c66beb2a278eb00e070` | `823795a178ee5dc80a286ebf1e6ce0cb6c3c070a001bce259b6207432fbe9413` |

Machine-readable evidence: `APPROVED_METADATA.json`, `OUTPUT_DIFF.json`,
`BASELINE_OUTPUT_HASHES.json`, `FINAL_OUTPUT_HASHES.json`,
`ACTUAL_SELECTED_HEADERS.json`, and preserved `baseline/` outputs.

### Exact reviewer-recheck instructions

Run only in the saved scratch workspace. The script fixes its targets to these
two clones, verifies the approved metadata hashes, and never installs them in R.
`--baseline` restores the preserved pre-fix runtime in the production scratch
clone; `--run` copies the current R runtime there and runs only this focused matrix.

```sh
S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016
W="$S/integration/final_small"
cmp "$W/APPLIED_RUNTIME.diff" "$S/review_integration/production_fix_review/REMAINING_FIX_PROPOSAL.diff"
python3 -B "$W/focused_tests.py" --baseline
python3 -B "$W/focused_tests.py" --run
```

Expected results: 3 baseline command successes, then 43 matched checks. Inspect
`FOCUSED_RESULTS.json`, `OUTPUT_DIFF.json` (only the two helper hashes above), the
unchanged real-output hashes, and the preserved new review body. The current
owned-file hashes are `CHECKSUMS.json`; the runtime files were verified identical
to both tested clones, Python syntax checks passed, and owned-file whitespace /
tracked `git diff --check` checks passed.

**Disposition:** F1/F2/D1 complete; no remaining blocker found in this focused
pass. Approved metadata remains external for the coordinator's real installation.
This unit is finished; no broader review, release work or follow-up task was started.
