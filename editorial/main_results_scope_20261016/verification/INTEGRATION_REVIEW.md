# Preserved independent review and implementation fix pass

The independent review below is copied verbatim from
`m42_20261016/review_integration/REVIEW.md` in the approved OpenCode scratch
directory, dated 16 October 2026. Its SHA-256 is
`ea742723f620b4576874fadcf9cb5f21572314ebc08c1c04337de38aa143414a`.
It reviewed the delivered six-file implementation on a scratch clone at
`3de9c74`; its original source hashes, findings and verdict are retained.
The implementation agent's dispositions are appended after the original report.

---

# Independent M42 integration-tooling review

**Verdict: changes required before infrastructure sign-off.** Three must-fix
source-validation gaps are reproduced below. The historical 77-row table,
September evidence boundary, and 182-name principal guard survive the ordinary
addition path. Actual-manifest/new-row review remains a separate, pending step.

Date: 16 October 2026. Repository: `/Users/yxie/Projects/bfgs-nonsmooth`.
Scratch directory: this report's directory, `S/review_integration`.

## Scope and provenance

- Reviewed only the six delivered paths, plus the requested handoff/method/report
  material and the existing helpers where necessary to understand their use.
  Mathematical proof bodies were not independently reviewed.
- Tests used a scratch clone checked out at `3de9c74`. Only the six delivered
  implementation paths were copied from R. All further manuscript, register and
  Lean-looking changes were synthetic test fixtures in that clone.
- No repository content was edited, and no add/commit/checkout/reset/config/push
  command was run in R. No Lean or lake command ran anywhere. Prototype fixes
  were exercised only in the scratch clone, then the clone's fixture state was
  restored.
- The implementation's `CHECKSUMS.json` matches all six start hashes. All six
  remained byte-identical through the end observation. R advanced concurrently
  from the stated starting revision to `1ef18d9c64a11f281a9f14950ca420a468782105`;
  the reviewed implementation bytes did not change.
- The empty manifest is intentional. This review did **not** demand that the
  unfinished actual article/coverage/manifest tree pass either entry point.

## Must fix

### I1 — Valid alternative input spellings bypass exact authorization

**Locations:** `editorial/coverage_additions.py:79-84,95-107`;
`editorial/release_20261015/refresh_correspondence.py:1055-1060`;
`editorial/assemble_claim_ledger.py:20-22`.
The dependency responsible for the missed edge is
`editorial/active_tex_sources.py:21-26`.

Both entry points trust a scanner recognizing only adjacent, braced
`\input{...}` / `\include{...}`. These valid TeX spellings are invisible to it:

```tex
\input {appendices/review_hidden}
\input
{appendices/review_hidden}
\input appendices/review_hidden.tex
```

For **each** spelling, I installed an unlisted scratch input containing new
labels, a named statement and a proof, with no register or authorization for it.
`--write`, the assembler, and the subsequent `--check` all exited 0. The hidden
input was absent from `active_article_inputs`. Refreshing the master-file hash
does not establish the claimed exact input/label inventory.

**Required fix:** make the shared gate reject source syntax its input/label/item
scanners do not understand, or consistently extend those scanners. The tested
conservative fix rejects noncanonical `input`, `include`, `label`, `begin` and
`end` spellings before treating the graph as complete. Document the supported
literal TeX grammar; it is not a general TeX macro evaluator.

**Tests/fix:** `BUG-noncanonical-input-{space,newline,unbraced}-*`;
`fixed-noncanonical-input-*`, `fixed-noncanonical-label-*`.
`FIX_PROTOTYPE.diff` demonstrates the central fail-closed guard in the delivered
helper. Both entry points reject the reproductions with that guard.

### I2 — Canonical module ownership is not enforced on transitive targets

**Locations:** `editorial/coverage_additions.py:233-241,256-307`, especially
`238-239` versus `295-299`.

The canonical `ex.lean_module(path)` check runs only for `additions.files`.
`check_item()` recursively visits other files, but trusts those registers'
arbitrary `lean_module` values when checking the first declaration's owner.

Reproduction: a new registered prose item refers to the old item
`A/geometry/prose/007`. Give that old item status `LEAN`, set its register module
to `BfgsArticle.HypothesisExamples`, and cite the scratch package declaration
`BfgsVerification.HypothesisExamples.helper`. Keep the complete-input row current
with the new prose status and reachable name. All three commands pass even
though the required module is `BfgsArticle.Coverage.Article.Geometry`.

This is an ownership failure in the relationship closure, independent of
whether the referred-to mathematical statement is relevant.

**Required fix:** in `check_item()`, for every visited target, require both its
canonical register path and its canonical source-file coverage module. Track the
actual register path loaded, rather than deriving a potentially different path
only when producing the receipt.

**Tests/fix:** `BUG-foreign-closure-module-*` passes on the delivery;
`fixed-transitive-foreign-module-*` rejects with `FIX_PROTOTYPE.diff`.
`fixed-canonical-transitive-target-*` confirms that a correctly owned old target
still works. Cross-file cycles and unresolved transitive names already reject.

### I3 — “Current declaration” lookup can report nonexistent names or incomplete statements

**Locations:** `editorial/coverage_additions.py:224,248-250,291-299,319-327,345-358`;
`editorial/assemble_claim_ledger.py:102-103,115-118`.
Relevant dependency behavior: `editorial/coverage_index.py:40-70` and
`editorial/lean_coverage/check_coverage.py:41-54`.

The new evidence path relies on the existing textual scanner without validating
its lexical context or the completeness of its statement extraction:

| Fixture | Observed result |
|---|---|
| Put the governing `theorem toy ...` entirely inside a nested-comment-capable `/- ... -/` block | Write, assembler and check pass; the new ledger record cites the commented line as its current declaration. |
| Add an anonymous `section` / `end` inside the coverage namespace and cite the parser's resulting root `review_section_*` names | All three pass. The declarations are still inside the real outer namespace; the scanner incorrectly popped that namespace at the section's `end`. |
| Use `theorem toy (n : Nat := 0) : n + 0 = n := ...` | Write and assembler pass, but the published statement is exactly `theorem toy (n : Nat`, with its conclusion missing. |

The explicit source-only status correctly avoids claiming kernel evidence, but
it does not make a commented declaration, wrong qualified name, or truncated
statement truthful source correspondence. Preferring these strings over stale
audit signatures makes this a relevant dependency defect in the new path.

**Required fix:** validate addition-cited declarations against lexical Lean code:
mask nested comments and strings, track sections separately from namespaces,
resolve the actual name at the cited source line, and reject incomplete or
unsupported statement extraction. A declaration body separator must not be
confused with a default-binder assignment. Keep the legacy sealed/audit index's
provenance intact.

**Tests/fix:** the three `BUG-comment-only-*`, `BUG-anonymous-section-*` and
`BUG-default-binder-*` groups reproduce these failures. The conservative source
guard in `FIX_PROTOTYPE.diff` rejects each through both entry points. It also
rejects a private declaration masquerading as a public cited name. Ordinary
current-signature changes, the valid fixture, and the empty-manifest path still
work with identical ledger/HTML output where appropriate.

The scratch guard is an executable, conservative fix prototype: it rejects
unsupported headers instead of implementing all Lean syntax. Only the listed
regressions and positive fixtures were tested. A production parser/fix still
needs implementation review; this is not a completed production fix pass.

## Should address explicitly

### S1 — Complete-input rows are normalized, not raw-byte prose-review seals

**Locations:** `editorial/coverage_additions.py:135-136`;
`editorial/release_20261015/refresh_correspondence.py:211-225,586-600`;
`editorial/main_results_scope_20261016/INTEGRATION.md:48-52`;
`editorial/release_20261015/README.md:100-102,203-205`.

Ordinary unlisted prose edits are rejected even after updating only the
manifest hash: the whole-input row becomes stale. However, its comparison uses
the old whitespace normalization. I first reviewed an input tail containing:

```tex
Unregistered editorial tail for whole-input binding.% invisible note
A standalone source-only sentence.
```

I then moved the newline after `%` to a space, making the visible sentence a
comment, and updated **only the raw manifest hash**. Write, assembler and check
all passed with the exact same reviewed `CHANGES.json` rows. The normalized
strings are equal; the comment-stripped TeX is different. This is not a hash
collision. It follows the documented whitespace-only exemption, but qualifies
the stronger prose-binding description.

**Recommended exact fix, tested:** use the full raw-file hash for the new
`input:` row's `after_sha256`, leaving every historical unit's normalization
unchanged. `RAW_INPUT_FIX_PROTOTYPE.diff` adds that input-only hash and records its
scope in the receipt. Update the row/hash documentation at the locations above.
Its 22 checks preserve all 77 old rows, reject the newline/comment edit until
the input row is re-reviewed, and confirm deterministic write/check behavior.
If normalized input rows are retained, expressly state this limitation rather
than treating the row as raw-byte or semantic prose review.

### S2 — The actual old-file M42 prose has no listed review unit

**Locations:** `editorial/coverage_additions.py:126-127,233-241`;
`editorial/main_results_scope_20261016/INTEGRATION.md:16-18,50-58`;
`editorial/release_20261015/README.md:55-59,169-174`.

| Actual addition observed | Last existing mapped unit ends | Treatment |
|---|---:|---|
| `paper/sections/geometry.tex:110-138` — the appended hypothesis-checking and examples paragraphs | 100 | Current file hashes only |
| `paper/sections/local.tex:443-451` — the appended infinite-run witness paragraph | 435 | Current file hashes only |

These additions contain no new input, named environment, label or display, so
they do not even add their files to `Additions.files`. Adding registered prose
items alone would not change that trigger. They therefore receive neither new
`CHANGES` rows nor this helper's all-registered-prose/closure validation.

This **is consistent with the October README's explicit old-input limit**; it
is not an undisclosed bypass of that bounded contract. It means the phrase
“a file containing an addition” in `INTEGRATION.md:16-18` must be interpreted
more narrowly than all actual M42 prose additions. The global strict coverage
check and the independent manuscript/coverage review retain their roles.

The scratch `old-prose-*` tests confirm: `--check` first detects stale current
file hashes, but `--write` then succeeds with no new row; the two files are
absent from `coverage_additions.coverage_verified`. Actual ranges, unit metadata,
hashes and the prose-only diff are saved in `OLD_PROSE_SCOPE.json` and
`ACTUAL_OLD_PROSE.diff`.

**Exact strengthening if these paragraphs are to be mechanically review-bound:**
extend the explicit manifest with passage entries for the geometry tail starting
at `\paragraph{Checking the hypotheses.}` and the local tail starting at
`The infinite-run quantifier here has actual witnesses`, ending at the current
EOF, each with its exact file and raw passage hash. Include those files in the
validated set and create `passage:m42-geometry-scope` and
`passage:m42-local-witnesses` units requiring M42 rows and overlapping current
prose coverage. A subsequent tail edit must stale the passage row, not merely
the receipt. This passage extension is a proposal, not an implemented/tested
production fix. At minimum, name the hash-only exception in `INTEGRATION.md` and
record the independent review of these actual paragraphs separately.

## Optional

**O1 — Make proposal status machine-explicit.**
`editorial/release_20261015/refresh_correspondence.py:1058-1059,1240-1247` and
`editorial/coverage_additions.py:198-202` correctly avoid successful verification
in proposal mode. The README and final report clearly explain the distinction.
An explicit `verification_performed: false` / `status: PROPOSAL` field would
help downstream consumers: exit 0 means a proposal was produced, and an empty
`coverage_additions.problems` list is not a strict coverage certificate.

## Boundaries and checks that do hold

- For the canonical syntax actually recognized, the manifest compares exact
  observed input and label sets, including section labels, against fixed M42
  baseline `61453638c9e86c7fce2cba0078da9fa0fe6f0e16`. A wildcard label grants no
  permission; changing the manifest baseline/header fails. Raw input hashes
  prevent stale-source authorization. The template itself grants no additions.
- Old label moves, old statement removal even with its labels retained,
  unlisted old statement mutations, extra new labels/proofs, and missing new
  mechanical items reject. The implementation's additional removal/authorization
  tests were inspected, rather than blindly rerun.
- New named results require final `LEAN` ownership and a theorem/lemma-shaped
  primary declaration; definitions require `DEFINITION`. A following proof must
  target its precise statement. Statement/proof rows cannot substitute a merely
  reachable supporting declaration for the governing coverage name.
- Mechanical item hashes/placement, registered prose anchors, final statuses,
  missing references and cycles are checked. Every registered prose item in the
  selected addition files is checked, not every possible prose claim in the
  document. The closure-ownership and source-parser exceptions are I2/I3.
- New statements, proofs, labeled/unnumbered displays and whole inputs get
  addition units. I separately changed an existing unnumbered display inside an
  old proof, keeping fixture coverage current: both its new display row and the
  changed old proof row were necessary; deleting either row rejected. The old
  display-removal test in the implementation suite was also inspected.
- The 77-row empty-manifest proposal matches exactly. Empty-manifest write,
  assembler and check preserve the baseline ledger, HTML and component reviews.
  Repeated write/assembler with different Python hash seeds are deterministic.
- New records have current source/proof locations and raw source hashes, empty
  historical `source_spans`, registered `full_formal_exports`, no
  `principal_exports`, and source-only status. Old article records remain
  identical in the ordinary toy-appendix test. The old bounded-field, snapshot,
  retained-evidence and export checks remain active.
- The exact 182-name principal guard is unchanged; every new fixture export is
  already included through coverage registers in the complete audit name set.
  This was a source-only name-collection check, not an axiom audit execution.
- The receipt catches edits to the helper, index, strict checker, full checked
  register, cited Lean source and unrelated active TeX files. Its Lean binding
  is to **cited source files**, not an imported-module dependency closure or a
  fresh elaboration. Current-package signature preference over an old audit
  entry works; the extraction still needs I3.
- The assembler does not independently validate reviewed `CHANGES` rows. Its
  success alone therefore cannot establish review of whole-input prose. The
  documented assembler + October write/check combination is required. Neither
  establishes TeX/Lean semantic equivalence, import completeness, elaboration,
  axiom admissibility or kernel verification.

## Tests and artifacts

The implementation's `run_tests.py`, `extra_tests.py`, result files and report
were inspected: 103 + 12 recorded checks, all marked passed, with matching
delivered-file hashes. I reused only its synthetic fixture constructor.

| Independent artifact | Observations | Interpretation |
|---|---:|---|
| `REVIEW_TEST_RESULTS.json` | 80 | Baseline, ordinary addition, adversarial authorization/closure/parser cases, receipt pins and prose boundaries |
| `EDGE_TEST_RESULTS.json` | 19 | Changed old unnamed display + parent row, retained-label statement removal, comment/newline complete-input limit |
| `FIX_TEST_RESULTS.json` | 32 | Scratch canonical-syntax, closure-ownership and source-lexing guards |
| `RAW_INPUT_FIX_TEST_RESULTS.json` | 22 | Raw whole-input row binding and backward compatibility |

The 99 review observations comprise 46 accepted commands, 30 expected
rejections, 15 invariant assertions and 8 explicit deficiency observations.
They must **not** be summarized as 99 successful verification checks. The 54
scratch fix observations all matched their expected outcomes (24 accepted
commands, 21 rejections, 9 assertions). `REVIEW_TEST_SUMMARY.json` gives the
counts; `logs/` retains command output.

Two initial harness attempts stopped at an earlier fail-closed diagnostic: a
stale complete-input citation in the transitive-target fixture, and removal of
a theorem label rather than movement of a section label. Those fixtures were
corrected to isolate the intended conditions. Initial traces remain in
`REVIEW_TEST_RESULTS_INITIAL.json`, `REVIEW_TEST_RESULTS_PRE_FINISH.json` and the
initial logs. The final matrices contain no unexplained failed expectation.

Python syntax checks used `compile()` without creating repository bytecode.
All fixture declarations and reviews are textual test data, not evidence for
the actual mathematics. Prototype diffs are separate from the delivered files;
they were not installed in R.

## Pending actual manifest / CHANGES / ledger review

This is **not completed by the infrastructure tests**. After the implementation
fix pass and completion of the real coverage, the coordinator can continue this
review session for:

1. The installed manifest: fixed baseline/header; the final raw hash of
   `paper/appendices/hypothesis_examples.tex`; exactly the actual new inputs and
   labels, including section label `art:hypothesis-examples` and the six known
   result labels `art:examples-mixed`, `art:examples-full-rank`,
   `art:examples-run-existence`, `art:examples-two-quadratics`,
   `art:examples-nonradial-runs`, `art:examples-no-step`, plus any genuinely added
   display labels. No placeholders or prefix permissions.
2. All actual new statement/proof/display/whole-input rows, their final statuses,
   current hashes, exact governing declarations and proof targets; retained old
   row IDs and appropriate correction IDs on any changed old unit.
3. A clear disposition of the geometry/local prose above: independently reviewed
   hash-only material, or explicitly bound added passage units.
4. Actual new ledger records with current, correctly resolved declarations,
   source provenance, proof locations, no invented September spans/principal
   exports, and the still-exact 182-name guard.
5. Fresh write/assembler/check and deterministic receipts on the settled source
   set. The coordinator's package build, axiom audit, kernel replay and PDF
   review provide their own evidence later; none was run by this reviewer.

The coordinator should record accepted findings in the repository TODOs. This
read-only reviewer has left that repository edit to the coordinating session.

## Preserved source hashes

Full start/end records: `SOURCE_HASHES_START.json` and `SOURCE_HASHES_END.json`.
Observed from `2026-10-16T18:51:54.081343+00:00` to
`2026-10-16T19:12:04.513879+00:00`; every digest is unchanged.

| Delivered path | SHA-256 at both observations |
|---|---|
| `editorial/assemble_claim_ledger.py` | `0d1da3564f20206868793e6103b6b4389b288d9af4fdadbee93888a6fedad3aa` |
| `editorial/coverage_additions.py` | `eab2e09a3953722d4e3d98eccf0200f805dbe274d80f5b7861255bb5dd6e6787` |
| `editorial/release_20261015/refresh_correspondence.py` | `4a8d39356afd8e02454fd95dcaeddde6ed8bb3f717a4399d46b5a5310e893447` |
| `editorial/release_20261015/README.md` | `5d062fdd8c407cbe34f605f577e6a31e232fe772639c335337155b6084d57acf` |
| `editorial/main_results_scope_20261016/ADDITIONS.json` | `9e79e14e57d6e7f104c3f9a0e22c34d2adbb3b04e1985aa99e47ca8011bff5a9` |
| `editorial/main_results_scope_20261016/INTEGRATION.md` | `990b408e466d0270a8efc33089ed405c4f367e7653133548e62becc0d72c4c40` |

---

## Fix dispositions (implementation agent, 16 October 2026)

The author/coordinator accepted I1, I2, I3, S1, S2 and O1. This section records
their implementation; it does not replace the independent findings above or the
later real-manifest/manuscript/row review.

| Finding | Production fix | Verification scope |
|---|---|---|
| I1 | `coverage_additions.require_canonical_tex` is shared by both entry points. It rejects noncanonical input/include/label/begin/end spellings, unsupported arguments and TeX character translation. The frozen `active_tex_sources.py` is unchanged. The existing companion `StartModule` label template is accepted only on its exact baseline definition line. | Both entry points reject the spaced/newline/unbraced inputs and includes, noncanonical labels/environments, translated commands and unsupported starred claims. Ordinary commented commands and the real manuscript source graph work. |
| I2 | `Coverage.register_sources` records the loaded JSON path; `check_item` requires the canonical register path and `ex.lean_module(path)` for every visited item, including transitive targets. Every source is an active, indexed document input. | Foreign closure module and renamed closure register rejected; canonical cross-file closure accepted. |
| I3 | New `editorial/lean_source.py` supplies lexical names and complete source statements. Nested comments/strings are masked, section and namespace scopes are distinct, public qualification is resolved, private/unsupported names are refused, default binders and simple type-level lets do not terminate headers. Source-backed entries retain actual file/line provenance and are marked as statements, while the sealed index is preserved. The strict checker's other rules are retained through a source-name callback. | Synthetic comment/string/private/section cases, default binders, absolute qualification and a header longer than 80 lines; real article/core/companion module shapes, including the production type-level let and structure-valued definitions. These are source checks, not elaboration/kernel evidence. |
| S1 | `unit_hash` uses raw bytes for new complete inputs; historical units still use the unchanged normalization. | Comment/newline and CRLF changes require renewed input rows even after manifest-only hash updates; old 77-row hashes remain valid. |
| S2 | Schema-v2 `passages` authorizes exact existing document paths, unique inclusive start/end anchors (null end = EOF), raw slice hashes and exact contained registered prose-item sets. The geometry/local tails and Chapter 7 caveat are proposed automatically and require manifest authorization plus M42 change rows. | Production-shape route includes all five `C/07_H/prose/076`–`080` items; undeclared passages, missing rows, stale raw hashes, omitted prose, non-M42 rows, duplicate anchors and arbitrary/traversing paths reject. |
| O1 | Top-level and nested proposals explicitly report `status: "PROPOSAL"`, `verification_performed: false`. | Proposal assertions distinguish successful proposal generation from strict verification. |

The supported literal TeX and lexical Lean grammar, explicit unsupported forms,
schema and exact coordinator commands are in `../INTEGRATION.md`. General TeX
macro/conditional/catcode evaluation and Lean command generation/elaboration are
outside this source check. Sealed source-span evidence and the 182-name principal
guard remain separate from the new source-backed records.

The completed fix matrix has **188 matched checks** (58 accepted commands,
101 expected rejections, 29 invariants), including production write/ledger/check,
unchanged old 77 rows, identical sealed-index provenance, the exact 182-name guard,
and deterministic outputs under different hash seeds. Two initial test harness
expectations were refined to isolate the intended guard: theorem-label removal
first hit the existing unlabeled-statement check, and omitting an open-question
prose citation first hit the existing unreachable-principal check. Both were
correct rejections; their initial traces are retained. No production guard was
relaxed to satisfy either test.

Final lexical-boundary regressions also reject repeated same-line attribute lists,
unknown column-zero commands and inline/wrapped scope commands. The production
write/ledger/check was repeated after that tightening, with identical ledger/HTML
and component outputs and deterministic refreshed receipts.

Scratch test scripts/results are recorded under `m42_20261016/integration/fix/`
and in the appended **Fix pass** of
`m42_20261016/integration/FINAL_REPORT.md`. No Lean/lake run, mathematical proof
review, release refresh, or installation of the real manifest/table was performed
by this infrastructure fix pass.
