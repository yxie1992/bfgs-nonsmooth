# Preserved production-fix review and final small fix dispositions

The independent report below is copied verbatim from
`m42_20261016/review_integration/FIX_REVIEW.md` in the approved OpenCode scratch
directory. Its SHA-256 is
`032fc6677b686c59254e6b98f7dad3786ef7a38623a0fc9d891a193a37f4bc06`.
It reviewed the `caf00d3` production sources and the eight tooling hashes it lists.
Its findings and historical pending-review statements are unchanged. Final
implementation dispositions follow the original report.

---

# Independent review of the production M42 infrastructure fix pass

**Verdict: one further, small fix pass is required.** The original counterexamples
are closed, and the actual `caf00d3` source integration succeeds. Two remaining
edge cases still violate the fail-closed input inventory and complete-statement
claims: **F1**, bare-CR comment boundaries; **F2**, definitions ending in literals.
Both have minimal scratch-tested fixes. There is also a nonblocking grammar
documentation clarification, **D1**.

This continues `REVIEW.md`; it does not repeat its completed general review or
approve the eventual installed manifest/change rows.

## Reviewed snapshot and execution boundary

- R: `/Users/yxie/Projects/bfgs-nonsmooth`,
  `caf00d3a4cd17a300fd36599fb938398d6cdca57`.
- Read the implementation report from **Fix pass**, the preserved original
  review/dispositions, and current `INTEGRATION.md`; inspected the production
  code and implementation test scripts/results. Its eight checksums match the
  reviewed snapshot and its reported 188 checks all have matched outcomes.
- Fresh scratch clones under `production_fix_review/`, based on `caf00d3`,
  received only the eight delivered files. The real manuscript/core/coverage
  inputs came from that commit. Synthetic fixtures and temporary manifests/rows
  were confined to those clones.
- R was read-only: no content edits or git mutations. No Lean/lake commands ran.
  Release archives and H/HOST were untouched. A tiny, separate pdfTeX input
  grammar probe corroborated F1; it did not build the manuscript or check any
  mathematical proof.
- All eight delivered source hashes are unchanged between the start/end
  observations below. R's real manifest remains the empty schema-v2 template.

## Disposition of the original findings

| Finding | Independent disposition |
|---|---|
| **I1** canonical TeX syntax | Original spaced, newline and unbraced cases reject through both entry points. The frozen `active_tex_sources.py` is unchanged. **F1 remains** at a newline/comment boundary. |
| **I2** recursive ownership | **Closed.** Every visited item checks its actual loaded register path, canonical module and active indexed source. Forged transitive module and renamed transitive register both reject; proper transitive references work. |
| **I3** current declaration lookup | Original comment/string/private-name, anonymous-section and default-binder failures are closed. Complete long headers work. The actual production declarations work. **F2 remains** in non-theorem body trimming. |
| **S1** raw input seals | **Closed.** New input rows bind raw bytes. Comment/newline and CRLF changes still require row renewal after a manifest-only hash update. Historical hashes are retained. |
| **S2** explicit old-source passages | **Closed for the requested routes.** The actual geometry/local/Chapter 7 units are proposed, authorized, raw-sealed and checked with their complete required prose lists and reference closure. Missing authorization, missing row, omitted prose/open-question item, stale passage and invalid path reject. |
| **O1** proposal status | **Closed.** Both levels report `status: PROPOSAL`, `verification_performed: false`. Successful generation is explicitly distinct from verification. |

The original report is preserved verbatim with its correct hash in
`editorial/main_results_scope_20261016/verification/INTEGRATION_REVIEW.md`.

## Remaining must-fix findings

### F1 — Bare CR lets a live input disappear into the guard's comment mask

**Locations:** `editorial/coverage_additions.py:59-69,121-127`.
The frozen resolver's `editorial/active_tex_sources.py:21-26` provides the
contrasting universal-newline read; it need not be edited.

The new helper reads raw UTF-8 bytes, but `tex_code()` terminates `%` comments
only at LF. The frozen resolver uses `Path.read_text()`, which normalizes bare
CR to LF. In the scratch master's otherwise unmodified body, insert these bytes:

```text
% scratch comment\r\input {appendices/review_hidden}\n
```

Here `\r` and `\n` denote actual control bytes, not TeX backslash commands.
The raw guard masks the input as part of the comment. The frozen scanner sees
the spaced `\input` after universal-newline conversion and misses it for the
original I1 reason. The new file, labels and named result have no authorization
or register.

**Observed:** `--write`, assembler and subsequent `--check` all exit 0, and
`review_hidden.tex` is absent from `active_article_inputs`. A minimal pdfTeX run
with the same bare-CR/comment/input shape actually read the hidden file and
printed its marker. This is a literal input-grammar issue, not TeX macro expansion.

Evidence:

- `production_fix_review/logs/I1-bare-CR-observation.log`
- `production_fix_review/logs/I1-bare-CR-accepted-{assembler,check}.log`
- `production_fix_review/TEX_CR_RUNTIME_PROBE.json`
- `production_fix_review/clone/review_tex_cr_probe/stdout.log`

**Exact fix tested:** before comment masking in `require_canonical_tex`, reject
`re.search(r'\r(?!\n)', text)`, with an explicit “use LF or CRLF” diagnostic.
This keeps the frozen resolver untouched and avoids inconsistent bare-CR line
counts elsewhere. State the accepted LF/CRLF newline profile in
`INTEGRATION.md:113-123`. The two entry points then reject this reproduction;
a properly re-reviewed CRLF new input still integrates successfully.

### F2 — Trailing string/character literals are removed from definition bodies

**Locations:** `editorial/lean_source.py:21-28,47-77,197-209`, especially line 208;
the affected completeness claim is `INTEGRATION.md:124-132`.

The lexical mask correctly blanks strings/characters while locating commands.
However, non-theorem extraction computes its endpoint with
`len(self.code[start:end].rstrip())`. That same mask has blanked literal values,
so it removes a final literal along with trailing comments/whitespace.

| Actual source | Published `statement` |
|---|---|
| `def value : String := "hello"` | `def value : String :=` |
| `def value : Char := 'x'` | `def value : Char :=` |
| `def value : Prop := "x" = "x"` | `def value : Prop := "x" =` |
| A structure whose last field is `label : String := "hello"` | The field ends at `label : String :=` |

Raw-string definitions exhibit the same problem. These are within the documented
supported literal grammar. Numeric definitions and theorem headers containing
string literals are controls that still extract correctly.

**End-to-end reproduction:** cite the public scratch package declaration
`M42ReviewSupport.literal_prop`, defined by `"x" = "x"`, as an additional
registered name. Write, assembler and check all pass. Both the coverage index
and new article record publish the truncated `def literal_prop : Prop := "x" =`
with current file/line provenance and source hash.

Evidence: `production_fix_review/GRAMMAR_PROBE_RESULTS.json`,
`production_fix_review/LITERAL_PIPELINE_REPRO.json`, and
`production_fix_review/logs/literal-definition-pipeline-*.log`.

**Exact fix tested:** separate the masks used for syntax recognition and for
trimming trailing comments. The proposed patch adds
`code_mask(..., preserve_literals=True)` and uses that comment-only view when
finding a non-theorem declaration's end. It continues scanning/skipping literal
contents lexically, so comment-looking text inside literals is retained and
fake declarations inside strings remain invisible to the normal declaration
inventory. All five incomplete-body cases become complete, and the end-to-end
ledger contains the full proposition definition.

### Tested patch and regression scope

`production_fix_review/REMAINING_FIX_PROPOSAL.diff` contains only the two small
runtime corrections above, against the reviewed production bytes. It is a
suggestion, not an installation in R.

`production_fix_review/REMAINING_FIX_TEST_RESULTS.json` records **31/31 matched
outcomes**: 12 accepted commands, 4 expected rejections and 15 invariants.
They include:

- F1 rejection through both entry points; accepted CRLF integration after raw-row
  renewal;
- complete ordinary/raw-string, character, proposition and structure bodies;
- trailing-comment removal and continued rejection of comment-only names;
- strings still unable to create lexical declarations;
- a full actual-source write/assembler/check cycle with **byte-identical real
  ledger, HTML and component outputs**, unchanged old 77 rows, and deterministic
  output under changed hash seeds.

The two corrections require refreshed receipt hashes and an implementation
review before sign-off; they do not change the mathematical declarations.

## Nonblocking documentation clarification

### D1 — Type-level term restrictions apply at delimiter depth zero

**Locations:** `editorial/lean_source.py:94-118` versus
`editorial/main_results_scope_20261016/INTEGRATION.md:133-141`.

The documentation says type-level `by`/`have`/`do`/`letI`/recursive lets require
a future extension. The code rejects those tokens only when the delimiter stack
is empty. For example, it accepts and faithfully records:

```lean
theorem value : (by exact True) := by trivial
```

There is no truncation in that example, and this is not another correctness
blocker. Clarify the operational boundary: **at delimiter depth zero** those
tokens are refused; balanced subterms are retained lexically without their term
grammar being classified or elaborated. This matches the helper's otherwise
well-stated source-only scope. The observation is recorded in
`production_fix_review/GRAMMAR_PROBE_RESULTS.json` and was retained as a positive control in the
scratch fix tests.

## Actual production integration and declaration evidence

Using only the committed `caf00d3` article/coverage/core sources and the eight
delivered tooling paths, with temporary test authorizations/review sentences:

- Initial proposal: **77 matching historical rows**, no stale/unmatched rows or
  unresolved anchors, and **26 new units**: 6 statements, 6 proofs, 10 displays,
  3 passages and 1 complete input. Temporary integration has 103 rows.
- The new input has exactly the seven expected labels, including the section
  label, with its actual raw hash. No real manifest was installed in R.
- Required passage sets are exactly 16 geometry prose items (`044`–`059`),
  4 local prose items (`045`–`048`), and all 5 Chapter 7 items (`076`–`080`),
  including the open question. The receipt validates 323 selected/closure items
  and binds 26 Lean-evidence inputs: 25 current `.lean` files and the sealed
  declaration index.
- Write, assembler and check pass; all original 77 row values are unchanged.
  The six new article records have current proof/source locations, empty
  historical spans, source-only status and no `principal_exports`.
- Every old sealed-index coverage signature/provenance entry remains identical.
  The exact principal-guard set is still **182** names. Every new article export
  is already in the coverage-register set collected by the full audit tooling.
  This was name collection, not execution of an axiom audit.
- Repeated write/assembler under different hash seeds is byte-identical.

The two recent spectral lemma headers were independently compared with their
complete current source slices, excluding the proof terms:

| Declaration | Current source | Result |
|---|---|---|
| `BfgsCoverage.Article.HypothesisExamples.mixed_least_spectrum` | `BfgsArticle/Coverage/Article/HypothesisExamples.lean:114` | Exact two-line header, including `IsLeast (spectrum ℝ (Mixed.run.H k)) ...` |
| `BfgsCoverage.Article.HypothesisExamples.mixed_spectral_limit` | Same module, line 126 | Exact three-line header, including both the universal spectral assertion and the `Tendsto` conclusion |
| `BfgsCoverage.Article.HypothesisExamples.quadratic_history_decrease` | Same module, line 333 | Complete type-level `let R := Quadratic.run ...` and both conjuncts |

These are under `bfgs_lean_article/`. Exact extracted strings and provenance are
saved in `production_fix_review/ACTUAL_SELECTED_HEADERS.json`. The production
`BfgsVerification.HypothesisExamples.Quadratic.run` definition also retains its
structure-valued body, including the final `weak_wolfe` field. Neither F1 nor F2
was triggered by the unmodified production manuscript/declarations in this run.

The documented restricted grammar is appropriate as a **lexical source**
boundary: public literal names, separate section/namespace scopes, balanced
headers, and explicit refusal of generated/quoted/unsupported command forms.
It does not establish import resolution, Lean elaboration, axiom admissibility,
proof-term validity or TeX/Lean semantic correspondence. The coordinator's Lean
results and mathematical reviews retain those roles.

## Tests and artifacts retained

Under `production_fix_review/`:

| Artifact | Scope/outcome |
|---|---|
| `FIX_REVIEW_RESULTS.json` | 86 observations: 23 accepted commands, 35 expected rejections, 26 invariants, one bare-CR observation and one explicit remaining-defect record |
| `GRAMMAR_PROBE_RESULTS.json` | 8 lexical probes; 5 expose the literal-body truncation, 2 are complete-statement controls, 1 documents D1 |
| `LITERAL_PIPELINE_RESULTS.json`, `LITERAL_PIPELINE_REPRO.json` | 3 accepted pipeline commands and the published-truncation assertion |
| `TEX_CR_RUNTIME_PROBE.json` | Minimal pdfTeX corroboration that the bare-CR hidden input is read |
| `REMAINING_FIX_TEST_RESULTS.json` | 31 matched scratch-patch checks, described above |
| `FIX_REVIEW_SUMMARY.json` | Machine-readable counts and actual integration metadata |
| `production_checkpoint/`, `synthetic_checkpoint/`, `logs/` | Reproducible scratch states and command output |

These observations are not “all successful verification checks”: the delivered
code accepts the two counterexamples. The implementation's entire 188-case
matrix was inspected, not redundantly rerun. Unchanged historical behaviors from
the first review were retained; testing focused on the fixes, new parser
boundaries and the now-final production inputs.

One test-harness oracle initially assumed every selected theorem used `:= by`.
`mixed_spectral_limit` uses a direct proof term. The oracle was corrected to the
appropriate header separator, the already-passed observations were retained,
and only the required temporary output state was regenerated to continue.
`FIX_REVIEW_RESULTS_INITIAL.json` and `retest.log` preserve that initial trace;
the final matrix has no unexplained failed expectation.

## Separate pending review

After F1/F2 and the documentation updates, the coordinator's **actual installed
manifest and reviewed CHANGES rows still require their separate review**.
The temporary review sentences here explicitly identify infrastructure testing;
they are not mathematical row approval. The later review should check the final
raw hashes, all seven labels, three passage boundaries/prose sets, every new unit,
its exact coverage/target/current declaration and the generated receipt/ledger.
The successful scratch cycle and 182-name guard check do not replace that step.

## Source hashes

Full records: `production_fix_review/SOURCE_HASHES_START.json` and
`production_fix_review/SOURCE_HASHES_END.json`.
Observed from `2026-10-16T20:01:26.615160+00:00` to
`2026-10-16T20:27:02.643466+00:00`; all eight are unchanged.

| Delivered path | SHA-256 at both observations |
|---|---|
| `editorial/assemble_claim_ledger.py` | `36e7fa7c82de410d6f5ddbc2d2bafcab4ac10034be823d2429985561aafd00dc` |
| `editorial/coverage_additions.py` | `001dde6c0e96f6d3d1b6f285932298a263cec76e8fbb8f0db145acec2195c5d1` |
| `editorial/lean_source.py` | `6ef07b45f802a5147ed147348de579a83b8724e75aba1c66beb2a278eb00e070` |
| `editorial/release_20261015/refresh_correspondence.py` | `7dadc6d7d48869b7d2538ce37c18800451f38a3de834aca59f46ce82d5b67376` |
| `editorial/release_20261015/README.md` | `0ba5db0ef0b306b5fe8cf7afc81f440799a5d4126fbd96425575186035b50e3d` |
| `editorial/main_results_scope_20261016/ADDITIONS.json` | `18380c1fb005893f5ffdd9101fae84392da8ace8217c915e8c2ff4071a8d53c8` |
| `editorial/main_results_scope_20261016/INTEGRATION.md` | `b0c625f78456259abf51abafde815542cb510355988a91ebf8e99eff75608795` |
| `editorial/main_results_scope_20261016/verification/INTEGRATION_REVIEW.md` | `d5d59a56657f7c7a8fe763d680b918bbba5f221a05d7ca4ac4ce835d4cd9928f` |

---

## Final small fix dispositions (implementation agent, 16 October 2026)

The coordinator accepted F1, F2 and D1. The two runtime changes exactly match
`production_fix_review/REMAINING_FIX_PROPOSAL.diff`; no further parser or
mathematical change is included in this pass.

| Finding | Final change | Focused verification |
|---|---|---|
| F1 | `require_canonical_tex` rejects `\r(?!\n)` before comment masking, with the explicit LF/CRLF diagnostic. The frozen resolver is unchanged. | Bare-CR hidden-input reproduction rejects through both entry points; a re-reviewed CRLF input completes write/assembler/check. |
| F2 | Syntax recognition keeps the literal-masked view; trailing-body trimming uses `code_mask(..., preserve_literals=True)`, retaining literal contents while removing trailing comments. | Ordinary/raw-string, character, proposition and structure-final-field definitions remain complete. Nested trailing comments are removed, comment-like literal contents survive, strings cannot create declarations, and comment-only names still reject. The full literal proposition is published in both ledger indexes. |
| D1 | `INTEGRATION.md` and the October README state that the listed type-level token refusals apply at delimiter depth zero; balanced subterms are retained lexically without semantic validation. | The reviewer's parenthesized `(by exact True)` header is retained exactly as a positive control. |

**43/43 focused checks passed:** 12 accepted commands, 4 expected rejections and
27 invariants, based on the reviewer's 31 focused checks plus the coordinator's
approved-production comparison requirements. Three additional pre-fix baseline
commands succeeded. The completed broad 188-case work was not repeated.

The coordinator subsequently supplied independently reviewed metadata, including
the four corrected governing citations. Only scratch clones used these exact files:

- `ADDITIONS.reviewed.json`: `10a582f0888c35830c4cfb5717b73bd280ff47869f46bde81d55081f4482499a`.
- `CHANGES.reviewed.json`: `fe941216c6cf87a918d5a75eb1e6178243101468140ea1e4319b8f77dec5d283`.

With those inputs, the real ledger, HTML and three component outputs are
byte-identical before/after F1/F2. The receipt differs **only** at
`helper_sha256["editorial/coverage_additions.py"]` and
`helper_sha256["editorial/lean_source.py"]`. All 77 historical rows, 26 new units,
six new article records, actual complete spectral/type-let/structure statements,
and the exact 182-name principal guard are preserved. Repeat production outputs
are deterministic under changed hash seeds.

The real manifest remains empty in R. No real table/receipt/generated output,
mathematical source, register or frozen resolver was changed. No Lean/lake, git
mutation in R, or H/HOST access occurred. Source correspondence remains distinct
from elaboration, semantic equivalence and kernel evidence.

Exact output diffs, input/output hashes, focused scripts/logs and reviewer-recheck
commands are in `m42_20261016/integration/final_small/` and the **Final small fix
pass** appended to `m42_20261016/integration/FINAL_REPORT.md`.
