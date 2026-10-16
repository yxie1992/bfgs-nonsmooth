# Integrating the M42 article additions

This is an editorial infrastructure extension, prepared against `6145363` on
16 October 2026. Its schema-v2 `ADDITIONS.json` began as an empty, fail-closed
template. After independent mathematical, coverage, metadata and infrastructure
reviews, the coordinator installed the exact reviewed configuration: one new
appendix, seven labels and three bounded passages. The current table has 103
listed changes (77 historical rows and 26 M42 additions), and the ledger has six
new article records. Current correspondence and strict coverage checks pass;
the 182-name principal guard is unchanged. Records are in `verification/`.

## Evidence and boundaries

- `ADDITIONS.json` explicitly lists **new active inputs** (path → full raw-file
  SHA-256) and **every new label** (label → file), relative to the fixed M42
  baseline `61453638c9e86c7fce2cba0078da9fa0fe6f0e16`. Both tools require that
  history. The actual `paper/master.tex` input graph determines what is active.
  A wildcard/prefix permission, an unused file, or a register row alone grants
  no authorization. Old inputs and labels must remain, in their original files.
- `coverage_additions.py` validates every mechanical item and every registered
  prose item of a file selected by a new input/result/label/display or an explicit
  passage. It invokes the existing strict checker with lexical source-name lookup
  (the checker's status/hash/docstring rules are retained) and additionally checks current lines, hashes, anchors,
  complete final status, reference closure (including cycles), declaration lookup,
  and canonical register-path/coverage-module ownership for **every recursively
  visited target**. A named theorem/lemma/proposition/corollary must
  be `LEAN`, with a theorem in the file's coverage module. Its following proof in
  the same input must be `PROOF` of that precise statement. Definitions must be
  `DEFINITION`. A new proof not attached to an added result is refused.
- Every new statement, proof and display, plus the whole new input, has a current
  October `CHANGES.json` row citing M42. Unnumbered display keys are coverage item
  ids. New/changed unnumbered displays in old inputs are detected by comparing the
  mechanical display sequences with the M42 base; an unmatched current display
  is conservatively a newly checked unit. Deletions are refused. Existing labeled
  units retain their original keys. Both the old unit row and any nested new unit
  row must be reviewed when an old proof gains a display.
- New complete-input rows use the **raw file SHA-256**, and explicit passage rows
  use the **raw UTF-8 byte-slice SHA-256**. Their hashes preserve comments, newline
  boundaries and line endings; even a whitespace-only edit needs a renewed row.
  Historical units keep their original normalization and hashes.
- The three historical component reviews gain **no new rows, spans or exports**.
  Their immutable evidence and all bounded-field/export assertions stay intact.
  Their refreshed source hashes/locations continue to describe the current files.
  The existing 77 rows are still valid wherever the text is unchanged.
- The assembler adds new `article_records` from current coverage. They carry
  current TeX hashes, registered statements with real source provenance and source
  hashes, and the actual proof location and coverage relationship. Their
  `source_spans` are empty; `full_formal_exports` contains the registered names;
  **`principal_exports` is absent**. The audit's complete cited-name set grows, but
  its existing 182-name principal guard stays fixed. Every new name is already in
  the coverage-register name set audited by `axiom_audit.py`.
- For addition citations of package declarations, the coverage index reads the
  complete, lexically resolved `.lean` text even if an earlier package audit has
  a signature. `lean_source.py` masks nested comments/strings and distinguishes
  sections from namespaces; private or unresolved names cannot be published as
  public current declarations. The legacy
  index and its September/supplement/audit provenance remain intact (SF6,
  `3fa85bc`). New records are marked `CURRENT_COVERAGE_SOURCE_CORRESPONDENCE`;
  source lookup is not kernel evidence. Section variables/open namespaces still
  apply to source-text statements, as in the existing coverage index.
- The October receipt additionally pins this helper, `lean_source.py`, the coverage index/checker,
  the manifest, checked registers and the Lean sources cited by the additions.
  The manifest's raw input hash and the whole-input row bind prose outside every
  mathematical item. The main assembler validates source coverage independently;
  the October checker validates `CHANGES.json` and the mapping receipt. Run both.

## Explicit prose passages (schema version 2)

Alongside `active_inputs` and `labels`, `passages` maps a key such as
`m42-local-witnesses` to exactly these fields:

```json
{
  "file": "paper/sections/local.tex",
  "start_anchor": "The infinite-run quantifier here has actual witnesses",
  "end_anchor": null,
  "sha256": "<full raw passage hash from --propose>",
  "coverage": ["<every current registered prose item in this passage>"]
}
```

Anchors are nonempty, single-line, verbatim strings, each occurring exactly once
in the file and its uncommented text. The start is inclusive; a non-null end is
inclusive through the end anchor, while `null` means the exact current EOF.
The path must be an existing source at the fixed M42 baseline, present in both
the actual document input graph and `extract_items.ARTICLE` or `.COMPANION`.
Unindexed/inactive/arbitrary paths and new-input paths are refused. The complete
new appendix already has its own `input:` unit.

The following three requested routes are automatically proposed when their start
anchors are present, and require explicit manifest authorization:

| Key | File | Inclusive boundaries |
|---|---|---|
| `m42-geometry-scope` | `paper/sections/geometry.tex` | `\paragraph{Checking the hypotheses.}` → EOF |
| `m42-local-witnesses` | `paper/sections/local.tex` | `The infinite-run quantifier here has actual witnesses` → EOF |
| `m42-ch07h-existence` | `companion/chapters/07_H.tex` | `Existence of an infinite admissible run is a separate issue.` → `remains open here.` |

`coverage` is the exact set of current registered prose items overlapping the
passage; each must be contained in its line range and have its anchor in the
passage. At least one is required. The Chapter 7 route includes all five entries
`C/07_H/prose/076`–`080`, including the open question. The helper checks the entire
selected file and every referenced target. A `passage:<key>` CHANGES row must cite
M42 and **all and only** these prose items, with their current statuses and hashes.
Other recognized existing-source passages can be explicitly declared with the
same schema; this grants no arbitrary filesystem access. Unknown prose outside
all declared/detected units retains the original file-hash-only boundary.

Passage rows are `added` review units relative to the September unit inventory;
this does not assert that every byte of their text is new. Their `before_sha256`
is null. Review both their raw text and their coverage closure. Updating only a
manifest hash cannot authorize a changed passage: its CHANGES row must also be
reviewed and refreshed.

## Supported source syntax and evidence limits

- **TeX:** the shared gate requires adjacent literal braced `\input{...}`,
  `\include{...}`, `\label{...}`, `\begin{...}` and `\end{...}` commands. Spaces or
  newlines before `{`, unbraced forms, dynamic/nested arguments, and starred
  theorem/proof environments are refused. The newline profile is LF or CRLF;
  bare CR is rejected **before comment masking**, so it cannot hide a live input
  behind a `%` comment. Input paths, labels and environment
  names use the literal character sets enforced by the gate; TeX `^^` character
  translation is refused too. The pre-existing
  companion `StartModule` macro's `\label{#1:chapter}` is allowed only on its
  unchanged baseline definition line. The frozen `active_tex_sources.py` is
  untouched. This is a literal source graph, not TeX macro/conditional/catcode
  evaluation; commands constructed by general TeX expansion are outside the
  supported manuscript grammar.
- **Current Lean source:** literal named declarations and namespace/section/end
  commands start at column zero. Namespace qualification, `_root_.` declarations,
  named/anonymous/noncomputable sections, ordinary and raw strings, character
  literals, nested comments, single-line attribute lists (one list per line) and the ordinary declaration
  modifiers are recognized. Private declarations cannot serve as public exports.
  Complete theorem/lemma headers require an explicit type and balanced delimiters;
  default-binder `:=` and simple type-level `let ... := ...` are distinguished from
  the body separator. There is no 80-line truncation. Definitions/structures retain
  their complete body up to the next supported command, including `where` fields
  and trailing string/character/raw-string literals. Syntax recognition masks
  literals; trailing-body trimming uses a separate comment-only view that preserves
  literal contents, including comment-looking text within them.
- **Refused current-source grammar:** indented declaration/scope commands, quoted
  identifiers, bare `_root_` namespace commands (use `_root_.Name`), Lean syntax
  quotations, interpolated strings, multiline or repeated same-line attribute lists,
  mutual blocks, generated-command macros/elaborators/exports, unknown column-zero
  commands or identifier-led unindented continuations, inline/wrapped scope commands,
  BOM characters and
  ambiguous/incomplete headers. The type-level `by`, `have`, `do`, `letI` and
  recursive-let token refusals apply **at delimiter depth zero**. Balanced subterms
  are retained lexically, subject to the other lexical restrictions, without
  classifying or semantically validating their term grammar: for example,
  `(by exact True)` is retained in a theorem's type. Ordinary proof bodies after
  the separator are not parsed or checked. Anonymous generated instance names and structure
  projections are not inferred as literal declarations. Frozen sealed-index
  records retain their original provenance rather than being reinterpreted by
  this lexical parser. Unsupported unrelated files are not current-source evidence.

The standalone historical coverage/index scripts are unchanged. For additions,
the helper supplies the lexical name callback to the existing strict checker and
complete source statements to the existing index renderer; the ledger distinguishes
those strings from sealed/elaborated signatures. Section variables, opens and
notation still apply. No Lean macro expansion, import resolution or elaboration
is claimed by this lexical source check.

The mechanical extractor cannot discover all prose assertions or prove that the
Lean and TeX mean the same thing. The existing independent coverage/row review
must check those, including the full joint hypotheses and initialization
quantifiers. Textual declaration lookup does not check imports, elaboration,
axioms or proof terms. The final package build/audit/replay supplies that evidence.
No release archive is produced by this extension.

## Coordinator run order and exact commands

Run from the repository root. Use Python 3.11 or newer. The example scratch path
below is the integration agent's approved scratch directory.

### 1. Finalize manuscript and coverage

Confirm the finalized `paper/appendices/hypothesis_examples.tex` is listed in
**`ARTICLE` in `editorial/lean_coverage/extract_items.py`** as well as in the actual
TeX input graph (the coordinator added both during this infrastructure task).
That explicit inventory is outside this infrastructure change's ownership;
the new gate refuses an unindexed input. Finalize
`editorial/lean_coverage/register/A_hypothesis_examples.json`, the coverage module
and its root import. Resynchronize the edited old files using the coverage
README's correction procedure. Build/visually inspect the TeX edits and compare
warnings as required by `AGENTS.md`.

```sh
python3 editorial/lean_coverage/check_coverage.py --strict
S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/integration
python3 editorial/release_20261015/refresh_correspondence.py --propose > "$S/m42-propose.json"
```

### 2. Review and install the exact manifest

Review `coverage_additions.proposed_manifest`: every path, label (including section
anchors), raw input hash, passage boundary/hash and prose-item list must belong to
the finalized M42 edit. Resolve all
`coverage_additions.problems`; proposal mode is intentionally read-only and can
describe unapproved/incomplete additions. Both the top-level and nested proposal
have `status: "PROPOSAL"` and `verification_performed: false`; exit 0 and an empty
problems list are not coverage certification. Once reviewed, install that manifest:

```sh
python3 - "$S/m42-propose.json" <<'PY'
import json, pathlib, sys
proposal = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert proposal['status'] == 'PROPOSAL' and proposal['verification_performed'] is False
manifest = proposal['coverage_additions']['proposed_manifest']
assert manifest['schema_version'] == 2
pathlib.Path('editorial/main_results_scope_20261016/ADDITIONS.json').write_text(
    json.dumps(manifest, indent=2) + '\n')
PY
python3 editorial/release_20261015/refresh_correspondence.py --propose > "$S/m42-reviewed-rows.json"
```

### 3. Review and merge the current change rows

In `$S/m42-reviewed-rows.json`, review every `uncovered` row against its `hints`,
the source diff and the Lean statements. Fill `review`, verify `coverage` and
`principal_lean`, and resolve stale rows/anchors. New rows must cite M42. On an
old row changed again by M42, retain the correction items describing the net
September-to-current change and add M42. Use the proposed current hashes; old
`before_sha256` values remain September hashes. New `input:` and M42 `passage:`
`after_sha256` values are raw hashes, not the historical normalized hashes.
Do not rename existing row ids.

After the independent row review, this merges the reviewed rows by id:

```sh
python3 - "$S/m42-reviewed-rows.json" <<'PY'
import json, pathlib, sys
proposal = json.loads(pathlib.Path(sys.argv[1]).read_text())
path = pathlib.Path('editorial/release_20261015/CHANGES.json')
table = json.loads(path.read_text())
positions = {row['id']: i for i, row in enumerate(table['changes'])}
for row in proposal['uncovered']:
    assert len(row['review']) >= 20 and 'M42' in row['correction_items'], row['id']
    if row['id'] in positions:
        i = positions[row['id']]
        old = table['changes'][i]
        assert (old['kind'], old['key']) == (row['kind'], row['key'])
        table['changes'][i] = row
    else:
        positions[row['id']] = len(table['changes'])
        table['changes'].append(row)
path.write_text(json.dumps(table, indent=2) + '\n')
PY
python3 editorial/release_20261015/refresh_correspondence.py --write
(cd editorial && python3 assemble_claim_ledger.py)
python3 editorial/release_20261015/refresh_correspondence.py --check
```

A fresh `--write` is expected: the committed October receipt pins the earlier
tooling and sources. This updates the **current** receipt/component mappings;
the Oct15 release at `992d477`, its receipts, archives and `release/history/`
remain historical. A later release requires its own normal freeze and validation.

### 4. Check the audit boundary, then complete formal evidence

This source-only check must still report 182 guarded declarations:

```sh
python3 - <<'PY'
import pathlib, sys
sys.path.insert(0, 'bfgs_lean_article/scripts')
import axiom_audit as a
principal, article, companion, private = a.ledger_names()
guarded = set(principal) | set(a.PACKAGE_PRINCIPAL)
pinned = {line.split()[-1] for line in pathlib.Path(
    'bfgs_lean_article/BfgsArticleAxioms.lean').read_text().splitlines()
    if line.startswith('#print axioms ')}
assert guarded == pinned and len(guarded) == 182
print('Principal guard unchanged:', len(guarded))
print('Complete audit name set:', len(set(article) | set(companion) |
                                      set(a.coverage_names()) | set(a.PACKAGE_PRINCIPAL)))
PY
```

When the Lean agents have finished, complete the actual package build, axiom audit
and kernel replay with the commands/order in `bfgs_lean_article/README.md` and
`editorial/release_20261015/README.md`. Re-run the ledger if signatures/registers
change, and `--write`/`--check` if the addition's bound inputs change. Those commands
were not run by the infrastructure agent; scratch fixture `.lean` files are only
textual test data and provide no formal evidence for the article.
