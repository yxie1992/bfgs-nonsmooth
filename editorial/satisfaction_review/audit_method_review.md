# Independent agent review of the audit method

Reviewed 12 September 2026. This is an author-side, AI-assisted code and
mathematical-contract review, not human peer review, a proof of foundational
consistency, or a claim that all imported libraries were freshly rebuilt.
The JSON record identifies the source bytes actually reviewed. Later release
integration must not treat those hashes as a review of subsequent changes.

## Structural geometry audit

The new `formal/DependencyAudit.lean` has no identified material dependency
traversal omission. It discovers all fourteen owned geometry declarations,
including private helpers, rather than selecting only convenient public
theorems. It requires each transitive declaration in the checked environment;
rejects unsafe and partial declarations; follows every type and available
definition, theorem or opaque value; and expands constructor parents,
mutual-inductive companions and constructors, and recursor companions and
rules. The actual closure contains 26,496 declarations. For each root,
elaborator and checked-environment types and values agree, and the separately
implemented ordinary axiom traversal agrees with the structural traversal.
The exact resulting axiom set is `propext`, `Classical.choice`, `Quot.sound`.

The pinned Lean 4.19.0 `Lean/Declaration.lean` explicitly describes the `.all`
fields on definitions, theorems and opaque declarations as information without
kernel relevance. Their omission from the structural expansion is therefore
not an omitted mutual-recursion proof dependency: actual value expressions
carry the recursor or well-founded recursion dependencies. The pinned
`Lean/Util/CollectAxioms.lean` confirms the ordinary traversal's cases; this
auditor strengthens its missing-name behavior by failing instead of skipping.
Both traversals use Lean's `Expr.getUsedConstants`, so their agreement is
independence of traversal, not independent expression parsing or two kernels.

No claim follows that a loaded imported `.olean` was independently rechecked
from source. In the pinned `Lean/Environment.lean`, imported module data
populate the environment; checking `env.checked` is a useful audit of that
environment, not a fresh elaboration of every imported source. The standard
Lean kernel, compiler/runtime, import mechanism and permitted foundations
remain explicitly trusted. No custom mathematical axiom or actual invalid
proof was found in this review.

## Findings and bounded remedies

**A01 — Reused object bytes were not authenticated by the old reuse record.**
The frozen historical register has 761 inputs and zero `.olean` entries.
Fresh geometry compilation binds the two new source/object pairs, but its
imported project and dependency objects previously had source/revision and
existence checks, not an exact object-byte inventory. The source archive's
cache attachment likewise linked those existing caches. Identical root
signatures, declaration counts and axiom sets alone do not identify all
imported object bytes. This is an evidence-boundary gap, not evidence that any
current theorem is false. The bounded remedy is an exact SHA-256 cache,
source, trace and compiler manifest with a logged incremental build and
explicit trust in prior object construction, verified before and after an
extracted-tree replay. Work and actual status are recorded below.

**A02 — Geometry compilation inherited ambient Lean paths.** The reviewed
runner copied `os.environ` and asked `lake env` for its search path without
first removing inherited `LEAN_PATH`. Its newly compiled owned objects are
prepended for the audit, which is good, but an unrelated fallback path should
not be permitted silently. Clear inherited `LEAN_PATH`/`LEAN_SRC_PATH` and
record the closed pinned search path. Parent owns changes to existing runners;
the new cache-binding helper clears both variables. No actual unintended
import was found.
The actual `geometry_structural_01/02_search_path.stdout.log` was normalized
and compared against the final cache binding's complete eleven-entry pinned
search path: they agree exactly. Thus the recorded run did not in fact use
an ambient fallback; this finding is hardening for future invocations.

**A03 — Across-run printed types are not canonical expression identity.**
Within one audit the root type/value comparisons are Lean expression equality.
Across runs, the registered contracts are `Meta.ppExpr` strings. These are
excellent readable statement evidence, but may omit implicit or universe
details and should be described as matching printed contracts. Source and
exact object identities plus the actual kernel checks supply the stronger
binding here. If an independent cross-run AST-identity claim is desired,
serialize level parameters and full expressions canonically; that additional
claim is not needed for the present report. No differing contract was found.

The public gate checks the fixed root inventory, complete local input
manifest, hashed logs and unique audit receipt, graph uniqueness and resolved
edges, exact type/value/structural edge partition, and the per-root reachable
axioms against the ordinary collector. It also checks that the union of the
root closures exhausts the registered graph. The archive verifier checks ZIP
members, path safety, regular-file modes, exact source inventory/Git state,
and fresh compilation of the article additions. Missing compiled supplement
caches are expressly not counted as fresh proof evidence. These are useful
preserved checks; the proposed cache binding augments them rather than
substituting an object hash for an actual proof audit.

## Actual cache-binding work and the first failed run

The first actual `cache_binding_01` run cleared inherited Lean paths and
checked all nine pinned package states before running
`lake --rehash build BfgsVerification`. It failed at
`proofwidgets/widgetJsAll`; no manifest was emitted. The command, stdout,
stderr and failure summary are retained in `cache_binding/runs/cache_binding_01`.

Diagnosis found a real upstream cache-metadata inconsistency. The pinned
ProofWidgets source tracks `widget/package-lock.json.hash` with value
15032582431581979733, whereas the pinned Lake text hash of the unchanged lock
file is 110023375396192760. The `--rehash` attempt recomputed that tracked
sidecar, making it the sole dirty dependency file. The existing JS target
trace is byte-identical to its cached official release archive entry
(`37380981568d4047ae48c2b08decaebf0fcccb24f5f040a10634a10f250f522d`), so
restoring that trace from the same archive cannot fix the mismatch.
`WidgetHashDiagnosis.lean` independently printed the actual lock hash and
a simple input-hash fold, with its command and outputs retained beside the
failure. The fold does not reproduce the full Lake Job trace aggregation;
`cache_binding_01/DIAGNOSIS.md` corrects the overly strong output label and
excludes those fold values from the evidence. These are infrastructure diagnostics, not mathematical proof premises.

Mathlib deliberately configures `errorOnBuild` for this widget target. No
one should disable that guard, invent a replacement trace, call the failed
command a success, or describe a metadata restoration as a fresh JS build.
The recorded method decision is an ordinary unchanged Lake build with
independent read-only recomputation of every cached binary `.olean` hash and
comparison of every present `.olean.hash`, plus the exact SHA-256 manifest.
This checks the proof-output hashes without disabling the JS guard or
modifying source pins.

## Completed bounded cache binding

`cache_binding_04` passed under the final schema-2 helper. Its manifest is
`cache_binding/runs/cache_binding_04/MANIFEST.json`, SHA-256
`ea9b04f7201824f549bbe6ab4f9ff2af740c5f7d6e253b24fe59368076cb33c2`.
The helper source SHA-256 is
`a1f2a6bf3bdb93f13fbcdd045f93bf2f7e5c13a4709fcf2f99f6be25c1234130`.
The actual ordinary build completed successfully; all 43 recorded commands
exited zero with empty stderr. Its replayed warnings concern unused variables,
unreachable or unnecessary tactics and deprecated names; no compile error or
newly built original module was reported. This is an incremental build.

The binding enumerates all 8,853 `.olean` objects across the eleven configured
search entries, including 736 original project objects and 1,471 toolchain
objects. Every object now has its actual existing source counterpart bound.
All 7,382 existing `.olean.hash` sidecars agree with independently recomputed
binary Lake hashes both before and after the ordinary build. The 1,471
toolchain objects do not ship Lake traces or output-hash sidecars; that
absence is recorded explicitly. The final cache manifest seals 32,470 object,
source, trace and sidecar files, plus compiler executables, 765 pinned source
and helper inputs, dependency revisions and command evidence. All nine
dependencies remained clean and pinned. Every original project trace is
unchanged from the baseline taken before the first failed rehash attempt.

Lake legitimately includes an unused, absent Cli output directory in its
search path. Its absence is sealed and must remain unchanged. Run02 stopped
before building because the initial helper required every configured path to
exist; that failure remains intact. Run03 passed with all object bytes bound,
but a subsequent inventory review found that the `LakeMain.olean` source was
mislocated in the pairing rule. Run04 corrects that source mapping, retains
Run03 unchanged, and is the sole active binding. No missing source remains.

The checker calls the pinned Lake `computeBinFileHash` on each raw object and
uses `Hash.load?` only to read the sidecar. This is precisely the binary hash
that `Module.oleanFacetConfig` obtains through `fetchFileTrace` and that
`cacheFileHash` writes. Python additionally requires canonical decimal byte
equality. The helper requires identical before/after inventories and bytes,
rejects missing or changed original project traces, validates the exact
ordered command inventory and actual version/search-path receipts, and
performs a second complete read-only verification before accepting a seal.
The sibling agent independently reviewed this implementation and found no
actionable blocker; that review did not execute the seal.

Read-only adverse-input tests in `cache_binding_review_01` exercise failed or
changed commands, omitted core/object inventory, inconsistent binary hashes,
an invented successful-rehash claim, and a wrong object SHA-256 expectation.
The tests use input overlays, preserve all original files, and ran with
Python optimization enabled. The unchanged receipt passed and all seven
adverse cases were rejected; `GUARD_TESTS.json` records the actual outcomes.

This closes A01 for the current trusted incremental evidence. It does not
establish the historical origin of every prior object independently of Lake
traces, re-typecheck every imported object, or rebuild Mathlib from an empty
cache. The parent-owned fresh archive replay and public-gate integration have
separate completion records; this review does not claim those before they run.


## Final integration review and A02 resolution

The final two-script diff was independently read after implementation. In
`validate_archive.py`, every external command now passes through the single
`run` helper with an explicit copied environment that removes both
`LEAN_PATH` and `LEAN_SRC_PATH`; the command and summary receipts state that
control. Each fresh supplement's actual ordered base search path must resolve
to exactly the eleven sealed directories. The pinned frozen runners prepend
only their newly compiled local modules for their own audits. This closes A02
for archive replay without changing an already audited runner or retrospectively
claiming a different old environment. The actual earlier geometry path was
also directly verified to match the complete pinned path.

The archive authenticates the registered cache manifest, summary, helper and
retained evidence before attaching the disclosed caches. It then executes the
read-only cache check before library use and in `finally` after all four fresh
supplement audits and the current/historical gates. A preceding failure is
not converted to a pass when the final cache check succeeds. Existing source,
ZIP, contract, graph, axiom, compiler and document checks remain in force.

The public gate authenticates the same receipt and actually runs the helper
when both caches exist. Broken or partial cache availability fails. If both
caches are absent, it explicitly reports source-only receipt authentication
with `current_cache_bytes_verified = false`; it does not claim that present
cache bytes or fresh compilation were verified. The actual current gate
passed all 21 checks with helper exit zero, empty stderr and
`current_cache_bytes_verified = true`. Its inspected receipt SHA-256 is
`23f2474fa41a6eb07d8c2f4ee66505a4a98c4ef23d76fd25fb2e027fc15597b1`.

The reviewed final source hashes are
`b9c15b1ac8b3bfbd5aae96e556ade8f6e678d10fa75eb6e7a8e279944fa73bd8`
for `validate_archive.py` and
`f77d173cbb9973221f043b434c24846d15ab5b65e1cd11a60bf46f6b5233322f`
for `verify_release_inputs.py`. No actionable blocker was found in this
bounded integration review. A01 and A02 are closed at the stated evidence
boundary. A03 remains an explicit terminology distinction: across-run printed
contracts with pinned sources and objects, versus within-run exact Lean
expression equality. The complete new archive execution is parent-owned and
has its own later receipt; it is not claimed by this code review.
