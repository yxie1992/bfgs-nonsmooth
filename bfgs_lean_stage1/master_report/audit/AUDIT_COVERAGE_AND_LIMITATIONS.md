# Complete declaration audit: scope and trust boundary

The old central gate checked 7,813 theorem constants whose names begin with `BfgsVerification`. Its checked-environment traversal was sound for those roots, and the new audit reproduces every one of their printed types and transitive axiom sets exactly. However, namespace filtering omitted 61 generated theorem constants: 59 private declarations and the generated equations `isEmptyElim.eq_1` and `signHom.eq_1`, and non-theorem mathematical definitions were not independently enumerated as roots. This was a coverage gap, not evidence of a faulty proof.

The new audit enumerates ownership by the actual imported Lean module rather than by declaration-name prefix. It finds all 736 library modules (735 files plus the root import file); the 737th frozen Lean source is the central `Audit.lean` tool itself, not an additional mathematical library module.

| Safe checked declarations | Main library | Main plus supplemental claim reviews |
|---|---:|---:|
| Theorems, including private/generated | 7,874 | 7,954 |
| Definitions | 1,679 | 1,708 |
| Inductive type declarations | 38 | 38 |
| Constructors | 43 | 43 |
| Recursors | 38 | 38 |
| Total unique safe roots | 9,672 | 9,781 |

The main audit additionally covers 21 proof-valued definitions and 11 proof constructors as independent roots. `isProp` in the JSON means that the constant's *type* is a proposition. A target definition whose type is `Prop` therefore has `isProp=false`; this does not mean that its value is not a mathematical proposition. Its type and value are nevertheless audited. Universe parameters are recorded separately from the pretty-printed type.

Every safe root has a checked kernel declaration, and its checked type, safety, declaration kind, universe parameters, and immediate dependency list agree with the elaboration environment. The graph collector uses the checked types and bodies. It matches the pinned `Lean.Util.CollectAxioms` cases, including inductive-constructor traversal, constructor/recursor type-only traversal, opaque bodies, and axiom/quotient terminal cases. Complete outgoing edges are constructed before reverse axiom reachability is computed; cycles cannot create partially cached axiom sets. The graph helper is byte-identical to the already reviewed central helper.

Both complete graphs have no missing declaration and no reachable unsafe or partial constant. Every transitive axiom is one of `propext`, `Classical.choice`, and `Quot.sound`. This conclusion covers definitions and their types independently, including definitions not used by a named final theorem. It does not claim that Lean mathematics uses no axioms.

## Compiler-only declarations

The 11,632 main-module constants also contain 1,960 compiler implementation entries excluded from mathematical roots: 1,727 unsafe definitions, 14 partial unsafe-recursion companions, and 219 unsafe `axiomInfo` entries. The latter comprise 183 `_spec_` specialization names and 36 `_elambda_` erased-lambda names, distributed across the modules listed in `compiler_classification.json`. All 219 carry `isUnsafe=true`; there is no safe project `axiomInfo`. None of these excluded entries is reachable from any of the 9,672 safe main roots, even through imported dependencies. They are therefore not added mathematical assumptions of the verified statements. Compiler-erased pseudo-types such as `_obj` are not interpreted as mathematical propositions; their JSON `isProp` field is null.

A comment/string-aware scan of all 737 frozen sources finds no authored `axiom`, `unsafe`, `implemented_by`, `sorry`, `admit`, or `native_decide` token. The graph itself independently rejects `sorryAx`, unsafe or partial reachability, and every nonstandard axiom. The two extra excluded constants in the supplemental environment are unsafe generated definitions, not additional safe axioms.

## Supplemental scope and source attribution

Five newly compiled modules are exact byte copies of the public M, A/C, D/L, search-fuel, and original-claim peer sources. The original-claim peer source contains the complete owner source verbatim, so compiling it covers all 17 owner declarations without importing duplicate definitions. All 182 ordinary audit occurrences from the six public jobs (141 distinct names) agree with the unified axiom inventory, and the fresh source compilations rerun their strict contracts. The 70 distinct authored supplemental declarations expand to 109 additional safe constants when generated declarations are included.

Eight generated equation lemmas have a different `getModuleIdxFor?` attribution depending on import order; their names, types, universe parameters, axiom sets, and direct dependencies remain identical. In particular, `FullBFGSRun.d.eq_1` can be attributed to the newly imported M audit rather than a main module. Count supplemental additions by the difference of declaration-name sets, not by the apparent owning-module prefix. Preserve main-only attribution when a fixed original source location is wanted. A recorded source range is metadata supplied by Lean and may be absent for a generated declaration; it is not proof that the declaration was textually authored at that location.

## Remaining limits

This is a declaration and dependency audit, not a replacement for reviewing the source-report-to-Lean statement correspondence. A kernel-checked theorem can still state an unintended conditional conclusion. The original-claim review, source claim ledger, corrected mathematical statements, and strict independently stated contracts address that separate question. Unsupported historical numerical protocols and measurements are not made true by compilation.

The trusted proof boundary remains the pinned Lean kernel, its imported checked library, and the three named standard axioms. The auditing metaprogram is independently reviewed tooling, not a new mathematical axiom. Python only orchestrates commands, compares exact evidence, and hashes artifacts; it performs no mathematical verification. A further fully independent ordinary collector replay can be slow; the shared collector's case correspondence and exhaustive existing ordinary comparisons are preserved rather than misrepresented as a new ordinary invocation per root.

The reproduction uses an incremental `lake build BfgsVerification` against the pinned project, not a clean reinstall. It clears inherited `LEAN_PATH`, creates its own exact-byte supplemental objects, records the explicit resulting path, and verifies all nine dependency revisions and clean states before and after. It never calls the central `check.py`, and it does not change the released central audit or status register. The old `check.py` itself does not clear inherited `LEAN_PATH`; this standalone run does.
