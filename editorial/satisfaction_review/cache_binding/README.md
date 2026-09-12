# Exact binding of reused Lean objects

The active receipt is `runs/cache_binding_04/MANIFEST.json`, schema 2,
SHA-256 `ea9b04f7201824f549bbe6ab4f9ff2af740c5f7d6e253b24fe59368076cb33c2`.
The actual run and its second complete read-only check passed.

From the repository root:

```sh
python3 editorial/satisfaction_review/cache_binding.py --check \
  --manifest editorial/satisfaction_review/cache_binding/runs/cache_binding_04/MANIFEST.json
```

To check a fresh extraction with explicitly attached pinned `.lake` and
`.toolchain` caches, add `--root /absolute/path/to/extracted/repository`.
Historical command paths are checked as metadata; all actual file lookups use
repository-relative paths under that root. The check performs no build,
changes no files and authenticates the complete cached-object inventory.
The caller must anchor the manifest's expected SHA-256 in its release record.

Run04 records an ordinary pinned `lake build BfgsVerification`, with inherited
`LEAN_PATH` and `LEAN_SRC_PATH` cleared. Before and after the build it:

- Checks all frozen source inputs and all nine clean, pinned dependency revisions.
- Enumerates every `.olean` on the recorded search path, including the built-in toolchain library.
- Uses pinned Lake's binary hash implementation to recompute every object hash and compare every existing `.olean.hash`.
- Seals SHA-256 hashes for objects, their existing sources, traces and hash sidecars, plus compiler executables and command evidence.
- Requires unchanged project traces and unchanged complete inventories and bytes.

The receipt binds 8,853 objects, all 8,853 source counterparts and 32,470 paired
cache files. It checks 7,382 existing output-hash sidecars. The 1,471 shipped
toolchain objects have no Lake trace/hash sidecars; their absence is recorded.
The unused Cli output directory is also explicitly absent. Any changed
presence or added object is rejected by a subsequent check. All 736 project
traces must remain identical to the baseline preceding Run01.

Run01's actual `--rehash` build failed because of tracked upstream ProofWidgets
JS cache metadata. Its failure, diagnosis and exact metadata restoration are
preserved. `runs/cache_binding_01/DIAGNOSIS.md` also corrects an overstrong label
on an unsuccessful simplified JS trace calculation. No successful `--rehash`
is claimed. Run02 failed before building on the absent unused Cli path; Run03
passed under its prior helper but mislocated the `LakeMain` source counterpart.
Both records are preserved. Run04 is the final corrected binding.

This evidence authenticates current bytes and trusted incremental provenance.
It does not independently establish every imported object's historical origin,
re-typecheck all imported objects, or claim an empty-cache original-library or
Mathlib rebuild. The Lean compiler/runtime, Lake trace mechanism and prior
cache creation remain trusted. Fresh article-supplement compilation and axiom
audits, and the fresh archive replay, have separate receipts.

The adverse-input tests in `runs/cache_binding_review_01/check_guards.py` passed
under `python3 -O`: unchanged receipts passed and seven altered command,
inventory, hash or scope cases were rejected. The tests use read-only input
overlays and leave all proof/cache/evidence files unchanged. For a new binding,
`--seal --run-id NEW_UNIQUE_ID` retains a new actual build and never overwrites
an existing run; unexpected project trace changes require explicit review.
