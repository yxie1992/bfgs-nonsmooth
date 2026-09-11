# Complete safe-declaration audit

From `bfgs_lean_stage1/`, validate the delivered evidence:

```sh
python3 master_report/audit/run.py --check
```

Create a new, timestamped audit run without overwriting the delivered run:

```sh
python3 master_report/audit/run.py --run
```

The command prints its new directory. Validate that run with `--check --run-dir <directory>`. The pinned project must already be bootstrapped. The runner uses the existing project-local Lean4.19 toolchain and an incremental main-library build; it does not install a toolchain, erase cached artifacts, run the central checker, or alter the frozen central status.

`main/all_safe_declarations.json` is the complete 9,672-root main inventory. `supplemental/all_safe_declarations.json` is the complete 9,781-root unified inventory, including all main roots. Merge by declaration name; it adds 109 safe constants rather than duplicating main declarations. `module_sources.json` maps actual module metadata to the copied source files or pinned main sources. Each declaration records the checked type, universe parameters, optional source range, and direct project dependencies from its type, value and inductive structure, separately from its transitive standard-axiom set.

The six files in `sources/` are exact copies of the public original-claim review sources. Five are freshly compiled as modules: the peer source already contains the entire original owner source, so that owner is not imported twice. The runner verifies this exact-prefix relationship through the public claim-review manifest, reruns the ordinary reports/strict contracts in those sources, and enumerates all their safe generated constants as well.

The `fresh/` directory contains actual compiler logs, command/cwd/timing records, before/after dependency checks, source/configuration hashes, both inventory outputs, and a completed summary. It includes the incremental main build and fresh compilation of every copied supplemental module. All mathematical traversal is performed in Lean; Python only orchestrates and compares evidence.

The 219 main compiler-only unsafe `axiomInfo` entries are separated in `main/compiler_implementation_declarations.json`. They are not mathematical roots, and the complete checked dependency graph proves that no safe root reaches them or any unsafe/partial implementation entry. See `AUDIT_COVERAGE_AND_LIMITATIONS.md` for the exact trust boundary, the 59 private plus 2 other generated theorem additions, module-attribution drift, and the difference between declaration audits and statement reviews.

Historical absolute paths in command records identify where this actual run occurred. They are evidence labels, not runtime dependencies: validation and reruns read only the copied package plus existing public files in `bfgs_lean_stage1/`. No scratch proof import is needed. All log/source hashes are retained. The earlier preparatory run's final classifier rejected an overly narrow “all61private” assertion; all its Lean commands succeeded. The final runner compares the exact audited declaration-name sets and the corrected59+2 classification.
