# Reconstructed verification suite (Module E)

This is a newly authored, reproducible theorem-verification counterpart to the report's nineteen job categories. It was reconstructed from the report proof and the checked Lean library after the user stated that they did not have the source inputs and that the sources were AI generated.

The original protocols, numerical measurements and archived transcripts are unavailable and unsupported. They are recorded as `superseded_unsupported_ai_generated_history`, not asserted to be false. This package does not claim to recover or rerun them. The original report files are preserved.

Every job compiles a frozen literal proposition for each listed actual theorem and checks exact definitional equality with its current type. Proposition bodies are frozen separately from the library's target aliases. The jobs use pinned Lean's ordinary transitive `collectAxioms` and reject all axioms outside `propext`, `Classical.choice`, and `Quot.sound`. Python only orchestrates commands, records evidence, and validates it; it does not prove mathematical claims.

Run from the Lean project root after the delivered library adoption:

```sh
python3 verification/reconstructed/run_all.py
python3 verification/reconstructed/validate.py --validate-only
```

The default run writes `fresh/`, retaining an earlier default run in `runs/`. An explicit `--run-dir` must name a new directory inside the project. `--workers` controls concurrent Lean jobs. A successful run includes a pinned `lake build`, freshly compiled job drivers, complete stdout logs and per-job check records, source/input SHA256 values, environment versions, exact commands, UTC timestamps, elapsed durations, and `fresh/SUMMARY.json`. The validator rechecks the recorded logs and all bound source/configuration hashes; it does not manufacture a successful run from a prior summary.

The names ending in `-numerical` are historical category labels. Their reconstructed methods are exact theorem counterparts:

* `C-planar-numerical` proves actual full-BFGS convergence for the explicit planar objective within its exact `<1/100` initial-value basin, and eventual objective value below `10^(-45)`.
* `U-multidimensional-numerical` proves actual full-BFGS convergence for the complete infinite-series spike objective in every supported dimension, with a unit normal, plus eventual value below `10^(-28)`. The exact rational oracle is linked to that full series.
* `G-oscillatory-numerical` is an explicit authored substitution: the unavailable auxiliary oscillatory example has no defining formula in the report. This job uses the report-defined accumulating-kink objective and proves its actual incoming-pair geometry and certificate obstruction. It does not claim an actual bad BFGS trajectory or recovery of the unspecified oscillatory function.

The tolerance indices are existential consequences of convergence; no iteration count, stopping-time computation, numerical precision or historical trajectory is asserted. `jobs.json` keeps the superseded old measurements separate from fresh compiler-check counts and timings. Repeated theorems in multiple categories are reported as check occurrences; `distinct_theorems_checked` separately records unique names.

`CORRECTIONS.md` and `SOURCE_SCOPE_MAP.json` state the exact authored changes. `CONTRACT_MAP.md` maps each mathematical role to its actual theorem and literal contract. The frozen library's definitions and hypotheses remain part of every statement: in particular, no arbitrary objective is assumed to satisfy a radial, transport, compactness or smoothness certificate, and no iterate/matrix convergence is inserted as a new hypothesis.

The extra L checks in the P category are labeled boundary/regularity comparisons in `CONTRACT_MAP.md`. They do not assert that the negative L embedding belongs to the positive finite-polyhedral/PLQ convergence class.
