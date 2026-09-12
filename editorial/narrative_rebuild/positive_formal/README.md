# Literal mixed-benchmark proof

`MixedBenchmark.lean` proves whole-sequence convergence for every actual admissible full-BFGS run on `UnexcitedMetric.objective`, the literal function `u²+|v|`. It is separate from the old special vertical-run family. The only three public declarations are the actual inward error, the inward sublevel bound, and the end-to-end global convergence theorem.

After bootstrapping the pinned `bfgs_lean_stage1` project, run from the repository root:

```bash
python3 editorial/narrative_rebuild/positive_formal/verify.py
```

Each run has a new directory under `runs/`. The compiler freshly builds the article-only proof. The imported original library's build remains the separately sealed historical evidence. The runner verifies all 761 frozen original audit inputs before and after the run, records exact source hashes and actual commands/output, and invokes an independent checked-environment dependency audit. That audit includes type, value, constructor, mutual-inductive and recursor-rule edges; checks every module-owned helper; rejects nonstandard axioms, unsafe/partial or missing dependencies; checks exact root type/value agreement; and compares the ordinary axiom collector per root with an independent traversal.

The reviewed final evidence is `runs/20260912_mixed_benchmark_02/`: 3 owned declarations, 31,960 checked dependencies, only `propext`, `Classical.choice` and `Quot.sound`. Run 01 is retained as earlier-version evidence. `.olean` files under each run's `build/` are reproducible ignored artifacts. No audit program or unchecked computation is imported into the mathematical proof.
