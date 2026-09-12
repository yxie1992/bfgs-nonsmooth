# Article-only formal deductions

These supplemental sources verify elementary geometry written explicitly in the journal article. They do not modify the sealed Lean project or its audit policy.

From the repository root, after the pinned project bootstrap has succeeded:

```bash
python3 editorial/article_formal/verify.py
```

Each invocation creates a new UTC-named directory under `runs/`; `--run-id NAME` selects a unique explicit name. Existing run directories are never overwritten. The command verifies pinned input hashes, checks the actual Lean version, compiles both mathematical modules, and runs an independent dependency audit. Object files under each run's `build/` are reproducible intermediate artifacts.

`ArticleGeometry.lean` proves the mixed-ridge inward identity and actual derivative, equal-rate descent, exact seed affine independence/full affine span and strict descent, and the affine-balance equivalence. `ConvexBalance.lean` proves the generic finite convex-balance equivalence. All slope statements use the isolated algebraic seed, not its plotted rational approximation. The inward identity is proved for every real `tau <= 1`, which includes the article's `0 <= tau <= 1` range.

`DependencyAudit.lean` selects every declaration owned by either mathematical module, including generated/private helpers rather than only a namespace or advertised theorem list. It traverses checked types and proof/definition values recursively, fails on missing, unsafe, partial or unapproved axiom dependencies, compares checked/elaborated root metadata, and runs Lean's ordinary `collectAxioms` independently for each root. Its own metaprogram is audit tooling and is never imported by a mathematical proof.

The final successful run is recorded in the root contract register. Its `SUMMARY.json`, `commands.json`, compiler logs, `declarations.json` and full `dependency_graph.json` bind the result to exact source hashes. Earlier failures are retained as failed drafts; their compiler-generated `sorryAx` messages are not accepted verification evidence. No mathematical source contains an unfinished proof, and a final audit containing `sorryAx` fails.
