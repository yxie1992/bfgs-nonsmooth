# Main-result hypothesis and scope review — 16 October 2026

Requested by Yuchen Xie after the 15 October release: are the main results'
complicated conditions jointly satisfiable, are examples presented, and how
general are the results?

Start with [REVIEW.md](REVIEW.md). It separates qualifying objectives, actual
infinite BFGS runs, and existence from prescribed initial data. It collects the
existing examples and provides additional worked calculations. Manuscript
presentation proposals are tracked as M42 in `TODO_MANUSCRIPT_REVIEW.md`.

**Implementation completed, 16 October 2026.** The approved additions are now
in the article's hypothesis-check guide and Appendix E, with joint Lean
hypothesis/run witnesses and literal coverage. The companion explicitly states
the Chapter 7 existence caveat. Independent implementation, mathematical,
literal-coverage and correspondence reviews are in [verification/](verification/README.md).
Fresh package-wide evidence passes for 5506 audited names and 786 replayed
modules; see [the completion record](verification/EVIDENCE.md).

## Records

| File | Purpose |
|---|---|
| `REVIEW.md` | Coordinator's synthesis, theorem-scope map, explicit certificates and runs, further analytic examples, presentation recommendations. |
| `FORMAL_EVIDENCE.md` | Independent source/PDF audit of the existing theorem contracts and non-vacuity witnesses at `a6f46d1`, with exact Lean declarations and locations. |
| `FORMAL_CHECKS.lean.txt` | Exact scratch input used for the source audit's 29 signature checks and 14 axiom checks; saved as a text artifact. |
| `FORMAL_CHECKS.log` | Successful Lean output for those checks; inspected axioms are standard. |
| `MATHEMATICAL_REVIEW.md` | Independent analytic review of the draft's new examples and scope claims. Its three required scope corrections are resolved in `REVIEW.md`, Section 8. |
| `HIGHER_RANK.md` | Follow-up proving that a genuinely full-rank certificate and an actual infinite BFGS run coexist, in arbitrary finite dimension. |
| `HigherRank.lean.txt`, `HigherRank.log` | Complete new scratch Lean construction and successful compilation/axiom output for the higher-rank calibration. |

The independent reports preserve what was reviewed, including draft line
numbers and references to temporary files. Source paths in them refer to
`a6f46d1`. The original scratch `Checks.lean` is archived here as
`FORMAL_CHECKS.lean.txt`; its `Checks.log` is `FORMAL_CHECKS.log`. The released-PDF
text extractions mentioned in the source audit are reproducible from the PDFs
under `release/`.

The review distinguishes proofs already registered in the Lean package from
new analytic specializations. M42 calls for formal coverage of any additional
examples promoted into the manuscripts. The existing Chapter 7 common-tilt
non-vacuity question remains in `TODO_LEAN_REVIEW.md`.

## Replaying the Lean checks

Copy either `FORMAL_CHECKS.lean.txt` or `HigherRank.lean.txt` to a scratch file
outside the repository with the suffix `.lean`. From `bfgs_lean_article/`, run:

```sh
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean /absolute/path/to/HigherRank.lean
```

The first file checks existing names and their axioms. The second proves the new
calibration, including an explicit Euclidean-norm identity (the library's
`Vec n` has the Pi/sup norm), the complete actual-gradient BFGS run, field rank
exactly `n`, all certificate conditions jointly, and convergence. It compiles
without warnings; all six inspected declarations use only the standard axioms.
These text artifacts record the follow-up checks, not additions to the 15
October package's reported count of 5420 audited declarations.
