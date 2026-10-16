# M42 completion evidence — 16 October 2026

**PASS.** The article additions, their joint Lean hypothesis/run witnesses,
literal coverage, independent reviews and current-source correspondence are
complete. Fresh package-wide evidence was produced on clean commit
`74900ef0a87a17a0715ba5c3ef53e9a36a372621`.

## What was verified

The article's new Appendix E (`paper/appendices/hypothesis_examples.tex`) contains
six named results: a mixed-ridge certificate with an actual infinite BFGS run;
a full-rank quadratic calibration; a general differentiable-step/run existence
criterion; the positive-parameter two-quadratic family; actual runs for the
printed three-quadratic example; and a max-linear differentiable-step obstruction.
The geometry/local sections explain the hypothesis checks and actual witnesses.
The companion explicitly states the known nonexistence cases and remaining open
case of the Chapter 7 common-tilt family.

The mathematical modules are `BfgsArticle/HypothesisExamples.lean` and
`BfgsArticle/TwoQuadraticExample.lean`. Their joint-witness theorems connect the
objective hypotheses, certificate parameters, initial data and actual runs in
one statement. In particular, `TwoQuadraticExample.joint_witness` combines
the planar hypotheses, universal convergence and run existence for every
prescribed differentiable start, SPD matrix and valid constant pair.
`BfgsArticle/Coverage/Article/HypothesisExamples.lean` supplies 29 named literal
coverage theorems, including the mixed run's least spectral value and its limit.

Independent implementer/reviewer/fix-pass records are indexed in
[README.md](README.md). They include separate mathematical, literal-coverage,
source-tooling and actual-metadata reviews. No manuscript hypothesis was weakened
to accommodate a formalization.

## Fresh build, audit and kernel replay

| Check | Result |
|---|---|
| Full package build after the new imports | PASS, 105.14 seconds; all three new modules imported by the root. |
| Build at the evidence commit | PASS, 2.88-second no-op. |
| Axiom audit | PASS, 5506 names, including 3311 coverage-register names; no missing/unresolved names or nonstandard axioms. |
| Principal axiom guard | The existing 182 declarations remain unchanged after `--write-guard`. |
| Project import closure | 788 modules. |
| Independent kernel replay | PASS, 786 modules; no failures. The two import-only roots are `BfgsArticle` and `BfgsVerification`. |
| lean4checker self-test | PASS; deliberately forged declarations rejected. |

All 1244 build warnings come from the hash-pinned main library; the new modules
produce none. The audit took 472.87 seconds (7.9 minutes), with six jobs. The
replay took 1610.02 seconds (26.8 minutes), with eight jobs, on the 10-core
MacBook. Both reports record the same clean source commit and Lean 4.19.0.

Audit axiom sets:

- 5499 declarations: `propext`, `Classical.choice`, `Quot.sound`;
- 5 declarations: `propext` only;
- 2 declarations: `propext`, `Quot.sound`.

The checker is lean4checker `v4.19.0`, commit
`e11f65c651edd58d68ba260015d2bfde5102cd7f`, binary SHA-256
`e04539c18f29bd09e57207809f4ed4b72f464553672ac63293758a91c9589ba4`.
As documented by the replay script, this rechecks every project declaration
in the module closure; Mathlib and Lean core are imported, not replayed.

Committed reports and SHA-256 hashes:

| Report | SHA-256 |
|---|---|
| `bfgs_lean_article/AXIOM_AUDIT.json` | `0411efc45647c571f19e6526d4301bf44f3afa17ee73d88186a14dd1a3f81149` |
| `bfgs_lean_article/KERNEL_REPLAY.json` | `15a06b2efbdb28a761d5e7681410a56c11c869c83269359f082acd7f7053dc5f` |

Copying these reports and rerunning `editorial/assemble_claim_ledger.py` left
both the ledger and its HTML index byte-identical. No second audit was needed.

## Manuscript, correspondence and source binding

- Strict coverage passes for all **2529 items**: 668 article and 1861 companion.
  Totals are DEFINITION 192, LEAN 1134, NON_CLAIM 449, OPEN 13, PART_OF 124,
  PROOF 92 and SAME_AS 525. M42 added 54 classified items; its additional OPEN
  item restates the existing Chapter 7 question, not a new unproved theorem.
- The additions manifest and three bounded passages are independently reviewed.
  Current correspondence passes with **103 listed changes**, preserving all
  77 historical row objects. The ledger has exactly six new article records
  (125 in all); regeneration is deterministic.
- `generate_companion.py --check` passes: 14 chapters, 172 source spans and
  3087 preserved formal exports; all managed outputs match.
- Both PDFs build: **54 article pages, 108 companion pages**. All 57 pages
  changed by the mathematical/expository additions were inspected at 110 dpi.
  The final count/date update changed only companion PDF page 94, which was
  separately rendered and inspected. There are no new LaTeX warnings, overfull
  boxes or undefined references; the companion's two prior underfull boxes remain.
- [SOURCE_BINDING.json](SOURCE_BINDING.json) records PASS for the two existing
  T3 checks in `editorial/verify_release_inputs.py`: source-bound October Lean
  evidence and strict coverage. The checks were executed unmodified in a
  read-only wrapper, excluding the release-receipt writer and unrelated historical
  release gates. They verify the audited ancestor, unchanged bound inputs,
  pinned Lean/checker versions, recomputed name/module counts, and the counts
  printed in `companion/current_verification.tex`.

The working-source follow-up is complete. The archived 15 October release keeps
its original PDFs and validation records; this follow-up does not claim a new
source-archive validation. The Chapter 7 higher-dimensional existence question
and the author's existing questions retain their separate open entries.

## Reproduction

From a clean checkout with the pinned dependencies built:

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd bfgs_lean_article
lake build
LEAN_NUM_THREADS=10 python3 scripts/axiom_audit.py --jobs 6 --write-guard --report /path/to/scratch/AXIOM_AUDIT.json
python3 scripts/kernel_replay.py --checker-repo /path/to/lean4checker --self-test --jobs 8 --report /path/to/scratch/KERNEL_REPLAY.json
```

Use lean4checker v4.19.0. Run the coverage and correspondence checks from the
repository root:

```sh
python3 editorial/lean_coverage/check_coverage.py --strict
python3 editorial/release_20261015/refresh_correspondence.py --check
python3 editorial/generate_companion.py --check
```

The reports describe the source commit named above. Later documentation/report
commits do not change its mathematical inputs; a change to an evidence-bound
input requires refreshing the corresponding evidence.
