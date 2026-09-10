# BFGS principal-minor and reciprocal-growth formalization — stage 1

**Status: DRAFT; NOT COMPILED; NOT LEAN-VERIFIED.**

This project starts formalizing Module M of the supplied BFGS master report.
The execution environment in which these files were prepared had neither Lean,
Lake, nor Elan. Attempts to download the toolchain and packages failed with DNS /
network errors. No `.olean` was produced and no Lean theorem is claimed verified.

The code is a set of candidate proof scripts, not a promise that it compiles.
Compiler errors, including tactic/API mismatches, may remain. The next action is
to compile and repair the drafts in the pinned environment.

## Scope actually represented

| Item | Status |
|---|---|
| Exact matrix definitions and target propositions for M.1–M.3 | Drafted, not typechecked |
| Scalar cancellation in the compressed-determinant argument | Candidate proof scripts |
| Finite weighted-potential recurrence at arbitrary hierarchy height | Candidate proof scripts |
| Geometric/arithmetic reciprocal divergence from `NormalizedHierarchy` | Candidate proof scripts, explicitly conditional |
| Derivation of `NormalizedHierarchy` from the actual full-BFGS update | **NOT IMPLEMENTED** |
| General matrix principal-minor theorem | **NOT IMPLEMENTED** |
| Finite-horizon AM–GM/root bound and superquadratic conclusion | **NOT IMPLEMENTED** |
| Kernel compilation and axiom audit | **BLOCKED / NOT PERFORMED** |

A successful future build of the CURRENT project would prove only the implemented
conditional scalar lemmas. It would not establish the still-open matrix theorem.
The three `...Target` declarations are definitions of propositions, NOT proofs of
those propositions. There are no placeholder theorem proofs for those targets.

## Files

* `BfgsVerification/Definitions.lean`: actual matrices, full inverse-BFGS update,
  principal sums, full matrix runs, and honest unproved end-to-end target statements.
* `BfgsVerification/CompressionAlgebra.lean`: real-algebra portions of the Schur /
  compressed-determinant calculation. Matrix identities remain separate obligations.
* `BfgsVerification/ScalarHierarchy.lean`: finite weighted sum and normalized
  hierarchy interface, including the terminal slot and trace domination.
* `BfgsVerification/ReciprocalGrowth.lean`: finite-prefix-preserving logarithmic
  proof of qualitative reciprocal growth from that explicit interface.
* `Audit.lean`: axiom reports and the full signature of the conditional result.
* `PROOF_OBLIGATIONS.md`: missing matrix bridges and exact source-to-code map.
* `MATHEMATICAL_REVIEW.md`: informal review of the scalar argument and quantifiers.
* `reference/foundation.tex`: unchanged source Module M extracted from the supplied ZIP.
* `scripts/check.py`: fail-closed build/audit driver; static scanning is never
  represented as Lean verification.
* `audit/STATUS.json`: actual execution status for this delivery.

## Reproducible version choices

* Lean: `leanprover/lean4:v4.19.0`
* mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b` (release `v4.19.0`)

These are explicit stable version choices, not claims about the latest release.
The tagged mathlib `lean-toolchain` was checked against the specified Lean version.
The commit was read from the official mathlib release page.

No `lake-manifest.json` has been fabricated: the first `lake update` must resolve
it from the pinned mathlib commit. Keep the generated manifest with subsequent
verified builds. This ZIP does not bundle a compiler or the mathlib cache.

## First compilation

In a terminal with a functioning Elan/Lean installation and network access:

```bash
cd bfgs_lean_stage1
bash scripts/bootstrap.sh
```

This performs `lake update`, `lake exe cache get`, then the build and axiom audit.
After dependencies exist, rerun:

```bash
python3 scripts/check.py
```

A source-only scan is available but is NOT a proof check:

```bash
python3 scripts/check.py --static-only
```

The driver exits nonzero on a missing toolchain, compilation error, timeout,
missing axiom report, or unapproved axiom dependency. It does not use
`native_decide` or import outputs of Python/SymPy as mathematical facts.
The standard mathlib foundational axioms allowed by the audit are `propext`,
`Classical.choice`, and `Quot.sound`.

## What counts as completion

1. Every staged source must compile and its axiom dependency report must be audited.
2. The actual matrix obligations in `PROOF_OBLIGATIONS.md` must be implemented.
3. An exported theorem must inhabit `PrincipalMinorHierarchyTarget` without assuming
   that target or an equivalent unchecked matrix identity.
4. The matrix-to-`NormalizedHierarchy` bridge must be proved and used to inhabit
   `ReciprocalGrowthTarget`.
5. M.3 requires a separately completed finite-horizon and ordered-tail proof.

Until then, do not label the paper's matrix hierarchy or its end-to-end BFGS
reciprocal-growth theorem "Lean-verified."
