# Full BFGS: principal minors and reciprocal growth in Lean

**Module M.1–M.3's original matrix-run targets are compiler-checked.**
The pinned Lean 4.19.0 build and transitive axiom audit succeeded on 10 September
2026. All 115 explicit theorem declarations and 167 theorem declarations including
Lean-generated auxiliaries were audited. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. There are no `sorry`, `admit`, custom mathematical axioms, or
unchecked external mathematical computations.

The original research sources are unchanged. The pre-work draft and report were
committed and pushed as `2c8bb60`. Historical environment-failure logs describe the
previous runtime, not the current proof status.

## Results and exact scope

| Export | Verified conclusion |
|---|---|
| `principalMinorHierarchy` | Inhabits the unchanged `PrincipalMinorHierarchyTarget`: actual full inverse-BFGS matrices, actual sums of principal determinants, arbitrary finite dimension |
| `fullBFGS_normalizedHierarchy` | Derives the scalar hierarchy from those matrices, with `K=4G²/c²`, `C=G²`, and `δ=d/c` |
| `reciprocalGrowth` | Inhabits the unchanged `ReciprocalGrowthTarget`: geometric and arithmetic reciprocal means diverge when predicted decreases tend to zero |
| `finiteHorizon` | The source's explicit real-power finite-horizon lower bound, including the actual tail budget and matrix potential |
| `superquadraticReciprocalGrowth` | Inhabits the unchanged `SuperquadraticReciprocalTarget`: reciprocal sums divided by `N²` tend to infinity under summability |

The exported growth results use `FullBFGSRun`, the original algebraic specification
of the unmodified full matrix update, with bounded gradients and a positive fixed
lower bound on beta. The accepted-step weak-Wolfe inequality implies this beta
bound by `FullBFGSRun.beta_ge_of_weakWolfe`. The growth assumptions are vanishing
or summable predicted decreases, respectively. No iterate/matrix convergence or
uniform matrix bound is assumed. No L-BFGS or update modification occurs.

This project does **not** claim a formal model of finite convex objectives,
differentiability of accepted iterates, or Armijo-to-summability/compact-sublevel
bounded-gradient deductions. Those objective-level connections and the other
research modules remain outside this matrix-run formalization. See
[MATHEMATICAL_REVIEW.md](MATHEMATICAL_REVIEW.md) and
[audit/STATEMENT_REVIEW.md](audit/STATEMENT_REVIEW.md) for the statement review.

## Reproduce

Pinned versions are unchanged:

- Lean: `leanprover/lean4:v4.19.0`
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`
- Transitive package revisions: generated and committed `lake-manifest.json`.

With Elan/Lake available:

```bash
cd bfgs_lean_stage1
bash scripts/bootstrap.sh
```

The current workspace keeps Elan in `.toolchain/elan`, dependencies and compiled
objects in `.lake`, and downloaded caches in `.cache`, all inside this repository
and ignored by Git. `bootstrap.sh` and `check.py` discover the local installation.
To install Elan locally in a fresh checkout:

```bash
mkdir -p .toolchain/elan
curl --proto '=https' --tlsv1.2 -sSfL \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o .toolchain/elan-init.sh
ELAN_HOME="$PWD/.toolchain/elan" bash .toolchain/elan-init.sh \
  -y --no-modify-path --default-toolchain none
bash scripts/bootstrap.sh
```

On this macOS runtime the pinned native mathlib cache utility failed to load with
`__DATA_CONST segment missing SG_READ_ONLY flag`. Bootstrap disables the native
cache post-update hook and runs the **same pinned cache program** with
`lake env lean --run`. This concerns download tooling, not proof trust. No
toolchain or mathlib revision was changed.

For subsequent checks:

```bash
python3 scripts/check.py
```

After the audit output log has closed, `python3 scripts/manifest.py` regenerates
the delivered artifact hashes in `MANIFEST.json`.

`--static-only` is explicitly **not** Lean verification. The default checker
verifies the compiler and mathlib revision, builds the library, enumerates the
compiled environment, checks every explicit source theorem has an axiom report,
and rejects unexpected transitive axioms. `Audit.lean` additionally requires
terms of the exact original targets and prints their definitions and full key
signatures. Verification is not inferred from names or compilation alone.

## Evidence and organization

- [audit/STATUS.json](audit/STATUS.json): actual status, source hashes, every
  explicit theorem's signature/dependencies, conditional reusable stages, and
  remaining target obligations.
- [audit/build.log](audit/build.log), [audit/axioms.log](audit/axioms.log): current
  compiler and complete axiom/type audit transcripts.
- [audit/lean_version.log](audit/lean_version.log),
  [audit/mathlib_revision.log](audit/mathlib_revision.log): actual pinned versions.
- [audit/declarations.json](audit/declarations.json): all audited theorem records.
- [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md): source-to-proof completion map.
- [audit/HISTORY.md](audit/HISTORY.md): historical versus current evidence.

The matrix chain runs through `PrincipalMinors`, `GramSchur`,
`CompressionDeterminant`, `BFGSUpdate`, `BFGSCompression`, `PrincipalInvariance`,
`PrincipalCombinatorics`, `CoordinateGram`, `OrthogonalCoordinates`, and
`PrincipalHierarchy`. `Normalization` connects this to `ScalarHierarchy`,
`ReciprocalGrowth`, and `QuantitativeGrowth`. `EndToEnd` exports the complete
matrix-run results. Conditional helper premises are discharged in `EndToEnd`.
