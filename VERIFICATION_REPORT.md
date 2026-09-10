# Verification, reproducibility, and proof status

**Fresh audit date: 10 September 2026. All 19 requested jobs completed with exit code zero and PASS status.** These are reruns of preserved source scripts in isolated writable directories. They are not an independent mathematical review. The exact commands, script hashes, environment and output paths are recorded in `verification/fresh/SUMMARY.json`.

## What the checks mean

Four distinct evidential levels must not be conflated. Symbolic identities and exact rational arithmetic prove the specific finite statements that they actually compute. Rational interval enclosures additionally certify continuum assertions such as an isolated root or strict signs over a box, when paired with the stated contraction or sign argument. High-precision non-interval computations are numerical regressions, not rigorous enclosures. Infinite-trajectory, compact-cluster, geometric joining and stable-manifold conclusions require their analytic proofs; running many iterations does not replace those arguments.

The negative program and positive program have independent foundations. The deterministic negative seed does not use the principal-minor lemma. The positive-curvature negative extension adds a hyperbolicity certificate and a standard stable-manifold theorem. The positive convergence family uses the principal-minor hierarchy and comparison energies. No published theorem for a modified or limited-memory algorithm is used as a substitute for full BFGS.

## Fresh execution register

| Job | Arithmetic / role | Result | Seconds |
|:--|:--|:--:|--:|
| `D-root` | Exact rational intervals | PASS | 0.723 |
| `D-symbolic` | Symbolic identities | PASS | 6.196 |
| `D-full-oracle` | Exact rational intervals | PASS | 1.041 |
| `L-hyperbolicity` | Exact rational intervals | PASS | 0.797 |
| `L-embedding` | Exact rational intervals | PASS | 1.215 |
| `A-minors` | Exact rationals | PASS | 2.981 |
| `H-lifting` | Exact rationals | PASS | 0.917 |
| `M-mixed` | Exact rationals | PASS | 2.070 |
| `P-polyhedral` | Exact rationals | PASS | 1.224 |
| `R-secant` | Exact rationals | PASS | 1.129 |
| `R-interpretation` | Exact rationals | PASS | 0.780 |
| `G-obstruction` | Exact rationals | PASS | 0.640 |
| `V-ridges` | Exact rationals; auxiliary proof | PASS | 2.677 |
| `T-certificate` | Rationals plus decimal logs | PASS | 1.386 |
| `C-planar` | Symbolic / exact rationals | PASS | 1.217 |
| `U-multidimensional` | Exact rationals | PASS | 0.935 |
| `C-planar-numerical` | 140-digit, not interval | PASS | 3.229 |
| `U-multidimensional-numerical` | 100-digit, not interval | PASS | 1.993 |
| `G-oscillatory-numerical` | 220-digit, not interval; auxiliary | PASS | 0.712 |

## What each suite actually checks

### D-root

Existence/uniqueness of the algebraic seed; every accepted and rejected trial; matrix positivity; embedding constants. Raw transcript: `verification/fresh/D-root/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### D-symbolic

Independent inverse/Hessian update closure and secant identities. Raw transcript: `verification/fresh/D-symbolic/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### D-full-oracle

45 accepted updates and 135 actual trials across five shrinking identity-initialized starts; complete global oracle. Raw transcript: `verification/fresh/D-full-oracle/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### L-hyperbolicity

Normalized Jacobian, characteristic-polynomial signs, stable/unstable eigenvalue separation, embedding bounds. Raw transcript: `verification/fresh/L-hyperbolicity/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### L-embedding

336 affine-plateau checks, 228 ramp checks, 72 full local value/gradient identities. Raw transcript: `verification/fresh/L-embedding/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### A-minors

125 update cases, 1,425 compressed identities and 375 minor-hierarchy inequalities. Raw transcript: `verification/fresh/A-minors/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### H-lifting

100 projected-update and invariant-subspace cases. Raw transcript: `verification/fresh/H-lifting/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### M-mixed

425 accepted-step cases; 1,030 minor inequalities; 425 weighted-potential checks; 684 compression identities; matrix-limit example. Raw transcript: `verification/fresh/M-mixed/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### P-polyhedral

144 accepted steps, including 72 with a C1,1 but non-C2 smooth part; 40 lifting checks. Raw transcript: `verification/fresh/P-polyhedral/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### R-secant

1,500 finite-max pair checks, sum/composition checks, 825 powered-gauge cases including 165 fractional-power cases, 90 accepted steps. Raw transcript: `verification/fresh/R-secant/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### R-interpretation

600 endpoint-pair cases and 1,800 inward Taylor inequalities; supporting-plane, boundary and strictness examples. Raw transcript: `verification/fresh/R-interpretation/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### G-obstruction

24 common-target obstruction cases, 117 SPD step realizations, 60 accumulating-kink cases, 150 rank-one feasibility checks. Raw transcript: `verification/fresh/G-obstruction/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### V-ridges

370 accepted steps, 263 crossings, 107 same-mode steps, 270 asymmetric-slope cases, 90 degenerate cases, 80 matrix-frame checks. Preserved as corroboration of a now-subsumed theorem. Raw transcript: `verification/fresh/V-ridges/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### T-certificate

96 projected-PSD energy cases, 384 accepted steps, 36 strictness examples. 208 logarithmic rescaling checks use 70-digit Decimal arithmetic and are not exact interval certificates. Raw transcript: `verification/fresh/T-certificate/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### C-planar

Angular and determinant identities; 90 full-BFGS moving-energy cases; explicit quadratic barycentric/basin checks; 3D field obstruction. Raw transcript: `verification/fresh/C-planar/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### U-multidimensional

72 full-matrix residual-energy cases, 150 cutoff transports, 87 minor inequalities, 18 finite-horizon tail checks, 23 spike-node identities, 161 infinite-series oracle cases. Raw transcript: `verification/fresh/U-multidimensional/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### C-planar-numerical

18 actual full-BFGS runs; 3,084 updates, 7,381 trials; all reached F < 1e-45. Its repeated exact stage is not counted twice. Raw transcript: `verification/fresh/C-planar-numerical/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### U-multidimensional-numerical

Nine actual full-BFGS runs in dimensions 3, 5 and 8; 495 updates and 1,050 trials; all reached F < 1e-28. Complete infinite-series oracle; repeated exact stage not counted twice. Raw transcript: `verification/fresh/U-multidimensional-numerical/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

### G-oscillatory-numerical

24 finite incoming-pair checks for the source oscillatory example. Historical auxiliary geometry, not a main BFGS counterexample. Raw transcript: `verification/fresh/G-oscillatory-numerical/stdout.txt`; the job entry in `SUMMARY.json` identifies every generated JSON result and the executed command.

## Analytic steps that still require independent review

| Result or proof component | Supplied evidence | What was not established by finite reruns |
|:--|:--|:--|
| Principal-minor hierarchy | Complete Gram-determinant proof; exact algebra cases | A third-party audit of the general proof |
| Reciprocal growth and the superquadratic tail theorem | Finite-horizon algebra and explicit ordered-limit proof | Any empirical inference from a finite horizon to an infinite limit |
| Transported certificate and radial equivalence | Full proof and identities | Uniform hypotheses for an arbitrary unlisted objective |
| Planar affine-critical theorem | Geometric joining proof; exact local identities; numerical example | Independent validation of the compact-neighborhood, joining and all-segment arguments |
| Fixed-normal multidimensional theorem | Residual-energy and cutoff proof; exact identities; full-series numerical oracle | A theorem for rotating normals or arbitrary curved active manifolds |
| Deterministic C2,1 local counterexample | Isolated algebraic root, symbolic closure, strict all-trial decisions, exact interpolation and containment induction | A positive-measure basin, robustness to floating-point perturbations, or a different line search |
| Positive-curvature counterexamples | Certified hyperbolicity plus the analytic return map and stable-manifold theorem | A numerical starting vector proved to lie exactly on the stable manifold |
| Semialgebraic affine-critical gap | Source-derived geometric proof using standard tame-geometric facts | A blanket semialgebraic BFGS convergence theorem |

All retained results remain working mathematical claims pending independent review. A successful source script can validate a mistaken formula if the same mistake occurs in its construction and checks; independent inverse/Hessian forms and separate symbolic/interval routes reduce, but do not eliminate, that concern. No publication-priority certification is made.

## Reproduce the audit

From the package root, with Python 3.13 (or a compatible Python), SymPy 1.14.0 and mpmath 1.3.0:

```bash
python -m pip install -r requirements.txt
python verification/run_all.py --workers 3 --timeout 600
python verification/run_all.py --numerical --workers 3 --timeout 600
```

The first command runs the non-optional algebraic suites; note that the transported source suite includes explicitly labeled decimal-log checks. The second includes the optional high-precision runs. Each selected job receives a new working copy of its module, so scripts may write their normal outputs without modifying `verification/modules/`. Existing fresh logs are output artifacts, not the source inputs; preserve them before a new audit when comparison is desired.

The exact environment for this run was:

```text
python: 3.13.5 (main, Jul 15 2026, 20:25:40) [GCC 14.2.0]
platform: Linux-6.18.35-x86_64-with-glibc2.41
sympy: 1.14.0
mpmath: 1.3.0
```

No verification job requires network access. Scripts under `verification/modules/` preserve the source versions; `verification/historical/` contains the old logs, while `verification/fresh/` contains this execution. Counts from old files are never represented as fresh checks, and exact stages repeated inside numerical scripts are not double-counted. The per-job script hash and the complete package manifest support later comparisons.

## Rebuild the report

```bash
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error master.tex
```

The editable report sources are complete. `report/tools/assemble.py` reconstructs selected proof modules from the preserved source snapshots; it is an editorial tool, not part of a theorem verifier. The authored common foundation, structural corollaries, affine-critical geometry, inventory and audit are separate editable chapters. Details of intentional changes appear in `EDITORIAL_NOTES.md` and `report/EDIT_MANIFEST.json`.
