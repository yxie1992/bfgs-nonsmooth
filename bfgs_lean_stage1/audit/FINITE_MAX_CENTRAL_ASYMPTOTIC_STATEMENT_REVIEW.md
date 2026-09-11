# Literal finite-maximum central asymptotic

Source: R.tex lines 243–250, particularly the retained `J|t|+O(t²)` statement. This independently compiled main file supplements the frozen `FiniteMaxScalarCalculus`, `FiniteMaxRadialObstruction` and `FiniteMaxRadialSufficiency` modules; it does not change them or the original source.

## Exact exports

`finite_branch_radial_remainders` derives a common quadratic Taylor remainder along any fixed direction r from the actual finite family of C² branches on an open neighborhood. It uses the checked local derivative-Lipschitz theorem and actual derivative Taylor estimate. There is no assumed remainder oracle or scalar second-derivative formula.

`activeRadialSet` is the actual set of branch indices attaining the finite maximum at w; `mem_activeRadialSet_iff` exposes its literal value condition. `activeRadialJump` is the supremum active directional derivative minus the infimum active directional derivative. It is nonnegative, and is zero exactly when every active branch has the same directional derivative.

`finite_max_central_remainder` assumes only an actual local finite-maximum representation and actual C² branch regularity. It proves that, for a derived C≥0 and all t sufficiently close to zero,

`|F(w+t r)+F(w−t r)−2F(w)−J|t|| ≤ C t²`.

The full active maximum replaces the original family only after deriving local exclusion of inactive branches from their strict value gaps and continuity. No finite-switching or active-identification premise is used. The remainder calculation covers t of either sign and the zero direction.

`finite_max_central_isBigO` specializes r=w−star and exports the literal mathlib asymptotic statement at the two-sided neighborhood filter of zero. `finite_max_central_not_isBigO` proves that J>0 excludes an O(t²) central difference. `finite_max_central_quadratic_iff` gives the exact pointwise equivalence with equality of all actual active radial derivatives.

## Source qualification

With more than two active branches, the exact coefficient in the asymptotic is **max(active derivatives)−min(active derivatives)**. An arbitrary chosen pair's positive difference need not be the exact leading coefficient, although it gives the previously checked lower bound. The source wording is retained; its `J` must be read as the full jump range for the literal equality.

This is a pointwise central-difference criterion. It does not assert that positive-band RS tests every optimal tie, nor replace the nonoptimal-point/strict-upper-level qualifications of the existing not-RS theorem. A nonzero reference direction and convexity are unnecessary for the C² expansion itself, so the expansion theorem validly has weaker assumptions than the source's convex-branch setting.

No BFGS convergence or divergence claim is added by this asymptotic unit. The finite-max sufficient basin theorem and the positive-band obstruction remain separate, already checked results.

## Reproduction

- `source scripts/env.sh; lake env lean audit/scratch/finite_max_asymptotic/FiniteMaxCentralAsymptotic.lean`
- `source scripts/env.sh; lake env lean audit/scratch/finite_max_asymptotic/FiniteMaxCentralAsymptoticAudit.lean`

The embedded audit checks 14 theorems and two actual definitions. Logs and source hash validation remain in this scratch directory until a later tranche imports the file.

Main import `BfgsVerification.FiniteMaxCentralAsymptotic` and 16-name audit both passed; see `FiniteMaxCentralAsymptoticAudit.lean`, `finite_max_central_asymptotic_{build,axioms,validation}.log`. The scratch history is retained. These additions postdate seventh milestone f820c46 and await the next whole-project audit.
