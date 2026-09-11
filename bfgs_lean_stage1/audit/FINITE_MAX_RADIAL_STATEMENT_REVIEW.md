# Finite C2 maximum branch test and radial-jump obstruction

Source: Module R, “Finite maxima: a simple branch test.” The original source is unchanged.

## Sufficient condition

`FiniteMaxScalarCalculus` proves the actual derivative and derivative Lipschitz bound for a finite scalar maximum whose active branch first derivatives agree. It never assumes a finite number of switches. Finiteness eliminates inactive *value* gaps locally; the derivative at a point is derived from the finite sum of actual derivative remainders. This gives an actual continuous derivative selection and a uniform centered local bound. A Dini mean-value theorem globalizes that bound on an interval with the same Lipschitz constant. Continuity of the selected derivative is proved, not assumed.

`FiniteMaxRadialSufficiency` supplies the vector/objective bridge. Its hypotheses are an actual finite convex objective, a local equality with the actual finite maximum of C2 branches on an open neighborhood of the center, and equality of the actual branch derivatives applied to `w-star` at every active tie in that neighborhood. The branch functions need not be convex separately in this stronger proof; the source's convex C2 branch hypothesis therefore implies the formal hypotheses. The condition uses actual `fderiv`, not an independently supplied gradient field.

The proof derives a common local derivative Lipschitz constant for the finite family from its C2 regularity. At each sufficiently close point, the scalar radial curve remains in that regularity neighborhood for a fixed open interval containing `[0,1/2]`. Active radial derivative agreement is converted to equality of the scalar branch derivatives by canceling the strictly positive dilation factor. The scalar finite-maximum theorem gives a derivative Lipschitz constant bounded by the branch constant times the squared radial norm. Convexity of the actual objective then gives the inward Taylor estimate, including at nondifferentiable sampled points of the full objective.

`local_finite_max_inward` and `local_finite_max_radial` derive uniform IR and RS on a fixed neighborhood. `local_finite_max_basin` derives a positive starting objective level before quantifying over actual full-BFGS runs, gives confinement to the original neighborhood, and proves objective and iterate convergence at an attained unique minimizer. Compactness is derived from localization. `finite_max_compact_basin` also preserves the source's nonunique-minimizer compact-basin setup: it concludes objective convergence and actual Euclidean distance to the entire minimizer set, with iterate convergence additionally under uniqueness.

There is no assumed iterate/matrix convergence, finite branch switching, eventual branch identification, C1,1 regularity of the full spatial objective, or convergence of a BFGS subsequence. Fractional radial norm bounds use the ambient norm only to derive finite constants; the pointwise radial condition is exactly the source's derivative pairing and the solution-distance output is explicitly Euclidean.

## Necessary no-jump condition

`FiniteMaxRadialObstruction` proves a stronger elementary local statement: two actual active convex branches, each dominated by the actual objective on a neighborhood, with radial derivative gap `J>0`, force the exact lower bound `centralDifference ≥ J*t` for nonnegative small t. The branches need not form the entire maximum family and need no C2 hypothesis for this supporting-plane lower bound.

This exact linear lower bound excludes every local quadratic central-difference upper bound. Using the verified RS-to-central theorem, `active_gap_forbids_radial` rules out RS when the tie is **nonoptimal and strictly below the structural upper objective level**. These margins put the tie in the positive nested-band setting of the source. The theorem must not be relabeled a BFGS failure or a nonconvergent trajectory.

The source's “necessary” interpretation must retain the positive-band qualification: a tie at optimal objective value is not in an RS positive band. Nor does this unit claim necessity of radial compatibility for BFGS convergence itself. Both distinctions are explicit in the formal statements.

The literal two-sided expansion `J*|t| + O(t²)` remains a separate explanatory assertion. With more than two active branches its exact coefficient is the maximum active radial derivative minus the minimum active radial derivative; an arbitrary pair gap only supplies a lower bound. The compiled linear bound already proves the stated no-jump obstruction, but is not counted as the full asymptotic expansion.

## Compiler and axiom evidence

The 13 scalar-calculus and six obstruction declarations have successful actual main import builds and scoped axiom audits, with exact requested/output name matching and only `propext`, `Classical.choice`, and `Quot.sound`. Logs are `finite_max_scalar_calculus_{build,axioms}.log` and `finite_max_radial_obstruction_{build,axioms}.log` with their correspondingly named `Audit.lean` files. The nine-declaration sufficiency unit also passed its actual main import build and scoped audit (`FiniteMaxRadialSufficiencyAudit.lean`, `finite_max_radial_sufficiency_{build,axioms}.log`), with exact name matching and only the same standard axioms. Thus all 28 branch-core declarations have independent scoped evidence.

No source file contains a `sorry`, `admit`, custom mathematical `axiom`, or `native_decide`.
