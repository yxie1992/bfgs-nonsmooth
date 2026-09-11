# BFGS master report: reconstructed and corrected edition

This companion defines the corrected edition together with the preserved
`BFGS_MASTER_REPORT_LaTeX/report/master.tex` and its 14 included chapters.
Every original mathematical assertion is retained with its original scope,
except for the explicit corrections below. Explicit conjectures and questions
remain questions. The original research files remain unchanged.

The user has clarified that the sources were AI-generated, the missing source
inputs are unavailable, and new inputs should be generated from the report's
proof. This authorizes the new construction and evidence package. It does not
establish whether the report's historical jobs ran. Unsupported historical
assertions are withdrawn from this corrected edition and preserved only in the
original snapshots.

## Verification scope

The final release must check every retained mathematical source span, the new
construction, all exact theorem contracts and transitive axioms, and all 19
newly specified execution jobs. The original source register contains 14
modules, 172 disjoint spans and 4,323 chapter lines. Its links identify actual
Lean exports and reviewed hypotheses, including reusable conditional criteria
and their objective applications.

The algorithm throughout is unmodified full BFGS with Armijo and weak Wolfe,
positive accepted lengths and differentiable accepted iterates. No L-BFGS,
matrix or iterate convergence assumption, arbitrary-ray step-existence claim,
or blanket convergence theorem for all finite convex objectives is introduced.
There are no placeholders, custom mathematical axioms or unchecked external
computations in the proofs. The permitted transitive axioms are `propext`,
`Classical.choice` and `Quot.sound`.

**Verified corrected edition:** the pinned Lean 4.19.0 build checked
5,195 explicit theorems, 7,813 total theorem declarations and all 255
exact targets, with 737 frozen Lean sources. All 19 newly authored jobs passed
107 strict literal type/axiom checks covering 93 distinct theorem names.

## Explicit reconstruction of R's four-piece illustration

Let `c` and `d` be the actual certified algebraic seed parameters of Module D,
implemented by `SeedOrbit.seedC` and `SeedOrbit.seedD`. Define

\[
\delta=c-16d-1>0,\qquad a=\frac{25}{4\delta}>0,\qquad
T(u,v)=(u,16v/5).
\]

For the verified coercive four-piece D objective `F_D`, set

\[
F_R(z)=aF_D(Tz)+a-1.
\]

Equivalently, this is the maximum of the following four affine functions:

\[
\begin{aligned}
 &au+a-1,\\
 &a(-u-2v/5)+a-1,\\
 &a(cu+16dv/5)+a-1,\\
 &16av/5-16a-1.
\end{aligned}
\]

The positive number used in the denominator is the actual third supporting
error of D, not the negative value of its third branch. The positivity proof
comes from the certified D parameters. The new objective is finite, convex and
has compact sublevels. Its unique minimizer is `(-1,5)` with value `-1`. The
first three branches there have values `-1,-1,-29/4`, hence supporting errors
`0,0,25/4`.

For the actual D run, write its iterates, gradients and inverse matrices as
`x_k`, `g_k` and `H_k`. The new run is explicitly

\[
\widehat x_k=T^{-1}x_k,\qquad
\widehat g_k=aT^Tg_k,\qquad
\widehat H_k=a^{-1}T^{-1}H_kT^{-T}.
\]

Accepted lengths and both line-search parameters are unchanged. The original
certified parameter range is `0<c1≤1/3` and `c1<c2<1`. Actual derivatives,
initial SPD, the literal full update and both acceptance inequalities are
proved under that range. The new points converge to zero, their strictly
decreasing values converge to `a-1>-1`, and zero is not stationary. This is an
actual infinite BFGS failure example, not an assumed trajectory.

Every three phases repeat the exact supporting errors `0,0,25/4`. Actual
positive secant curvature is multiplied by `a` and tends to zero. On one fixed
positive band of the actual initial sublevel, successive phase-one/phase-two
iterates therefore contradict any proposed supporting-plane bound. The actual
SP and RS conditions fail on that sublevel.

The defining namespace is `BfgsVerification.ReconstructedFourPiece`.
The complete targets are `ReconstructedFourPieceFailureTarget` and
`ReconstructedSupportingPlaneTarget`; their inhabitants are
`reconstructedFourPieceFailure` and `reconstructedSupportingPlane`.
The reusable positive-value transformation is separately verified by
`objectiveValueScaling : ObjectiveValueScalingTarget`.

This is a newly defined realization of R182–187. It does not identify or recover
an older objective. The original D objective still has optimizer `(-1,16)`;
the theorem showing that its value at `(-1,5)` is at least `3/8` remains valid.

## Mandatory corrections inherited from the full review

These nine correction identifiers retain their exact source and proof/review
links in `audit/REPORT_STATUS.json`.

| Identifier | Corrected mathematical meaning |
|---|---|
| `G.accessible_vs_active_span` | Accessible jumps need not span every active-gradient difference. Visibility yields a nonzero component perpendicular to the accessible span. The full common-active tangent conclusion requires spanning or actual annihilation of all differences. A verified finite strongly convex objective distinguishes the two assertions. |
| `Q.printed_pair_armijo_range` | The printed epsilon/2 pair satisfies Armijo exactly for `c1≤2/3`. A separately constructed rho family gives the claimed separation for every allowed `c1<1`; the original pair is not used beyond its actual range. |
| `C.negative_orientation_transport_sign` | When `det(T,n)=-1`, the signed determinant is `s_n*((a-e)*s_T+b*s_n)`. The corrected sign preserves the absolute estimates and resulting convergence statements. |
| `U.variable_jump_nonadditivity_zero_parameter` | The nonsplitting assertion needs `c≠0`. The source condition `‖c‖<1` permits `c=0`, where splitting exists. The convergence claim retains the zero case. |
| `R.degree_zero_intercept_normalization` | For general homogeneity degree, the actual intercept is `(p-1)F(x)+F(0)`. Positive degree implies `F(0)=0`; degree zero requires the extra constant term. |
| `R.historical_four_piece_attribution` | Current D has optimizer `(-1,16)` and supporting errors `0,0,-1+c-16d`. The new R objective above realizes the printed different tuple. This is an explicit reconstruction, not a changed claim about D. |
| `C.constant_rank_field_regularity` | C2 branches give a C1 gradient family and C1 common-rate field. No C-infinity field or higher-dimensional projected transport follows from those assumptions. |
| `L.Jacobian_lower_left_nearest_rounding` | The nearest 15-decimal lower-left entry is `0.751501570427498`. The original entry is still within `10^-15`; the exact derivative enclosures and hyperbolicity result are unchanged. |
| `D.five_nearest_decimal_roundings` | Correct nearest values are `-0.004954238005`, `0.375205963573`, `-0.817119670485`, `0.468627450980` and `0.635765118557`, respectively for the final point ordinate, Armijo ratio, Wolfe ratio, b=2 scalar center and lower plateau. Actual errors are proved below half a displayed unit. |

All previously documented proof-route replacements remain documented. In
particular, M's exact Gram-sum and sharp polynomial-degree assertions now have
their own proofs, alongside the unchanged original principal hierarchy and
reciprocal-growth proof chain. Changing a proof route is not an added theorem
hypothesis.

## Replacement for E's unsupported execution record

The September 10 PASS statuses, case/run counts, elapsed times, numerical
precisions, environment strings and archive identities in the original E and
`VERIFICATION_REPORT.md` are unsupported by recoverable source inputs or
process records. They are superseded in this edition. Newly generated scripts
and logs do not verify those original historical assertions.

The replacement retains all 19 source category labels and mathematical roles.
Each category is a newly authored pinned Lean job with explicit theorem
declarations, independently frozen complete type contracts and ordinary
transitive-axiom reports. The runner records actual commands, working
directories, UTC timestamps, exit codes, durations, environment and source/log
hashes. Shared proof imports and repeated contracts are distinguished from
unique declarations; arbitrary repetition is not counted as mathematical
coverage.

The role map includes D's actual algebraic root, inverse and Hessian identities,
all accepted/rejected trials and shrinking identity starts; L's actual
hyperbolicity, ramps, plateaus and local identities; the full principal/minor
and weighted-potential theory including the unexcited-matrix limit example;
lifting; the C1,1 polyhedral family; radial families and interpretations;
obstruction, accumulating-kink and rank-one geometry; asymmetric and degenerate
ridges; exact PSD transport and logarithmic normalization; planar examples and
spatial obstructions; and U's full residual, cutoff, tail and infinite-series
oracle results.

Three category labels require explicit interpretation:

- `C-planar-numerical` is a universal theorem counterpart. Under the actual
  printed planar basin hypotheses, every admissible run eventually has value
  below `10^-45`. No 140-digit run, observed stopping index, old trial count or
  iteration-complexity bound is asserted.
- `U-multidimensional-numerical` is a universal theorem counterpart for the
  actual infinite-spike objective in arbitrary dimension, with its unit-normal
  hypothesis. Values eventually fall below `10^-28`. No 100-digit numerical run
  or old finite execution count is asserted.
- `G-oscillatory-numerical` replaces the unspecified archived auxiliary by the
  accumulating-kink function actually defined in G. Its eligible incoming
  pairs, gradients, curvature, quotient divergence and neighborhood
  noncertificate conclusions are checked. This is an explicit auxiliary
  substitution, not recovery of an unidentified oscillatory formula or a bad
  BFGS trajectory, and not 24 claimed 220-digit computations.

The finite/interval/numerical/analytic distinctions in E remain in force.
Kernel-checked infinite dynamics, compactness, joining, stable-manifold and
semialgebraic arguments supply the analytic conclusions. No positive-measure
or floating-point-robust failure basin, rounded point on a stable manifold,
general rotating-normal result, arbitrary alternative line search or blanket
semialgebraic convergence claim is added. Agent statement reviews are not
represented as independent human reviews or publication-priority evidence.

## Completion record

The retained mathematics of this corrected edition, its explicit reconstruction,
and the new execution evidence have passed their respective gates. The complete
compiler transcript is [report_reconstruction_check.log](audit/report_reconstruction_check.log),
with [central status](audit/STATUS.json), [all transitive reports](audit/axioms.log),
and [737 source hashes](audit/report_reconstruction_source_hashes.json).
The [new nineteen-job summary](verification/reconstructed/fresh/SUMMARY.json)
contains actual commands, results and artifact links. The
[source register](audit/REPORT_STATUS.json) covers all 14 modules and 172 spans;
the [independent completion review](audit/REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md)
and [closing validation](audit/report_reconstruction_documentation_validation.log)
record the source/type/axiom/evidence correspondence.

`corrected_report_verified` is true for this explicit edition.
`original_snapshot_all_assertions_verified` and legacy `entire_report_verified`
remain false: neither the older unidentified objective attribution nor the
original execution history has been recovered. The reconstruction removes the
need for those unavailable inputs without representing new evidence as old.

Run `bash scripts/bootstrap.sh` to establish the pinned build. Then run
`python3 verification/reconstructed/run_all.py` for the new nineteen-job suite,
and `python3 scripts/validate_report_reconstruction_19.py` for the completed
source, theorem, axiom and evidence gate. Existing source-review and scoped
audit logs remain bound to their unchanged proof-source hashes.
