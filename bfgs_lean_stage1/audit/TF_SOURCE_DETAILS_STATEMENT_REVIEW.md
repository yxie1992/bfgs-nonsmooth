# T/F final source-detail statement review

Read the complete retained T.tex and families.tex against their inventories and
the actual exported statements. This review closes two proof details and
reconciles the previously completed applications. It is not a claim of whole-report
completion. The source files remain unchanged.

`ComparisonEnergyWarning.comparisonEnergyWarning` concerns the actual matrices
diag(1,(k+1)^4), reference vector (1,0), and moving vector (1,1/(k+1)). The matrices
are positive definite; the vectors approach the reference; reference energy is
one; and the energy increase tends to infinity. This supplies the algebraic
warning in T.tex206. It does not assert a BFGS trajectory for these matrices, or
that every convergent objective needs a transported certificate. Those would be
different and unjustified conclusions.

`AffineProjection.actualImageRange` proves range(H_k A^T)=range(H_0 A^T) for an
actual arbitrary-dimensional full-BFGS run on F composed with a full-row-rank A.
The transpose-gradient representation is derived from that objective. The fixed
image follows from the actual update invariant and positive-definite compressed
matrices, with no iterate or matrix limit premise. The already audited
`linearImageLifting` separately proves the source's full-space convergence and
the H_0^{-1}-metric fiber selection, under the explicitly stated convergence of
the projected run. The new equality closes families.tex85–90's invariant-space
argument; it does not replace the projected-run hypothesis by an assumed limit
of the full run.

Delivered-only reproduction is `bash audit/verify_tf_source_details.sh`.
The two-file manifest covers 15 actual declarations and two exact Prop targets.
The validator checks actual compiler success, every declaration's transitive
axioms, exact target type equality, and source hashes. Independent review and
fresh peer output are in TF_SOURCE_DETAILS_INDEPENDENT_REVIEW.md and
tf_source_details_peer_{axioms,validation}.log. The full thirteenth audit must
also pass before the report register publishes these results.

## Complete retained T source reconciliation

| Source lines | Actual Lean coverage |
|---|---|
| 1–24 | TeX notation/counter preamble, no mathematical assertion. |
| 25–73 | AdmissibleBFGSRun, EligiblePair, accepted_pair_eligible; actual convex upper-decrease bound, positive curvature and nonzero step. |
| 74–147 | transportedCertificateConvergence, certificate_trace_step and the actual M reciprocal growth theorem. Every positive band/all small eligible pairs, finite PSD field values; no uniform field bound or matrix convergence added. |
| 148–156 | Local unique and compact entire-solution-set basin theorems, structural-sublevel restriction, and one-sided shell certificate convergence. All quantify the basin before runs/initial SPD matrices. |
| 157–182 | rank_one_transport, projected_transport_iff_perpendicular, PotentialBandCertificate.absorb_constants. Singular fields, zero transport factor and bounded potentials have their literal scope. |
| 183–209 | radial_implies_band_certificates; actual Q parabolicCertificate/parabolicPrintedField and parabolicEligibleSeparation/parabolicNonnecessity; full affineCertificateCovariance; comparisonEnergyWarning. |

Q's explicit curved objective supplies strict separation of sufficient
conditions, including the literal printed field and an eligible-pair radial
failure. This is not a negative BFGS run. The previously pending nonunique basin
and affine covariance are already present in the pinned full audit. The new
energy warning is the last auxiliary source detail.

## Complete retained F source reconciliation

| Source lines | Actual Lean coverage |
|---|---|
| 1–24 | CenteredSmoothSublinear correction/recentering calculus; centeredSmoothConvergence and centeredLocalBasin. Original summands need not separately minimize at the center. |
| 25–50 | transformedGaugeConvergence and actual inverse/Theta derivative; compact sublevels, Euler/chain rule and the stated correction coefficient. Nonlinear-transform invariance is not used. |
| 51–74 | MaxAffine local active identity, inactive radii including parallel slopes, actual extended-real threshold/attainment/strict gap and threshold_tail_convergence. |
| 75–91 | Actual finite scalar absolute/hinge/quantile and Euclidean residual decompositions and local basins; linearImageLifting and actualImageRange. The general nonzero-gauge residual still explicitly requires its local C1,1 property. |
| 92–145 | Actual M finite-horizon bound; linearCorrectionRate, homogeneousRates, quadraticGaugeRates, exact correction constants and finite square-root budgets, big-O and little-o logarithmic conclusions. Rates count accepted iterations for a fixed instance. |
| 146–165 | Literal UnexcitedMetric infinite run and its arbitrary tangential limit; strict finite-bad-ray step existence and named residual classes; actual FivePieceObstruction including neighborhood scaling. |

The finite-ray existence conclusion is proved with the actual tilted-minimum
acceptable interval. This replaces the source's informal first-right-derivative
threshold proof, without changing its objective/ray assumptions or conclusion.
The finite five-piece inability to continue is kept distinct from infinite
admissible bad runs. The matrix example converges to a matrix with an arbitrary
unexcited entry; it is not an example of a divergent matrix sequence.
