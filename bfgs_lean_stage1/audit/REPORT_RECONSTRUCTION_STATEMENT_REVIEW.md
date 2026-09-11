# Reconstruction statement and scope review

The nineteenth mathematical gate passed with 5,195 explicit theorems, 7,813
total theorem declarations, 255 exact registered targets and 737 frozen Lean
sources. All 7,704 earlier theorem types and transitive axiom sets agree with
the previous complete audit. All 727 previous library proof sources are
unchanged. The four new targets have independent complete-statement reviews,
fresh ordinary axiom audits, and the integrated 85-declaration scoped audit.

## Positive objective-value transformation

`objectiveValueScaling : ObjectiveValueScalingTarget` transforms an actual
`AdmissibleBFGSRun` for a finite convex objective F into an actual run for
`a*F+b`, for a>0. The points and accepted lengths stay the same; gradients are
multiplied by a and inverse matrices by 1/a. Actual derivatives, initial SPD,
the literal full inverse-BFGS update, Armijo and weak Wolfe are derived. The
target records the corresponding energy, predicted-decrease and curvature
identities. It does not assume that every objective has an infinite run or
that a deterministic rejected-trial history is unchanged. The R construction
supplies its own actual witness from the already verified D run.

## R's new four-piece objective and actual run

The positive denominator is `delta=c-16*d-1`, using the certified algebraic
seed constants. Setting `a=25/(4*delta)` and `T=diag(1,16/5)` gives the literal
objective `a*F_D(Tz)+a-1`. Its four actual affine branches are defined in
`ReconstructedFourPieceObjective.lean`. The unique minimizer is (-1,5), its
value is -1, and the first three branch values are -1,-1,-29/4.

`reconstructedFourPieceFailure` constructs an actual admissible full-BFGS run
by coordinate covariance and positive objective rescaling. Its parameter
range is exactly 0<c1<=1/3 and c1<c2<1. All accepted points are differentiable,
the exact update and both acceptance conditions hold, values strictly decrease,
and the run tends to the nonstationary origin at the suboptimal limiting value
a-1. No matrix convergence or abstract assumed periodic trajectory is a
premise. Identity initialization and full rejected-trial claims are not added
to this R target; the separate D embedding theorems retain those claims.

`reconstructedSupportingPlane` uses the same actual run. Its three phases
have exact supporting errors 0,0,25/4; actual positive secant curvature tends
to zero. The SP contradiction chooses the single positive band eta=a before
the proposed bound C, inside the actual initial sublevel. The fixed nonzero
intercept difference cannot satisfy its proposed square bound as curvature
tends to zero. RS fails by the proved equivalence on that same compact
sublevel. Allowing constants to deteriorate between bands cannot evade this
fixed-band contradiction.

This is an explicit new realization of the printed R data, not identification
of an unprovided earlier objective. The current D objective's different
optimizer (-1,16), supporting errors and lower bound at (-1,5) remain proved.

## New E facts and execution evidence

The inverse secant identity concerns the actual full inverse-BFGS formula in
arbitrary dimension. Its only curvature hypothesis is nonzero dot(y,s). The
Hessian identity additionally uses actual SPD input and positive curvature to
derive invertibility of the same update. The positive-tolerance theorems use
actual objective convergence, not a convergence premise: the planar statement
retains its exact initial-value basin F(x0)<1/100; the infinite-spike statement
retains its unit-normal hypothesis and arbitrary finite dimension.

The thresholds 10^(-45) and 10^(-28) are universal eventual conclusions. They
provide no computed stopping index, iteration complexity, finite precision
run or historical trial count. The unavailable oscillatory auxiliary is
explicitly replaced by G's defined accumulating-kink example, with its exact
incoming-pair and obstruction conclusions. It is not a bad BFGS trajectory.

All nineteen newly authored category jobs ran successfully: 107 independently
frozen literal type contracts across 93 distinct actual theorem names, with
ordinary transitive axiom reports. The runtime invokes the pinned compiler;
Python does not supply mathematical proof. Actual command, environment, exit,
time, source, output and check records are bound by hashes. The independent
package review covers source roles and deliberate evidence corruptions.

## Corrected edition and original record

The user's instruction to generate missing inputs from the AI-generated
report authorizes these new constructions and jobs. It does not establish
whether any historical job ran. The corrected edition consists of the
unchanged master report together with mandatory `CORRECTED_REPORT.md`.
The nine inherited mathematical corrections remain explicit; source spans,
old proof exports and all 22 original research artifacts are preserved.

The three corrected completion components are retained mathematics, new
execution evidence and source reconciliation. They are distinct from the
legacy `entire_report_verified` flag, whose original-snapshot meaning remains
false. Explicit conjectures, objective-specific criterion hypotheses and
expressly unclaimed blanket convergence or robustness assertions remain
classified accordingly. No unavailable source input is still needed for the
explicitly reconstructed edition.

See `REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md` for the final independent
release review and `report_reconstruction_documentation_validation.log` for
the actual closing gate. Proof evidence is in `reconstruction_reviews/`, the
integrated scoped audit and the complete central transcript; source/evidence
reviews are in `reconstruction_scope/` and `reconstruction_delivery_evidence/`.
