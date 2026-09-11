# Parabolic transport peer review

## Scope of this review

Read independently: `ParabolicTransportAlgebra.lean` and
`ParabolicScalarTransport.lean`, with their imported actual-pair denominator
and secant statements, against Q.13--Q.17 in the original `Q.tex`.
This entry reviews the exact algebra and scalar estimates. The final
uniform compensated transport theorem and assembled band certificate are
not yet included in this review.

No concrete statement or mathematical defect was found in these two
modules.

* `radial_direction_transport` gives an actual vector identity with a
  scalar multiple of the actual displacement. Its determinant hypothesis
  is explicit; the imported `exists_small_denominator_bounds` derives that
  hypothesis uniformly from actual eligible pairs on a compact positive
  band. Neither a horizontal step nor an arbitrary normal slope is divided
  by or required nonzero.
* `quotient_cancellation` is the exact Q.15 identity using an actual active
  old branch. `exponent_increment` is the exact remainder identity for the
  old branch's exponent. They require only the displayed nonzero value
  denominators, which positive-band membership supplies. The latter does
  not assume differentiability of the active-index selection or a Taylor
  remainder estimate.
* `log_remainder_bound` has the exact local condition `abs(r-1) <= 1/2`
  and constant `2`; this condition also entails positivity of `r` for the
  later logarithmic identities.
* `compensation_square_bound` uses the source horizontal estimate
  `h^2 <= d/a` with `a > 0`, a bounded linear coefficient, and the Q.15
  cancellation error. Its `0 <= d <= 1` and nonnegative coefficient bounds
  are explicit. `compensation_log_bound` then cancels the first order term
  with no coordinate or gradient nonvanishing assumption.
* `exp_mul_le_one_add` is an exact convex interpolation bound, valid even
  for negative `C`. `squared_multiplier_bound` explicitly requires the
  positive multiplier and gives the source square multiplier bound for
  `0 <= d <= 1`. The future certificate assembly must establish a
  nonnegative transport budget; that is not a missing premise of either
  scalar theorem, whose displayed conclusions remain correct for all `C`.

The two algebraic modules do not yet assert the existence of uniform
positive-band constants or derive the actual objective-pair certificate.
Those remain separate assembly obligations, so these intermediate claims
must not be reported as the full Module Q convergence theorem.

## Uniform compensated transport review

Subsequently read the compiler-clean `ParabolicQuantitativeAlgebra.lean`
and `ParabolicUniformTransport.lean` against the full Q.17 quantifiers.
No concrete mathematical or statement defect was found.

`exists_uniform_log_transport` fixes `C>0` and `delta>0` from the original
family, compact set, positive level, and line-search constants before
quantifying over all actual eligible pairs. Both endpoints have the
required positive lower value. There is no assumed denominator, scalar
transport estimate, branch adjacency, coordinate nonvanishing, or matrix
convergence. Actual derivatives give active gradients even at differentiable
ties. Q.13 supplies the nonzero determinant; Q.16 supplies the switch error
for arbitrary old and new indices.

The constants bound the cancellation by `B*d`, the multiplier square
error by `S*d`, the exact old exponent remainder by `U*d`, and the branch
switch by `(CE/eta)*d`. Their sum gives exactly the stated logarithmic
constant `2*S+B+U+CE/eta`. The threshold includes both `delta_D` and `1`,
and `1/(4*(S+1))` proves `abs(lambda-1)<=1/2` and hence positivity.

`calibrated_vector_transport` is an exact identity for the actual vector
`theta(x)*(u,2v)`. `exists_uniform_vector_transport` provides its scalar
multiplier and displacement coefficient for each pair, with one uniform
nonnegative budget `L=exp(2*C)-1`. No rank or independent projection
estimate is assumed. These supply the vector hypothesis needed for the
subsequent general rank-one certificate criterion. This review still does
not claim that the final band certificate or run-convergence wrapper has
been checked; those are later assembly modules.

## Final certificate and convergence assembly review

Read `ParabolicCertificate.lean` after its final continuity elaboration repair.
No defect was found in the statements or assembly. The actual field is
`outer (theta*r) (theta*r)`, exactly Q.8. The visibility constant is
`theta_lo^2 * 4*eta^2 > 0`; the secant constant is `theta_hi^2*C`.
The source threshold `d<=1` is supplied by the transport threshold's proved
upper bound. The vector transport theorem discharges the general rank-one
certificate's actual displacement identity and squared-multiplier bound.
The latter theorem supplies the actual projected PSD matrix inequality,
not an assumed recurrence on a sequence.

`exists_bandCertificate` works for every compact set and positive level,
including empty bands. `hasBandCertificates` therefore has exactly the
objective-pair band quantifiers. `parabolic_convergence` derives compactness
of the initial sublevel and the unique minimum at zero from the original
family, then applies Module T to the actual `AdmissibleBFGSRun`. No
initialization restriction, selector smoothness, iterate convergence,
matrix convergence, or previously assumed hierarchy is introduced. The
two continuity lemmas concern the actual vector/matrix field on `F>0`
and make no assertion at the minimizer.
