# Constructive resolution of R182–187

The user has authorized reconstruction from the report's proof, rather than
identification of a missing earlier program or objective. This supplement
constructs a new explicit four-piece objective from the already verified D
counterexample and checks R's printed optimizer, branch values, supporting
errors and genuine infinite full-BFGS behavior for that objective. It makes no
claim that the new formula was recovered from an earlier source file.

Let c,d be the actual certified D algebraic seed and set

    δ = c − 16d − 1 > 0,
    a = (25/4)/δ > 0,
    T(u,v) = (u,16v/5),
    F_R(z) = a F_D(Tz) + a − 1.

The positive denominator is essential: 16d−c is the third D branch's negative
value at its optimizer, not its supporting error. Scaling by its reciprocal
would reverse convexity. The checked D positivity theorem supplies δ>0.

The objective is the maximum of four actual affine branches. The first three
are the scaled transformed D linear branches plus a−1; the fourth is
(16a/5)v−16a−1. Its unique optimizer is (−1,5), its minimum is −1, and the
first three branch values there are exactly −1,−1,−29/4. Hence their supporting
errors are exactly 0,0,25/4.

The D trajectory is transported by T inverse. Gradients become a T-transpose
g_k and inverse-BFGS matrices become a-inverse T-inverse H_k T-inverse-transpose.
Accepted lengths and Armijo–weak-Wolfe parameters are unchanged. Coordinate
covariance and positive objective-value scaling prove the actual full update,
initial SPD, all accepted derivatives and acceptance inequalities. Thus the
infinite run is inherited as an actual unmodified full-BFGS run, with no assumed
matrix recurrence, eligibility, convergence or positive-curvature hypotheses.

The transformed iterates tend to zero and objective values tend to a−1>−1.
The three supporting-error predictions recur in every cycle, and actual secant
curvature is a times the D curvature, hence tends to zero. The supporting-plane
condition therefore fails on the actual initial sublevel. This reconstructs
both the literal numerical display and its intended failure interpretation.

Status: the owner fresh five-source rebuild,53 ordinary type/axiom reports and
two strict target checks passed at17:58:45UTC on11September2026. Independent
proof review is pending. Existing main sources, the original report and
release18 evidence remain unchanged; this scope has not yet been integrated
into a new central release.

Subsequent independent proof review closed PASS at18:01:37UTC on11September2026.
See INDEPENDENT_PEER_REVIEW.md and peer_validation.log; all five proof-source
hashes stayed unchanged. The preceding pending note records the owner gate
before that independent review, not the current delivery status.
