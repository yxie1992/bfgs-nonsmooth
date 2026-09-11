# Module T core theorem: independent statement and proof review

Reviewed read-only by the `armijo_budget` agent against the complete source
`BFGS_MASTER_REPORT_LaTeX/report/chapters/T.tex`. This is an internal agent
review, not external mathematical peer review or a substitute for compiler and
transitive-axiom audit logs.

## Primary theorem and quantifiers

The primary compact-sublevel convergence theorem is represented faithfully.
`EligiblePair` includes actual derivatives at both endpoints, positive predicted
decrease, both objective-drop bounds, and the weak-Wolfe curvature lower bound.
It does not assume arbitrary eligible pairs can be chained by BFGS.

`HasBandCertificates` quantifies over each positive eta with a nonempty whole
positive band. Each band's field and constants may depend on eta and the fixed
line-search parameters. The certificate imposes PSD only at differentiable band
points and visibility for their actual derivative vectors. Secant and transport
bounds quantify over all eligible pairs in that band with d <= delta. There is
no omitted second-endpoint band membership or small-step qualifier.

The field is a function with real matrix entries. Its values are finite, but no
uniform bound, continuity, measurability, differentiability, positive definiteness,
fixed rank, or nonzero rank is assumed. Defining it on the whole ambient space is
only a total-function representation of a field used at differentiable band
points; arbitrary unused values can be assigned outside that domain.

## Actual matrix discharge

`accepted_pair_eligible` derives all eligibility conditions from the existing
objective-level accepted run. Initial-only SPD, q > 0, positive curvature,
Hessian update and annihilation are proved in Module M and reused.

The projector is the actual matrix I - ss^T/(s^T s). Accepted displacement is
proved nonzero. Both left and right invariance of the annihilated PSD matrix are
proved algebraically; testing the projected Loewner inequality against that
matrix produces the required trace inequality. PSD-product trace nonnegativity
is proved through an actual Gram factorization. No unproved scalar recurrence,
projected-trace identity, or hierarchy is supplied as a target premise.

`certificate_trace_step` therefore derives T.6 for the actual energy
tr(H_k^{-1} W(x_k)). Visibility, secant control, and the nonnegative transport
factor are used in the correct directions. Arbitrary real secant constant C is
handled in the scalar contradiction by enlarging it to max(C,0), without adding
a sign assumption to the objective certificate.

## Limit and compactness discharge

The finite objective limit is derived from Armijo monotonicity and an attained
minimum lower bound. Compactness supplies a gradient bound. Armijo supplies
summability and hence eventual d <= delta. A hypothetical positive limiting gap
selects one fixed nonempty positive band and one fixed certificate before the
tail argument. No uniformity in eta is introduced.

The compact-sublevel export derives containment from its initial-value condition
and Armijo. It proves objective convergence, distance to the actual full argmin,
and convergence of the whole iterate sequence under uniqueness. No iterate,
step-length, displacement, or BFGS-matrix convergence/boundedness is assumed.

## Disclosed proof-route difference

The source contradicts qualitative reciprocal-mean divergence using a constant
additive trace correction and an O(N) bound. The present implementation enlarges
the constant correction to O(k), invokes the verified summable-drift scalar
residual theorem, and contradicts superquadratic reciprocal-sum growth. This is
a valid alternative under exactly the same derived summability hypotheses; no
extra condition is imposed and the primary theorem's conclusion is unchanged.

## Findings and scope

No concrete mathematical or quantifier defect was found in the primary theorem
files reviewed. The source's subsequent local/shell refinements, scalar field
transport sufficient condition, bounded-potential rescaling, RS embedding/strict
inclusion, and affine covariance are separate obligations. This review of the
primary theorem does not certify those additional source claims.
