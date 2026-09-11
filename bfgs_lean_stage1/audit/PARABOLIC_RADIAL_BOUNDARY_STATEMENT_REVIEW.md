# Literal parabolic radial-secant boundary

Source: R.tex, explicit parabolic ridge example. Original source unchanged.
ParabolicRadialBoundary.lean contains 23 theorems and seven definitions.
Its actual objective is proved equal to max(u^2+v,2*u^2-v), and its convexity,
nonnegativity, unique zero minimizer, compact sublevels and actual branch
Frechet gradients are established from the existing parabolic family.

At each nonzero ridge base (u,u^2/2), the literal old/new points are
(u,u^2/2-epsilon) and (u,u^2/2+epsilon/2). For epsilon>0 their objective values
are 3*u^2/2+epsilon and 3*u^2/2+epsilon/2. Both actual gradients are proved.
The actual secant curvature is 3*epsilon, while the radial numerator is
-u^2+epsilon. Consequently the exact ratio is
(u^2-epsilon)^2/(3*epsilon), tending to +infinity as epsilon decreases to zero.
The actual ridge gradient jump and its radial pairing -u^2 are also exported.

`unbounded_radial_pairs` quantifies a positive objective band eta=u^2 BEFORE
the arbitrary proposed constant C. Both points lie in the requested arbitrary
neighborhood of zero; both actual derivatives, objective ordering, positive
secant curvature and strict violation of the proposed bound are proved.
Thus `not_radial_secant_on_neighborhood` negates the exact RS predicate on
every such neighborhood, and `not_radial_secant_on_sublevel` covers every
positive sublevel. This is not merely an unbounded ratio whose positive band
shrinks with C.

`converges_without_radial_secant` pairs that negative RS statement with the
already verified Module Q theorem for every actual admissible full-BFGS run
on this literal family. Failure of RS is not stated as a convergence failure.
No accepted-pair eligibility is needed for RS, which concerns all ordered
actual differentiable secant pairs. No convergence is assumed.
