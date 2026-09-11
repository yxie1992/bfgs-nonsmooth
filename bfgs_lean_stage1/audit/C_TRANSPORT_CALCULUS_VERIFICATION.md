# C determinant and one-sided transport calculus

`PlanarDerivativeDeterminant` (10 theorems) and `PlanarScalarTransport`
(6 theorems) are integrated after release `01c1511`. Pinned main-library build,
all explicit declaration/type and transitive-axiom checks, and both source-hash
checks passed. Only `propext`, `Classical.choice` and `Quot.sound` occur.
Evidence: `c_transport_calculus_build.log`,
`C_TransportCalculusAxiomChecks.lean`, `c_transport_calculus_axioms.log`,
`c_transport_calculus_declarations.json`, and
`c_transport_calculus_validation.log` in `audit/`.

The actual derivative matrix preserves the level tangent by the previously
checked field theorem. Its determinant is factored in the actual unit basis;
the sign agrees with the previously documented correction
`det(rotated normal, normal) = -1`. Its coefficients have explicit bounds from
the finite-Pi operator norm. Consequently the actual determinant derivative
is bounded by `6 * ‖DW‖ * ‖s‖₂ * |g⋅s| / ‖g‖₂`. Visibility and the Euclidean
field bound give the positive gradient-norm lower bound. Actual determinant
transversality cancels the step length to obtain the corresponding logarithmic
derivative estimate. Neither an assumed triangular derivative matrix nor an
assumed Euclidean interpretation of the Pi operator norm is used.

The scalar transport proof implements C.14's comparison by right derivatives,
without an assumption about a finite switching partition. For a convex scalar
restriction with actual initial derivative `-d`, every later right derivative
is at least `-d`. If `|h'_+| ≤ C*|φ'_+|`, then
`|h'_+| ≤ C*(φ'_+ + 2*d)`. The one-sided derivative comparison theorem applied
to `C*(φ(t)-φ(0)+2*d*t)` gives the endpoint bound `2*C*d` whenever
`φ(1) ≤ φ(0)`. This is a proof-route change; it does not strengthen source
hypotheses or assume an almost-everywhere fundamental theorem.

For `h = log D`, nonvanishing throughout the whole segment proves the positive
endpoint ratio by the intermediate value theorem. The actual determinant
ratio then gives the literal transport decomposition by the checked planar
basis identity. Real logarithm and actual nonzero right derivatives are used;
the sign of the determinant need not be supplied separately.

The scalar lemmas are reusable conditional calculus results. To obtain the
full source endpoint theorem, the actual field's right derivative and its
uniform local determinant bound must still be assembled for every point of
each segment, including corner neighborhoods where the field equals a
level-velocity function. The final secant correction and C principal
conclusion remain separate open obligations. These results do not yet claim
the full Module C theorem or the stronger uniform eligible-pair statement.
No research source or eighth-release global evidence was changed.
