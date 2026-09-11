# C actual full-BFGS logarithmic transport

The four new main modules `PlanarFieldStructure` (3 theorems),
`PlanarCornerTransport` (6), `PlanarEndpointTransport` (1), and
`PlanarRunTransport` (4) passed the pinned main build, every explicit
declaration/type and transitive-axiom check, and four matching source hashes.
Only the standard `propext`, `Classical.choice` and `Quot.sound` occur.
Import `BfgsVerification.PlanarRunTransport` for the full tranche. Evidence is
`c_actual_transport_build.log`, `C_ActualTransportAxiomChecks.lean`,
`c_actual_transport_axioms.log`, `c_actual_transport_declarations.json`, and
`c_actual_transport_validation.log` in `audit/`.

The same actual cutoff and corner-velocity family now simultaneously supplies
the visible locally Lipschitz comparison field, its smooth/corner structural
formula on an open neighborhood of the entire compact level, and common
support pairing on that level. The proof does not combine separately chosen
existential fields. Compactness and actual C1 velocity regularity provide one
Euclidean bound for all velocity derivatives, including an empty corner family.

At a smooth point, the checked actual field derivative preserves the tangent
line. Its determinant quotient is bounded using the actual derivative norm,
transversality, and the lower gradient norm derived from positive visibility.
At a corner point, the local identity `W=v(F)` gives an actual right derivative
through the actual convex scalar right derivative. Its quotient bound uses
the velocity derivative and transversality. The gradient-norm premise is
explicitly conditional on objective differentiability; no total default
gradient is treated as a nonzero gradient at a nonsmooth point.

`structured_field_segment_transport` derives the actual determinant right
derivative estimate at every point of the segment, using whichever structural
case holds there. The previously checked one-sided scalar comparison gives
the logarithmic endpoint estimate and positive exact transport coefficients.
No finite switching partition, assumed derivative budget, unchecked integral,
or bound on normal curvature is used in this assembly.

`eventually_structured_field_transport` then derives the uniform compact
field/velocity/derivative bounds, transversality, and eventual containment of
every accepted segment. Actual accepted gradients, actual steps, descent and
predicted decreases are substituted. The final source wrapper
`exists_log_transported_planar_field_of_no_affineCritical_cluster` derives the
finite value limit, positive limiting gap and vanishing steps from compactness,
an actual minimizer, the relevant strict contours, regular switching at the
cluster set, and the contradiction hypothesis that it contains no
affine-critical point. Its conclusion retains an open neighborhood with
uniform positive visibility against every actual support. Thus the target
does not permit a vacuous zero comparison field.

This verifies the actual-trajectory form of C's logarithmic transport lemma
and its source-derived field, with one constant and one tail index before all
later steps. The full crossing secant correction and resulting principal
affine-critical-cluster contradiction remain open. The stronger uniform
formulation over every sufficiently close eligible pair in a buffered
neighborhood is also separately tracked. No source conclusion is silently
identified with a weaker trajectory statement, and no source file or previous
release manifest was changed.
