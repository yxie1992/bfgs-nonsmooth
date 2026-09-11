# Positive affine objective-value scaling

The actual objective is `x ↦ a * F x + b`, with `a > 0` in the run theorem.
The input is an actual `AdmissibleBFGSRun` on F. The output constructs another
actual run, with the same points, accepted lengths, c1 and c2, gradients a·g,
and full inverse-BFGS matrices H/a. Every run field is derived: whole-space
convexity, accepted-point derivatives, initial SPD, nonzero gradients, the
literal full update, Armijo and weak Wolfe. No limit, boundedness or scalar
hierarchy is a premise.

The step identity cancels the opposite gradient/matrix factors. The update
identity combines the existing exact matrix/step scaling and simultaneous
secant-pair scaling identities. These algebraic identities require only a≠0;
positive a is necessary for the convexity, SPD and inequality transfer.
The energy q, predicted decrease d and actual secant curvature all scale by a.
The original coordinates and displacement stay fixed. The actual supporting
intercept and endpoint curvature use the original R definitions and scale by a.

`ObjectiveValueScalingTarget` explicitly quantifies over arbitrary dimension,
actual objective, positive factor, offset and actual input run, and constructs
the output run with all its matrix/gradient/step/curvature equations. It does
not assume existence of an input run for arbitrary F. The reconstructed R
application supplies the separately constructed D run after its invertible
coordinate transformation. This helper does not by itself transfer rejected
deterministic trials; no such conclusion is claimed here.

The complete owner audit has 25 actual declaration reports: 22 theorems and
three definitions, plus one strict exact target check. Both sources compiled
under the pinned toolchain. The initial compiler error was only an omitted
inverse-cancellation rewrite in the energy proof; `build_initial.log` preserves
it, and the entire corrected source and target compiled successfully before
the ordinary axiom audit. The only transitive axioms are the permitted standard
ones. Fresh independent peer evidence is recorded separately.
