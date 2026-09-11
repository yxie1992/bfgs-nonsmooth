# Independent positive-objective-scaling review

PASS. Both frozen sources were read completely and freshly compiled into a
separate peer object directory under pinned Lean. All 25 declared definitions
and theorems produced actual type and ordinary transitive-axiom reports with
only `propext`, `Classical.choice` and `Quot.sound`. Two strict comparisons
against an independently restated complete source target passed. Proof/source
hashes remained unchanged; no main files were edited.

For a positive scale a and arbitrary offset b, the actual new objective is
`a*F+b`. The actual new run has gradients `a*g`, inverse metrics `H/a`, and
the same accepted iterates, lengths and both line-search constants. Actual
derivatives are derived by the chain/constant rules. Convexity, initial SPD,
nonzero gradients, strict positive lengths, the unmodified full inverse-BFGS
update, Armijo and weak Wolfe are supplied from the original run. Thus the
existential target's `AdmissibleBFGSRun` witness contains those proved fields;
they are not extra hypotheses or unspecified acceptance data.

The step identity cancels a against its reciprocal. The update identity follows
from actual matrix/gradient scaling and remains an exact algebraic equality.
The algebraic helper permits nonzero negative scales where positivity is not
needed; the actual run theorem requires a>0, as required by objective order and
SPD preservation. The convexity helper correctly allows a=0 separately. The
actual q, predicted decrease d and secant curvature all scale by a. Supporting
errors scale by a because the value offset cancels, for any chosen reference
point; no false assumption that the reference is already an optimizer is needed
for that identity.

The target quantifies over every dimension, finite objective and actual run,
then constructs one complete transformed run before all iteration indices.
There is no matrix/iterate convergence premise, hierarchy premise, modified
algorithm or changed line-search constant. It provides the correct value-scale
component for reconstruction of R's objective and trajectory.

This helper by itself does not claim affine-coordinate covariance, optimizer
identification, deterministic rejected-trial histories, or a new infinite
failure limit; those remain correctly assigned to their separate transfer and
example theorems. In particular, preserving accepted Armijo–weak-Wolfe fields
is not mislabeled as proving every trial of a specific interpreter.

Evidence: `PeerAudit.lean`, `peer_build.log`, `peer_axioms_contracts.log`,
`peer_source_hashes.json`, `peer_declarations.json`, and `peer_validation.log`.
