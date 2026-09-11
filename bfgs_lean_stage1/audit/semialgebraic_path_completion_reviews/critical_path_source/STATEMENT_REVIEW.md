# Actual smooth critical-path values

The source supplement makes the remaining literal C path-component value
assertion explicit. Its final contract assumes only finite convexity on the
whole finite-dimensional space and genuine objective semialgebraicity. The
actual critical set has finitely many actual smooth path classes; each is
semialgebraic and internally connected by the specified smooth paths, with
constant actual objective value.

The proof uses the already derived actual finite critical-value image and
continuity on each preconnected class. For every actual critical-set smooth
path, its reparameterized prefix reaches every point of the closed unit
interval inside the same actual class. The objective is therefore constant
along the entire path. Local equality on a genuine neighborhood gives actual
HasDerivAt zero at every interior parameter, including the finite exceptional
parameters where the point path need not be differentiable.

No differentiability assumption on the composition, subgradient selection or
finite-value hypothesis is introduced. The stronger derivative statement is a
consequence of the completed value theorem, not a circular replacement for its
proof. This scope does not certify semialgebraic graphs for arbitrary smooth
paths. General semialgebraic-path construction and scalar semialgebraic
piecewise regularity remain separately reviewed scopes.

Both source files compiled, all five actual declaration types and standard
transitive axioms were checked, and the exact complete target passed. The
independent peer freshly rebuilt both sources, checked the full target and
separately restated the every-interior-parameter derivative claim. All frozen
hashes match. No original research source was modified.
