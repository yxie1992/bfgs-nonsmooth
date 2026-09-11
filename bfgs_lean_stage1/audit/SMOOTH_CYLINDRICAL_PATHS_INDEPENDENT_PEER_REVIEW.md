# Independent review: actual smooth paths and lifted graph

Reviewed all five frozen modules in full, including the actual path structure,
all four target propositions and both existing objective-path definitions. A
fresh independent PeerAudit.lean printed all45 actual declaration types and
transitive axioms, checked seven strict source/wrapper equalities, and compiled
an independently written restatement of the lifted-graph implication. All five
source hashes match declarations.json. The actual output and validation are in
peer_axioms_contracts.log and peer_validation.log. No defects were found.

The path data contains a real curve, endpoint identities, continuity and actual
containment on the closed unit interval, and a finite exception set. The reversal
and concatenation proofs transform those sets correctly. The join parameter is
explicitly exceptional, so no endpoint smoothness is assumed. The two affine
parameter maps send each open half to the original open unit interval; eventual
equalities justify actual smoothness away from the finite transformed sets.

Mapping uses smoothness within the actual source set. At an interior time the
closed parameter interval is a neighborhood, which turns the within-composition
conclusion into the required actual smoothness. The graph theorem constructs the
actual graph map. Open and one-sided bands use an actual smooth section and two
vertical linear segments in the actual convex fiber. No compactness, uniform
width or endpoint differentiability hypothesis is omitted. Empty base sets are
permitted; ordinary path connectedness is used only when nonemptiness is supplied,
and ordinary preconnectedness handles the empty case explicitly.

The lifted objective graph proof takes the actual coordinate projection of the
curve. Both derivatives come from the lifted curve. In particular, the actual
objective composition agrees with the none coordinate throughout the closed
unit interval, and hence in a neighborhood of each interior time. There is no
substitution of a different function for F and no assumed derivative of F. The
critical-graph specialization invokes the actual signed-support path constancy
proof for a finite convex objective.

Scope remains conditional: these proofs construct paths from supplied smooth
base paths/boundaries and supplied graph paths. They do not establish the general
finite semialgebraic cover. The curve predicate does not assert a semialgebraic
graph. That distinction is explicit in the owner review and must remain explicit
in the final source reconciliation; ordinary piecewise smooth paths in the actual
lifted critical graph suffice for the final critical-value consequence.
