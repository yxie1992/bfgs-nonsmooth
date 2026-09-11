# Seventeenth milestone: literal semialgebraic paths and composition

This review covers 33 new Lean modules in seven independently reviewed scopes,
152 scoped declaration reports (including definitions, structures and fields),
and 16 exact targets. Their owner and independent peer compiler, actual-type,
transitive-axiom and strict-contract gates passed before delivery. The central
build result is recorded separately in STATUS.json and
report_semialgebraic_path_check.log; this review does not itself certify that
the central gate has finished. Original research sources remain unchanged.

## Literal path graphs

Semialgebraicity means that the actual restricted graph is described by a
finite Boolean formula of real polynomial sign conditions. The map-graph
composition theorem constructs the shared intermediate witness and applies
the already verified finite-coordinate projection theorem. It does not assume
projection closure. Polynomial maps, coordinatewise graphs, restriction,
affine reparameterization, reversal, concatenation and scalar graph arithmetic
are proved for these actual graph sets.

The enriched path record retains an actual curve, continuity on [0,1], the
specified endpoints, containment, and smoothness away from a finite set of
interior parameters, and adds semialgebraicity of that very curve's restricted
graph. Graph certificates are attached to the explicit constant, reversed,
mapped, concatenated, graph-section and band-section analytic witnesses. The
concatenation graph theorem is separate from the endpoint-matching condition
needed for continuity. No opaque existential choice is assumed to preserve a
formula it was never required to satisfy.

The general finite-cover theorem constructs finitely many semialgebraic pieces
with these actual witness paths from semialgebraicity alone, in arbitrary
finite dimension. Actual zero factors, specialized root signatures and
boundary signs give whole ordered graph/gap cells. Dimension induction and
proved coordinate reindexing supply the cover. No arbitrary subset is assumed
connected; Boolean formulas select whole cells. Empty sets, empty coordinates,
zero polynomials, degree drops and unbounded bands are included. There is no
root-chart, projection, finite-cover, compactness or nonemptiness premise in
the final theorem.

## Regularity derived from actual graphs

The scalar function theorem derives a finite semialgebraic cover on which the
actual function is smooth. For an actual singleton vertical fiber, its value
must be a root of a nonzero defining polynomial factor: otherwise local sign
constancy would produce additional fiber points. The proof constructs the
actual root representation instead of assuming one. Actual root-signature
strata and ordered-root charts then give the finite function-piece cover.

In one variable, finite polynomial-root boundaries yield actual ambient
neighborhoods outside a finite exceptional set. Consequently the actual scalar
function is smooth there. This remains valid for a restricted domain: its
semialgebraicity is derived from the actual graph, and the possible domain
boundary points belong to the finite exceptional set. Arbitrary behavior of an
extension outside the domain is not assumed smooth.

The interval wrapper preserves continuity on the entire closed interval and
gives smoothness at interior points outside a finite set. It does not claim
derivatives at endpoints, bounded endpoint derivatives, or smoothness across
the exceptional parameters. This is the piecewise C1 meaning used in the
source's argument. Coordinatewise graph projection and the finite union of
coordinate exception sets prove the vector-curve version, including dimension
zero.

For a finite convex semialgebraic objective and an actual continuous
semialgebraic path, the graph of the actual composition F∘p is constructed by
projection with the same intermediate point. Convexity gives continuity of F;
path continuity gives continuity of the composition on [0,1]. The scalar
regularity theorem supplies its finite smoothness exceptions. Differentiability
of p or F∘p is not a premise of this target. The opposite coordinate conventions
for curve and scalar graphs are explicitly reindexed in the proof.

## Actual path components

The source-facing path record requires only an actual curve, continuity,
endpoints, containment and semialgebraicity of its restricted graph. Smoothness
is absent from its definition. The regularity theorem upgrades the same curve
to an enriched path, preserving all those fields. The reverse implication
forgets smoothness. Thus equality of the two relations and their actual
component operators is proved, including for ambient sets not assumed
semialgebraic.

An affine prefix of each actual path remains semialgebraic and piecewise
smooth. The zero-length prefix is handled separately; the positive-length
case proves every required nonzero denominator. Prefixes keep the entire path
inside its source component, giving internal connectivity of the actual class.
Each class is a union of whole finite-cover pieces that meet it. This proves
finiteness of the class family and semialgebraicity of each class. Outside-set
classes are empty and are not assumed nonempty.

Applied to the actual affine-critical set, these results give finitely many
actual continuous-semialgebraic path components, each semialgebraic and
internally connected by such paths. Objective constancy uses the independently
proved finite critical-value image and continuity. The earlier finite-value
proof used the lifted critical graph's smooth cover; it does not depend on this
new component argument. No circular appeal to the new conclusion occurs.

Ordinary topological components and unrestricted piecewise-smooth path classes
remain separately defined. The former's finiteness, semialgebraicity and
constancy were proved in milestone 16. The additional critical smooth-path
target explicitly proves the corresponding class constancy and constancy
along every actual smooth critical path. It derives zero value derivative at
every interior parameter from local constancy, even at an exceptional
parameter of the point curve. No equality with an unrelated component
operator is silently asserted.

## Source coverage and remaining evidence

These proofs close the literal geometric ingredients in A69–75: actual
semialgebraic witness paths, finitely many actual semialgebraically
path-connected components, and continuous piecewise C1 objective composition.
The already verified supporting-vector chain rule gives the displayed
derivative identity whenever both derivatives exist. Its affine combination
equal to zero gives the source's zero derivative. The corresponding C proof
ingredient and I synthesis are covered. The original low gap and BFGS basin
conclusions retain their previously reviewed hypotheses and quantifier order.

A later literal-source pass identified two additional M exports: the exact
eigenbasis Gram-sum equality at M94–99 and the sharp degree-n−1 potential
bound at M151. The principal matrix/growth theorems already have valid proofs
using sufficient inequalities. These displayed intermediate assertions remain
in a separate active proof scope; this tranche does not count them as proved.

R182–187 attributes numbers to an older four-piece objective whose definition
has not been recovered. The actual current D objective has a separately
verified optimizer and supporting-plane correction; it does not verify the
unidentified objective's asserted (-1,5), -29/4 and 25/4 values. This remains a
mathematical source-attribution obligation. E's original 19-job outputs,
counts, timings, environment and archive identities also remain unverified
without their referenced inputs. Current universal Lean proofs do not certify
those past executions. These exceptions must remain visible in the report
register; entire_report_verified cannot become true merely because the current
registered targets pass.

No new assertion is made for the source's explicit conjectures, general
rotating-normal convergence, floating-point or positive-measure robustness,
all-ray line-search existence, or blanket nonsmooth BFGS convergence. Earlier
mathematical corrections remain documented rather than changing the originals.

## Reproduction and review

The delivered aggregate manifest records every source, reviewed original hash,
import normalization, declaration name, exact target and peer artifact. Adopted
proof bodies equal the reviewed originals after import normalization. The
generic scoped gate rebuilds delivered modules, prints actual types and
transitive axioms, and checks exact target assignments. A delivered-only
correspondence gate reconstructs the original reviewed hashes and checks the
peer evidence without reading excluded scratch files.

The central check separately audits all compiled theorem declarations,
including generated auxiliaries, and the entire registered target set. Only
propext, Classical.choice and Quot.sound are allowed. No placeholder, custom
mathematical axiom, unsafe computation or unchecked external mathematical
calculation is accepted. Scoped counts are not substituted for the central
compiler inventory.
