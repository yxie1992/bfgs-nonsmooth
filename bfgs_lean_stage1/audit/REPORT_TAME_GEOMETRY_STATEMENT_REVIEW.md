# Sixteenth milestone: actual tame geometry and literal D closure

The scope comprises sixty new delivered Lean modules, 301 explicit declaration
reports including definitions/structures, and twenty-eight exact target
contracts. Every scope passed actual compilation, actual type inspection,
standard transitive-axiom checks, source-hash validation and independent
mathematical review before central registration. The frozen central gate covers
693 Lean files and 233 exact targets. Its completion is recorded separately in
STATUS.json and report_tame_geometry_check.log; this document alone is not an
audit result. The original research sources remain unchanged.

## Actual finite-dimensional geometry

The root analysis concerns actual specialized polynomials and their actual
roots and multiplicities. Degree bounds, iterated Rolle, arbitrarily small root
clusters and total-multiplicity upper bounds are proved. Finite conservation and
ordered matching use both the actual distinct real-root count and total real
multiplicity. Keeping only the distinct count would be insufficient: roots can
disappear at one cluster and split at another. No occupancy or root continuity
premise is substituted for this argument.

On the actual degree/distinct-count/total-multiplicity signature strata, ordered
roots are continuous and their actual multiplicities locally constant. The
multiplicity derivative supplies a nonzero derivative chart and a local smooth
ambient extension, yielding the stated smoothness on the stratum. Exact root
count and ordered-root graph definability come from the previously proved
polynomial elimination machinery. These are actual semialgebraic sets with
finite Boolean polynomial formulas, not abstract closure predicates.

Actual paths are continuous on [0,1], connect the specified endpoints, stay in
the specified set and are smooth away from a finite set of interior parameters.
Explicit reversal, concatenation, graph lifting and graph/band/cylinder paths
are proved. The same ordered-root graphs and intervening gaps are semialgebraic,
pairwise disjoint, cover the cylinder and have these paths. Finite simultaneous
boundary-sign strata keep all input polynomial signs fixed at all ordered roots.

The dimension induction constructs a finite cover for every genuine
semialgebraic set in arbitrary finite coordinate dimension. It splits actual
zero factors and root signatures, refines all boundary signs, applies the lower
dimensional theorem to the actual parameter sets and uses the actual ordered
cells. Nonzero factor signs on gaps are constant by the intermediate value
theorem. Boolean formulas select whole cells; no subset is assumed to inherit
connectivity. Empty families, identically zero factors, constant products,
empty strata, degree drops and dimension zero are included. The final theorem
has no projection, root, chart, decomposition or finite-cover hypothesis.

Actual piecewise-smooth path classes are defined by existence of the specified
paths. A prefix-path construction keeps their witnesses inside their own
classes. The proved cover gives finitely many actual classes, each
semialgebraic and internally piecewise-smooth connected. This does not identify
those classes with ordinary connected components without proof. Independently,
the finite preconnected cover proves that each ordinary connected component is
a union of whole cover pieces; this proves both finiteness and semialgebraicity
of the ordinary component family.

## Actual affine-critical values and the original low gap

The objective graph is the graph of the actual finite convex objective. Actual
supporting vectors and bounded signed affine combinations define the actual
affine-critical set and its lift to that graph. Their definability was proved
in milestone15 and is used here without an elimination hypothesis.

Apply the constructed smooth cover to the actual lifted critical graph. Its
paths simultaneously give a piecewise-smooth point curve and a piecewise-smooth
objective-value curve. The already checked two-sided supporting inequality
identifies the value derivative with the scalar product against every actual
subgradient. An affine combination equal to zero forces that derivative to
vanish, so the value is constant on each graph-cover piece. Their finite union
proves finiteness of the actual critical-value image.

Continuity of the finite convex objective makes it constant on each actual
ordinary connected component once that image is finite. For any attained
minimum, the finite image gives a positive gap below the next possible larger
critical value. The resulting statement is exactly the original strict low
threshold implying membership of zero in the actual subdifferential. Attainment
is needed only for this gap; no rank, genericity, subgradient-selection,
finite-value or path hypothesis remains in the general geometry target.

## Actual planar consequences

The compact structural-sublevel theorem retains the source compactness,
strict-positive-contour and local smooth-or-two-branch regularity hypotheses.
One positive basin threshold is chosen before every actual admissible full-BFGS
run. A half-gap margin handles the closed starting-value cutoff. Value
convergence and both actual solution-distance limits hold without uniqueness;
uniqueness is required only for the whole-iterate limit. The local-neighborhood
version explicitly assumes uniqueness and obtains an objective-only basin.
Neither theorem adds optimal multipliers, affine correctness, iterate or matrix
convergence, a condition-number bound or a scalar energy hierarchy. Actual
finite values and affine correctness are derived from semialgebraicity.

The literal C assertion about finitely many actual piecewise-smooth path
components is supplied by the separate general component wrapper. Constancy
on those components also follows from the already proved finite value image
and continuity along every such path. The original C2-to-C1 constant-rank
regularity qualification from milestone14 remains in force.

## Literal D consequences

Both non-strict tests are defined as the actual objective/gradient inequalities
inside the original unit-first bracket-and-midpoint/doubling interpreter.
Every accepted length and complete trial history agrees with the actual strict
interpreter at every index of the seed, coercive and embedded runs, for all
original allowed line-search constants and copy indices. Successful five-fuel
outputs prove finite search completion; exhaustion is never acceptance.

Rejected trials require strict violation of non-strict Armijo. The proof uses
the previously proved rejection at half the positive Armijo coefficient and
the actual negative directional product. The half coefficient is a proof
device; the executed tests still use the source coefficient. Actual objective
and derivative transfer obligations are discharged for all three source runs.

The source polynomial equations are equivalent, in both directions throughout
the whole original closed box, to the prescribed quarter and sixteenth lengths.
Box-wide denominator positivity is proved. The actual three-gradient convex
hull excludes zero because it lies in the actual subdifferential at the proved
nonstationary limit. The literal positive affine weights 8/17,8/17,1/17 sum to
one and give the stated identically constant branch combination. No approximate
number or supplied oracle replaces these actual definitions.

The exhaustive D source map now covers all 453 lines in 57 groups with 42
corresponding proof files. The five nearest-rounding corrections from
milestone15 remain documented; the original source is unchanged.

## Remaining literal and historical distinctions

The actual A low-gap proposition, actual finite values, ordinary components,
I's corresponding synthesis assertion and C's tame basins are proved in this
scope. A's proof paragraph additionally says the witnessing paths themselves
are semialgebraic and invokes piecewise-C1 regularity of their compositions.
The present finite-cover theorem certifies smooth paths inside semialgebraic
pieces; it does not separately certify those path graphs. That literal
ingredient is under active verification in a separate scope. It is not silently
marked proved, and no dependent final conclusion is weakened.

Historical E execution jobs, counts, timings, environment/archive identities
and R's old four-piece numerical attribution are not certified by these
mathematical proofs. The referenced original inputs are absent. The current
actual-objective corrections, universal theorems and reproducible Lean builds
are distinguished from those historical records. Explicit research conjectures
and blanket convergence claims remain unasserted.

## Evidence

The seven delivered scope manifests are tame_geometry_declarations.json,
d_literal_closure_declarations.json, boundary_sign_declarations.json,
smooth_path_components_declarations.json, general_smooth_cover_declarations.json,
semialgebraic_smooth_components_declarations.json and
critical_geometry_declarations.json. Their actual build/type/axiom/contract
logs and independent reviews are in audit/. The two component validators
reconstruct the reviewed original hashes from delivered text and recorded
import substitutions; no scratch directory is required for their reproduction.

All adopted proof bodies equal their independently reviewed originals after
import normalization. The exact target declarations are registered in
report_tame_geometry_targets.json; the central frozen hashes are in
report_tame_geometry_source_hashes.json. Only propext, Classical.choice and
Quot.sound are permitted. No placeholder, custom mathematical axiom, unsafe
computation or external unchecked mathematical result is accepted.
