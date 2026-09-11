# Entire-report Lean verification plan

Current status: the [corrected report](CORRECTED_REPORT.md) is verified.
The original historical record remains unverified. The initial plan and
milestones 1–18 below are historical snapshots: their pending-work statements
are superseded by the final nineteenth milestone, which records completed scope.

Active scope: every retained mathematical assertion in the canonical
`BFGS_MASTER_REPORT_LaTeX/report/master.tex` and its included chapters. The source
record is preserved. This plan continues the completed Module M milestone at
commit `6c29cff`; it does not label the rest of the report verified.

## Completion standard

Each theorem, lemma, proposition, corollary, mathematical example, and substantive
unnumbered deduction needs a source-to-Lean statement review and an exported
kernel-checked proof. Definitions must model the actual objectives, derivatives,
accepted steps, full BFGS matrices, determinants, and deterministic oracle
choices. General sequence lemmas and conditional criteria are useful dependencies,
not substitutes for their objective-level applications. No assumed matrix or
iterate convergence, modified update, or extra regularity is allowed.

Explicit conjectures and questions are recorded as such, not counted as proved
assertions. Historical numerical/reproducibility claims are recorded as evidence;
the finite exact claims on which the mathematical conclusions depend must also
be proved in Lean. Floating-point runs cannot verify continuum or infinite-run
claims. Any false or incomplete source assertion receives a documented correction,
a counterexample where possible, and a distinct status; it is never silently
weakened. Original sources remain unchanged.

`audit/REPORT_STATUS.json` is the report-level register, separate from the existing
Module M declaration audit in `audit/STATUS.json`. Its source spans cover every
chapter line, including prose outside named theorem environments. Initial spans
are coverage units, not a claim that their contents have already been reviewed.
As each module is read, its detailed inventory identifies every retained claim,
its exact quantifiers, proof dependencies, and corresponding Lean exports.

## Dependency-ordered milestones

| Milestone | Scope and required conclusions | Dependencies / status |
|---|---|---|
| M | Actual principal-minor hierarchy; normalized scalar hierarchy; reciprocal means, finite horizon and superquadratic growth; actual objective run; localization, energy, exact and residual frames | Complete, compiled and audited at `6c29cff` |
| Shared compact analysis | Attained minimum from compact sublevel; monotone value limit; distance to solution set from optimal values without uniqueness; zero-gradient termination | M; in progress |
| T | Projected PSD transport and eligibility from actual accepted pairs; positive-band/small-pair certificate convergence; solution-set distance and unique-minimizer upgrade; local and shell variants; rank-one, rescaling, radial and affine specializations | M + compact analysis; in progress |
| H core | Degree-one Euler/support identities; global gradient bound without bounded iterates; energy/potential; value dichotomy zero or minus infinity | M; in progress independently of compact geometry |
| G scalar | Arbitrary positive scalar metrics with Armijo–weak-Wolfe converge; actual dimension-one BFGS specialization | M + scalar convex analysis; in progress |
| R | Radial secant bound iff inward Taylor remainder, including derivative-free and optimum formulations; finite polyhedral partitions; gauges, penalties and examples; stated boundaries | T + convex directional calculus |
| F | Centered smooth-plus-sublinear and transformed-gauge classes; explicit max-affine basin; affine lifting; little-o rates; exact limits of matrix and line-search claims | M + R + compact analysis |
| Q | Arbitrary finite parabolic max branches, visibility and projected transport including zero slopes/flat contours; explicit strict separation from radial smoothness | T + max-branch calculus |
| G remaining | Exact certificate normalization, ellipsoid/range/pointwise feasibility, incoming-jump obstruction, scalar characterization and nonnecessity examples, finite-sample feasibility distinction | T + Q + scalar result |
| A | Equal-rate affine criticality, rank-loss example, barycentric stability; finite semialgebraic critical values | Finite linear algebra + semialgebraic/path decomposition infrastructure |
| C | Planar forced affine-critical cluster theorem, local consequences, joining/transversality/transport/endpoint bounds, examples and scope boundaries | M frames + A + finite max-branch geometry |
| U | Single exceptional hyperplane and parallel interfaces in arbitrary dimension; cutoff frames, tangential and residual estimates; nonsplitting/oracle/infinite-spike examples | M residual frames + max-branch calculus |
| H remaining | Recurrent-gradient affine-hull obstruction; effective dimension at most two iterate convergence; endpoint/unbounded cases and flat fibers | H core + affine/subspace geometry |
| D | Exact algebraic root and full matrix cycle; every accepted/rejected deterministic line-search decision; scalar interpolation and coercive globally C^{2,1} max-branch embedding; all stated constants and starts | M algebra + exact ordered-field/interval proofs + interpolation |
| L | Positive-lower-curvature persistence; true stable-manifold existence for the actual return map; all oracle decisions; C^{1,1} embedding and its failure to be C²; countably affine variant | D + differentiable dynamics/stable manifold + interpolation |
| I/E closure | Verify each synthesis implication and supersession against the proved statements; classify conjectures; reproduce evidence; replace every proof-bearing numerical shortcut by a Lean proof; final all-source coverage review | All preceding milestones |

Work is parallelized only across independent files. Common interfaces and exact
end-to-end targets are reviewed centrally before integration. Module order may
change when a dependency becomes available; the completion standard does not.

## First execution tranche

1. Complete and integrate shared compact analysis, Module T's general value
   theorem, Module H's value dichotomy, and Module G's scalar theorem.
2. Extend the audit with exact end-to-end targets for these theorems. Review all
   hypotheses, the source quantifiers, generated theorem dependencies, and the
   distinction between arbitrary scalar metrics and the full BFGS specialization.
3. Run the pinned build and full transitive axiom audit, preserve logs, refresh the
   status and delivery hashes, review the diff, commit, and push.
4. Continue with the radial/family/parabolic applications and parallel affine
   geometry work. Investigate the formal infrastructure needed by D/L and the
   semialgebraic claim early; a missing library theorem creates a proof obligation,
   not permission to add a mathematical axiom.

## Audit and release gate for every milestone

- Preserve pinned Lean, mathlib and transitive dependency revisions; run actual
  compilation after proof edits and a full checked build at integration.
- Scan every project Lean file for prohibited placeholders and unchecked proof
  mechanisms. Audit every theorem transitively, including generated auxiliaries;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- Link source claims to fully qualified exports with exact statement reviews;
  inspect assumptions and definitions, not merely successful compilation.
- Record conditional helpers separately from completed source theorems and open
  obligations. Keep failed/intermediate logs distinct from current evidence.
- Stage only intended project artifacts, generate and check the delivery manifest,
  confirm original source hashes, review, commit and push. Preserve unrelated
  untracked files.

The final gate is a clean reproducible build from the pinned dependencies, a full
axiom audit, complete coverage of all retained report assertions and synthesis
implications, no unresolved proof obligations for those assertions, and an honest
register of explicit conjectures and historical evidence. Until that gate passes,
the entire report is **not Lean-verified**.


## Execution record

First tranche passed: 19 exact targets, 417 explicit theorems, 594 total theorem
declarations including generated auxiliaries; only the three standard allowed
axioms. All five new objective-level targets have statement and dependency
reviews. Next: T normalization/rank-one/RS/local variants, H finite max-linear
and recurrent affine-hull obstruction, G incoming-jump/scalar certificate claims,
and R inward-radial and supporting-intercept equivalences. Independent inventories
also map Q and the negative constructions before their proof implementation.

Second tranche passed: 26 exact targets, 528 explicit / 768 total theorem
declarations. Detailed statement and peer reviews cover all seven new targets
and their secondary consequences. Next independent tasks are full RS-to-IR
approximation, affine projection/lifting followed by H.C, remaining G examples,
and F rates/structural families. Read-only inventories now cover every retained
claim in A, F, C and U; D/L infrastructure obligations are documented.

Third tranche passed: 36 exact targets, 760 explicit / 1,069 total theorem
declarations, complete transitive standard-axiom audit. The next parallel
implementation tranche is F centered smooth-plus-sublinear (including derived
local smoothness and the source correction bound), quadratic-plus-gauge
corrections followed by H.C, and G ellipsoid/pointwise/tangent geometry. Root
continues integration and remaining affine-covariance/application work.

## Fourth milestone: structural applications and geometric scope

The pinned full build and transitive audit pass for 996 explicit / 1,384 total
theorem declarations and all 44 exact targets. The fourth tranche adds the
actual centered and quadratic-gauge families, affine covariance, main planar
H.C, G ellipsoid/pointwise/accessibility geometry, and Q foundations through
Q.13. Statement and peer reviews are collected in
`audit/REPORT_APPLICATIONS_STATEMENT_REVIEW.md`; actual logs are
`audit/report_applications_check.log`, `audit/build.log` and `audit/axioms.log`.

The G.4 correction distinguishes accessible and all-active jump spans. Its
precise accessible-span consequence is proved, the full-active version keeps
its necessary qualification explicit, and the algebraic countermodel is not
misrepresented as an objective example. Original research sources remain
unchanged. `audit/REPORT_STATUS.json` records this separately.

Next independent work is Q's derived finite-envelope calibration and uniform
compensated transport, H's remaining block/low-rank/relative-interior clauses,
and F's transformed-gauge family. Remaining R/F applications, C/U/A and D/L
constructions, and synthesis/evidence closure are still obligations. Entire-report
verification remains false; no generic conditional criterion is counted as its
undischarged objective-specific application.

## Fifth milestone: parabolic and transformed families, H.8, and G.4 correction

The pinned full build and compiled-environment axiom audit pass for 1,202
explicit / 1,675 total theorem declarations and all 52 exact targets. Logs are
`audit/report_families_check.log`, `audit/build.log` and `audit/axioms.log`.
Only propext, Classical.choice and Quot.sound occur; every audited source hash
matches. See `audit/REPORT_FAMILIES_STATEMENT_REVIEW.md` and its linked reviews.

Q's arbitrary original finite family now has a derived actual θ²rrᵀ certificate
and full-BFGS value/iterate convergence. Uniform calibration, denominator,
logarithm and transport data are proved before all eligible pairs. The explicit
three-branch objective has actual SPD first-step witnesses, arbitrarily small
eligible decreases and unbounded radial quotients on a fixed positive band in
every neighborhood. The printed c1≤2/3 pair scope and the all-c1 rho extension
are distinguished. Literal ordered pruning and printed-field identification
remain separately tracked source-description obligations.

F:transform is proved including literal inverse/Theta' formulas and endpoint
gauge differentiability. H.8 has both the full-slope and actual recurrent-tail
convergence conclusions, derived coordinates and exact initial/current metric
fiber limits. H.7.4 and remaining H class bookkeeping are next-tranche work.

G.4's missing accessibility qualification now has an actual convex-objective
counterexample: shiftedAbs with (c1,c2)=(1/8,1/4), a continuous constant-I band
certificate and genuine limiting gradients whose full-active tangent is zero.
Accessible jumps are zero for these constants. The qualified accessible-span
statement remains valid. Original sources are unchanged; the correction and
example scope are recorded in `audit/G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md`.

Entire-report verification remains false. Remaining F/R applications, G
interpretations, C/U/A, D/L constructions and final synthesis/evidence coverage
remain explicit obligations. Next-tranche drafts live only under audit/scratch
and are excluded from this release manifest until fully integrated and audited.

## Sixth milestone: finite structural families and source closure

The pinned full build and compiled-environment audit passed for **1,445 explicit
and 2,014 total theorem declarations**, with all **61 exact targets** inhabited
and only propext, Classical.choice and Quot.sound in transitive dependencies.
The exact 177 source hashes match the audited bytes. Actual logs are
`audit/report_structures_check.log`, `audit/build.log`, `audit/axioms.log`;
statement scope is reviewed in `audit/REPORT_STRUCTURES_STATEMENT_REVIEW.md`.

Q's original-family theorem and every internally retained source construction
are now mapped, including literal ordered pruning, printed scale and strict
acceptance identities. H's internal H.7.4/class/energy statements are now proved;
its cited earlier three-gradient construction and external two-piece termination
result remain cross-references to reconcile. The rank-at-least-three open
question remains classified as a conjectural gap, not as a theorem.

F's actual max-affine active reduction, literal extended-real threshold and
tail basin are proved, as is the actual coercive five-piece finite line-search
obstruction in every neighborhood of its unique minimizer. R's arbitrary mixed
gauge powers, actual finite polyhedral C1,1 extensions and smooth-plus-PLQ basins
are proved. Extensions need not be convex off their cells. The proof derives
one-sided radial matching; the source's stronger full-gradient boundary assertion
is separately pending. No matrix/iterate convergence or algorithm modification
was added to any family theorem.

The A barycentric Gram-inverse and local affine-independence/positive-coefficient
geometry is checked, but its application to actual finite smooth-max subdifferentials
is still a separate obligation in this frozen release. New scratch proofs do not
change the verified status until integrated and audited.

Entire-report verification remains false. Continue with the explicit matrix-limit
run, finite-ray-singularity step existence, residual decompositions, R branch and
spectral boundary cases, A/C/U, D/L and source synthesis. Review and push the
milestone, then continue these independent proof chains autonomously.

## Seventh execution milestone — completed

The pinned full build and audit checked 1,848 explicit theorems, 2,636 theorem
declarations including generated auxiliaries, and all 78 exact targets.
The added source contracts are in ReportAnalyticTargets and FixedNormalTargets;
see audit/REPORT_ANALYTIC_STATEMENT_REVIEW.md and audit/report_analytic_check.log.
Original source files remain preserved.

Completed: actual finite-max subdifferentials and nondegenerate local affine
correctness; exact affine rank-loss geometry; Euclidean residual decomposition
and basin; finite-max radial compatibility and obstruction; adjacent-cell full
gradient matching; literal parabolic and actual spectral nuclear examples;
actual unexcited full-BFGS run; finite-ray strict step existence; U.1/U.2 and
uniform local basins; exact D/L closed-box root and Jacobian certificate.

Next: actual D/L BFGS cycle and every deterministic trial, then their embeddings
and perturbation dynamics; C's objective comparison field and endpoint estimates;
U.6 and its explicit series/variable-jump examples; A's lower-semicontinuity and
semialgebraic finite-value infrastructure; R/F named family and interpretation
closures. Independently audited new scratch work is integrated only after this
milestone's freeze ends. The whole-report completion gate remains unchanged.

## Eighth execution milestone — completed

The pinned full build and transitive axiom audit checked **2,193 explicit theorems**,
**3,134 total theorem declarations** including generated auxiliaries, and all
**85 exact targets**. The frozen source set has 265 library files plus the root
import and Audit.lean. Actual logs and source/axiom reviews are linked in
audit/REPORT_DYNAMICS_STATEMENT_REVIEW.md. Only standard Lean axioms occur.

Completed: U.6 tangential-only convergence and the separately coupled strongly
convex composite family, their uniform local basins and literal segment geometry;
C's actual finite-corner comparison field and whole-level neighborhood visibility;
R/F named scalar and rectangular Euclidean residual basins/finite-ray steps,
centered actual 2x2 nuclear convergence, literal finite-max central asymptotic,
actual Hessian/ray identities and normalized intercept formulas.

D/L's inherited seed now has exact ordinary three-update closure, intermediate
SPD, every actual gradient and all nine strict trial decisions. An actual
AdmissibleBFGSRun has the literal rho-powered phase data; its nonstationary zero
limit is derived. The exact bracket interpreter returns its lengths at every
iterate, with complete trial histories and actual differentiability/bounds.
This closes the homogeneous deterministic seed, not the later coercive/local
C2 or C1,1 counterexample embeddings.

Next: C buffered derivatives and endpoint transport/secant estimates, then C
convergence/local consequences; U spike/variable-jump examples; D's four-piece
coercive completion and scalar embedding, then L return-map/stable-manifold and
curvature constructions; A lower-semicontinuity/semialgebraic finite values;
remaining R norm-model/interpretation and source synthesis obligations. Scratch
proofs developed during the frozen audit remain excluded until integrated in a
later reviewed release. Entire-report verification remains false.


## Ninth execution milestone — completed

The pinned full build and transitive audit checked **2,718 explicit theorems**,
**3,841 total theorem declarations** including generated auxiliaries, and
all **95 exact targets**, with only the three standard foundational axioms.
There are **313 frozen Lean source hashes** in the status record.
Evidence: `audit/report_construction_check.log`, `audit/build.log`,
`audit/axioms.log`, and the scoped source/type/peer reviews linked in
`audit/REPORT_CONSTRUCTION_STATEMENT_REVIEW.md`.

This milestone adds the actual coercive deterministic seed, D's literal global
C2,1 scalar functions and all closed plateaus, U's actual infinite spike and
all-dimensional objective/convergence/RS separation plus terminating exact
rational oracle, C's actual full-BFGS tail logarithmic transport, and R's
spectral-norm, norm-convention, singular-curvature and current-model intercept
checks. The current-model intercept correction preserves the unresolved older
numerical attribution in the source record.

Next: finish D's actual local two-dimensional embedding and all deterministic
queries; C's secant and main/local consequences; U's variable-jump example;
L's genuine return-map persistence and embeddings; A's remaining compact
gap/semialgebraic infrastructure; remaining nuclear/descriptive identities,
historical references and final synthesis. The entire report remains incomplete.


## Tenth execution milestone: actual D embedding and C principal theorem

Full pinned audit: **3,004 explicit / 4,254 total theorem declarations**,
**106 exact targets**, and **354 frozen Lean source hashes**.
Only propext, Classical.choice and Quot.sound occur. Actual logs are
`audit/report_embedding_check.log`, `audit/build.log`, and `audit/axioms.log`;
exact statement and independent reviews are linked in
`audit/REPORT_EMBEDDING_STATEMENT_REVIEW.md`.

D's complete actual four-branch C2,1 construction now produces the claimed full
BFGS run with all actual search histories, derivatives, SPD matrices, nonstationary
limits and uniform whole-trajectory localization. C's uniform all-pair secant
bound and actual-run log transport feed the principal affine-critical cluster
theorem and convergence/local-basin consequences. U's variable-jump objective,
actual Hessians, local full-BFGS convergence, every-neighborhood RS failure and
corrected c!=0 nonsplitting are checked. L's actual quadratic-seed geometry is
proved without assuming a perturbed orbit.

Next independent tasks: L's actual five-dimensional return map, derivative and
spectral enclosure, constructive nonlinear stable orbit and local embeddings;
A compact affine-gap/semialgebraic infrastructure; C finite-max application and
explicit examples; general rectangular nuclear norm and named family closure;
final source/synthesis/evidence review. D/U retained construction proofs have no
undischarged premise, but the entire report remains incomplete.


## Eleventh execution milestone: affine gap, planar applications, matrix families

The frozen pinned build and full transitive audit pass **3,346 explicit / 4,762
total theorem declarations**, **120 exact targets**, and **394 source hashes**.
Only propext, Classical.choice and Quot.sound occur. Logs are
`audit/report_structural_closure_check.log`, `audit/build.log` and `audit/axioms.log`;
statement/independent reviews are linked in
`audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md`.

A now has actual local affine-distance lower semicontinuity and an attained
positive compact-band gap under its original-active nondegeneracy hypotheses.
C's finite-max corollary, actual positive branch-Hessian sufficient condition,
and every literal three-quadratic example calculation are checked, including
the exact F(x0)<1/100 all-run basin and fixed-band every-neighborhood RS exclusion.
R's arbitrary rectangular nuclear norm is proved from actual Gram eigenvalues,
with its variational formula, zero-safe polar witness, norm properties, centered
and mixed-power applications. Literal weighted first differences have the actual
nonzero-solution local basin.

L's actual analytic three-step return and deterministic oracle agreement are
checked. A constructive contraction on C0 sequences produces actual local stable
orbits; explicit five-dimensional eigenvectors/inverse coordinates convert the
stated block spectral data to this criterion. The two new stable-orbit exact
targets are conditional dynamics infrastructure. The actual J certificate and
infinite physical perturbed-run application are still separate obligations.
The direct orbit proof replaces the source's manifold route for trajectory
existence, without asserting the stronger smooth-manifold/tangency claim.

Next work continues in L's actual shape spectrum/global run and degree-two scalar
and local embeddings, A's actual path calculus and semialgebraic infrastructure,
C's remaining higher-dimensional and uniform transport assertions, and final
all-source/synthesis/evidence review. Entire-report verification remains false.


## Twelfth milestone: actual L dynamics and fixed-metric local failures

The complete pinned build and transitive axiom audit passed 4,039 explicit
theorems, 5,852 total theorem declarations including generated auxiliaries, and
all 145 registered exact targets across 488 frozen Lean sources. Only propext,
Classical.choice and Quot.sound occur. Evidence: audit/report_l_failure_check.log,
audit/build.log, audit/axioms.log, audit/STATUS.json and the frozen source manifest.

L's actual shape Jacobian, kernel rational spectral certificate, full characteristic
polynomial, parameter dependence and local inverse now supply the constructive
positive return orbit. The final actual global Q_mu BFGS run has no assumed
spectrum, trajectory or limit; every deterministic query and its actual derivative
is proved. Both literal smooth and countably affine local embeddings now have
actual infinite BFGS run families with one fixed SPD initial matrix, nonstationary
positive-value limits, strict Armijo/weak Wolfe, exact complete search histories,
and uniform all-query smallness as starts tend to 0. Scalar regularity, the
source 439/446/27 and 512 constants, actual Hessian bounds and local-copy identities
are checked. See audit/REPORT_L_FAILURE_STATEMENT_REVIEW.md and linked independent
reviews for each exact source boundary and reproducible scoped audit.

A's actual path calculus, bounded signed support representations, genuine
polynomial projection reduction and exact affine-coordinate Boolean elimination
are verified infrastructure; general nonlinear QE and finite semialgebraic path
decomposition are still required. C's literal three-dimensional transport warning
and the same quadratic's actual radial convergence are checked.

The entire report remains incomplete. L's fixed identity initialization and its
transformed constants/search/family conclusions are outside this frozen milestone,
as is smooth stable-manifold regularity/tangency. A's general semialgebraic
application/rank-loss spectrum, C's remaining uniform and higher-dimensional
partial statements, and final family/source/synthesis/evidence reconciliation
remain active obligations. Original research sources are unchanged.


## Thirteenth milestone: identity initialization and invariant stable manifold

The frozen pinned build and full transitive axiom audit passed 4,291 explicit
theorems, 6,264 total theorem declarations including generated auxiliaries, and
162 registered exact targets in 543 Lean files. Only propext, Classical.choice
and Quot.sound occur. Evidence: audit/report_source_closure_check.log,
audit/build.log, audit/axioms.log, audit/STATUS.json and the frozen source hashes.

Both actual L local failure families now use identity initialization for one
fixed objective each, with all exact search histories, actual query derivatives,
strict Armijo/weak Wolfe, positive nonstationary limits and uniform query
locality. Actual transformed strong-convexity/Lipschitz/Hessian constants are
derived from the fixed SPD square root. The actual L return map now has a
smooth embedded two-dimensional locally invariant stable manifold, with actual
stable tangent space and positive physical scales. These are conclusions, not
assumed orbit or spectral data.

C's same constructed field satisfies all three uniform estimates for every
sufficiently close eligible endpoint pair. A's literal rank-loss Hessian spectrum,
genuine univariate cells and actual arbitrary-degree simple-root local charts
are checked. T/F source details are closed; G is covered with its explicitly
documented accessible/active-span correction and actual objective counterexample.
See audit/REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md and its linked independent
reviews and delivered-only reproduction scripts.

The entire report remains incomplete. A still needs general nonlinear
semialgebraic projection and finite smooth-path decomposition/application; C
still needs its arbitrary-dimensional constant-rank field/secant partial
construction and A-dependent alternative. Final numerical-display, historical
source, synthesis and evidence reconciliation remain active. Original sources
are preserved, including every disputed claim and documented correction.


## Fourteenth milestone: constant-rank geometry, precision and two-piece termination

The frozen pinned build and full transitive audit passed 4,469 explicit theorems,
6,568 total theorem declarations,178 exact targets and582 frozen Lean files.
Only propext,Classical.choice and Quot.sound occur. Evidence is in
audit/report_geometry_completion_check.log and the accompanying frozen manifest,
compiler logs, declaration inventory and source statement review.

C's actual arbitrary-dimensional constant-rank construction now derives one C1
comparison field and uniform all-endpoint secant correction from the original
active gradients. C2 input does not justify C-infinity field regularity; the
qualification is explicit. L's complete source map and actual Jacobian precision
certificate close its remaining display claim, with a documented last-digit
nearest-rounding correction. The literal two-piece actual BFGS transition relation
is well-founded, and its terminal search ray exposes unboundedness. Arbitrary
full-row-rank linear images have no infinite actual admissible continuation.
The pre-existing two-piece theorem retains Xie–Wächter attribution.

A now has actual finite degree/multiplicity strata, derivative charts, exact
global quadratic root/sign projection with degeneracies, and arbitrary-degree
positive pseudo-division with one finite remainder family chosen before every
specialization. These fragments do not establish general Boolean projection.
General semialgebraic elimination and finite smooth paths, the dependent C
alternative, D numerical-display precision and final synthesis/evidence
reconciliation remain active. The entire report is not yet verified.


## Fifteenth milestone: general projection, critical definability and source conclusions

The frozen pinned build and full transitive audit passed 4,768 explicit theorems,
7,134 total theorem declarations, 205 exact targets and 633 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
audit/report_algebra_completion_check.log, STATUS.json and the accompanying
source hashes, actual compiler/axiom logs and statement/independent reviews.

Actual arbitrary-degree Boolean and finite-coordinate semialgebraic projection
is now proved through actual root-index recursion, sign determination and finite
sampling. Actual supporting/affine-critical set/graph definability follows.
The finite semialgebraic smooth-path argument, finite critical values and low gap,
and C's dependent alternative remain open; conditional path-cover statements
are not a proof of those premises.

H's actual three-gradient rank-two sharpness and I's literal ridge supersession
are proved. D's actual numerical precision, original-box update denominators and
literal Euclidean nine-query locality bound are proved, with five documented
nearest-rounding corrections; four immediate literal exports await the next
central gate. I's complete source reconciliation and E's historical-evidence
classification distinguish checked mathematics from absent original run records.
The entire report remains incomplete. Original research sources are unchanged.


## Sixteenth milestone: actual finite geometry, critical values and planar tame basins

The frozen pinned build and transitive audit passed 5,002 explicit theorems,
7,486 total theorem declarations, 233 exact targets and 693 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual logs and frozen
hashes are report_tame_geometry_check.log, STATUS.json and their companions.

The actual arbitrary-dimensional semialgebraic finite smooth cover is proved
from polynomial root analysis and finite sign refinements. It yields actual
finite ordinary/smooth-path components, finite affine-critical values, the
original low gap and the planar tame convergence basins, without any assumed
geometric decomposition or convergence. D's literal non-strict search and
remaining finite-algebra identities also pass; all453 D lines are reconciled.

The stronger literal A assertions about semialgebraic path graphs and general
piecewise-C1 composition remain in a separate active proof scope. Historical E
jobs/counts/timings/archive identities and R's unidentified older four-piece
numerical claim remain unresolved. The latter is a mathematical attribution
exception, not merely execution history. No original claim is silently retired.
All original research sources are unchanged; the entire report flag is false.


## Seventeenth milestone: literal semialgebraic paths and composition

The pinned full build and transitive audit passed 5,111 explicit theorems,
7,684 total theorem declarations, 249 exact targets and 726 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual closed evidence is
in report_semialgebraic_path_check.log, STATUS.json and the source/hash records.

Actual semialgebraic path graphs, a finite cover in arbitrary dimension,
finite actual continuous-semialgebraic path classes, same-curve regularity and
actual objective composition now close A's literal geometric proof ingredients.
Continuity includes the closed interval; smoothness is asserted off a finite
set of interior parameters, without endpoint derivative claims. C's literal
smooth-path constancy and I's synthesis are covered. All earlier mathematical
corrections remain explicit and the original research sources are unchanged.

M's principal theorems remain verified. The source's additional exact Gram-sum
identity and sharp degree-n−1 potential bound were found to need explicit
exports beyond the sufficient inequalities used in those proofs. They remain
a separate active scope until their delivered compiler/audit gate passes.

R182–187's older four-piece objective is unidentified, so its printed numerical
attribution remains a mathematical obligation. E's original 19-job archive,
counts, timings and execution identities remain unverified. Current D's proved
correction and current universal Lean proofs do not establish those missing
source facts. The entire original report flag remains false pending resolution;
no claim has been silently dropped or replaced by an added assumption.


## Eighteenth milestone: literal M identities and complete shared-graph audit

The pinned complete build and transitive audit passed 5,126 explicit theorems,
7,704 total theorem declarations, 251 exact targets and 729 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual complete evidence
is in report_literal_foundation_check.log, STATUS.json and their companions.

The exact actual-SPD eigenbasis Gram-sum equality closes foundation94–99.
The constructed optimized principal-potential polynomial, sharp degree n−1
bound and actual horizon root limit close foundation151–155. The earlier
principal-matrix and reciprocal-growth proofs remain unchanged.

The shared dependency-graph collector preserves Lean4.19's exact checked
constant cases and handles cycles by reverse reachability. Every milestone17
theorem's type/axiom set was compared with its complete ordinary audit; all
new scoped declarations also passed ordinary collector checks. All original
trailing axiom/target commands remain. This tooling change supplies no proof
premise and changes no mathematical theorem or pinned dependency.

R's unidentified older four-piece numerical objective and E's absent original
19-job archive remain source-resolution obligations. Neither current D nor
current Lean executions establishes those missing original inputs. The entire
original report remains unverified pending their explicit resolution. All
research originals, documented corrections and explicit questions are preserved.


## Nineteenth milestone: reconstructed and corrected report completed

The corrected edition is [CORRECTED_REPORT.md](CORRECTED_REPORT.md), read together
with the unchanged original master report. All retained mathematics is checked:
5,195 explicit/7,813 total theorem declarations, 255 exact targets and 737
frozen Lean files. The new nineteen-job package passed 107 strict literal
type/axiom checks across 93 distinct theorems. All earlier 727 proof files and 7,704
theorem types/transitive axiom sets remain unchanged. The permitted axioms are
propext, Classical.choice and Quot.sound; there are no proof placeholders or
unchecked external mathematical computations.

The new R objective realizes the printed optimizer and supporting errors, with
an actual transformed full-BFGS failure run and direct SP/RS contradiction.
The new E package supplies actual execution evidence. Original unsupported
historical runs and the older unidentified objective attribution are explicitly
superseded, with precise numerical-category/auxiliary substitutions. The nine
earlier mathematical corrections and all 22 original research artifacts remain.

The report-level `corrected_report_verified` is true. Legacy
`entire_report_verified` and `original_snapshot_all_assertions_verified` remain
false for the unamended original snapshot. Explicit open research questions and
conditional criterion hypotheses remain accurately classified. The remaining
input requests in earlier milestone entries are historical and are resolved
for the corrected edition by the user's authorized reconstruction.

Evidence: audit/report_reconstruction_check.log, audit/axioms.log,
audit/REPORT_STATUS.json, verification/reconstructed/fresh/SUMMARY.json, and
audit/report_reconstruction_documentation_validation.log. Reproduce the pinned
build with scripts/bootstrap.sh, the nineteen jobs with
verification/reconstructed/run_all.py, and the completed release gate with
scripts/validate_report_reconstruction_19.py.
