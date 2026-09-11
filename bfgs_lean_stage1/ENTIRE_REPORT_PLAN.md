# Entire-report Lean verification plan

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
