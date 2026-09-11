# Centered smooth-plus-sublinear statement and dependency review

Status: **31 declarations in six modules compiled and axiom-audited** with the
pinned Lean 4.19.0 toolchain. This covers the first section of
`BFGS_MASTER_REPORT_LaTeX/report/chapters/families.tex`: F:centered, its explicit
uniform correction estimate, the nonunique/unique/local clauses, and the
recentring paragraph. It does not mark the other Module F sections complete.

## Statement coverage

- `CenteredSmoothCalculus.lean`: standard local C1,1 means differentiability on
  U and local Lipschitz continuity on U of the actual Fréchet derivative. U is
  open in the final theorem. The ordinary finite-Pi norm is explicitly compared
  with the actual Euclidean sum of squares. The local supporting inequality
  assumes convexity only on U. The Taylor estimate is derived by the mean value
  theorem, not supplied as a field assumption.
- `CenteredLocalUniform.lean`: a finite compact cover derives one positive radius
  and one derivative Lipschitz bound on full balls centered at every point of K.
  It also derives continuous coordinate gradients and their Euclidean compact
  bound. Empty compact sets and arbitrary finite dimension are permitted.
- `CenteredCocoercivity.lean`: local C1,1 and compact K contained in open convex U
  derive a positive constant L and the Euclidean secant inequality. The two
  descent test points lie in the proved local balls. No smooth extension outside
  U, Hessian, integration, or gradient/matrix/iterate limit is used.
- `CenteredSecants.lean`: the nonsmooth summand derivative is derived from the
  actual endpoint derivatives of F and psi using subtraction and translation.
  Gamma's homogeneous supporting identities give its nonnegative pairing and
  own curvature bound. The scalar weighted estimate handles zero component
  curvatures; only the total curvature is divided by.
- `CenteredSmoothSublinear.lean`: `exists_pair_correction_bound` exports L's
  Euclidean secant inequality, the **global** supporting-gradient bound G for
  gamma, and the actual Euclidean radius R, as well as the precise
  `L * R^2 + 2 * G * R` correction. `centered_uniform_correction` specializes to
  the actual accepted full-BFGS gradients and derives positive total curvature
  from the run theorem. `centered_values` derives the required cumulative budget
  and applies the existing actual-matrix energy/reciprocal-growth chain.
  `centered_iterates` adds uniqueness only for the iterate conclusion.
  `local_centered_basin` chooses delta before every admissible run, covering every
  allowed initial SPD matrix and line-search constants.
- `CenteredRecentering.lean`: `center_support` derives the supporting vector at
  gamma(0) from minimum of the sum. It differentiates a one-sided smooth scalar
  surrogate, not F or gamma at the minimizer. `centered_rewriting` proves exact
  equality of the adjusted sum to F-Fstar on U and proves both summands
  nonnegative and minimized at the center. Separate results preserve convexity,
  positive degree-one homogeneity, and the original local C1,1 regularity.

The objective equality is required only on the original open neighborhood U;
this includes the globally represented source case and gives the local case
without changing the objective along a run. Neither summand is assumed to be
minimized separately. Gamma is not assumed nonnegative, symmetric, coercive, or
differentiable at the center. Psi is not assumed convex/smooth outside U. There
is no nonzero-dimension or rank hypothesis.

## Choice of the smoothness constant

The source's centered theorem chooses a uniform L existentially. The formal
proof obtains a local remainder coefficient M, then increases L so L>=2M and
both descent test points remain inside the original neighborhood. The final
Euclidean inequality and correction formula use this same chosen L exactly.
This is an alternate proof of the source's needed existence-of-constant claim;
no mathematical source correction or added assumption is needed.

The more general independent assertion that an **arbitrarily prescribed**
Euclidean Lipschitz derivative constant on all of an arbitrary open convex set
is the sharp cocoercivity constant is not exported here. No such result is
assumed transitively. That sharp Baillon--Haddad theorem is unnecessary for the
centered convergence and displayed existential uniform correction verified by
this tranche; it must not be described as independently formalized.

## Reproducible evidence

- Compiler history: `centered_calculus_build.log`, `centered_uniform_build.log`,
  `centered_cocoercivity_build.log`, `centered_secants_build.log`,
  `centered_main_build.log`, `centered_recentering_build.log`. The last log ends
  in the successful build importing all six modules; earlier failed drafts are
  retained as actual compiler feedback.
- `CENTERED_AXIOMS.lean` / `centered_axioms.log` enumerate all 31 declarations.
  Every transitive dependency set is contained in
  `{propext, Classical.choice, Quot.sound}`.
- `CENTERED_CONTRACTS.lean` / `centered_contracts.log` independently check the
  full actual-run value theorem, local-basin quantifier order, and center support
  against explicit expected types. The C1,1 abbreviation is expanded into its
  two standard hypotheses in those contracts. The log also prints the precise
  correction and recentering signatures.
- `centered_declarations.txt` and `centered_validation.log` record coverage.

No `sorry`, `admit`, custom mathematical axiom, or `native_decide` appears in the
six source modules. The proofs use no unchecked external mathematical
computation. Original research sources were not changed.
