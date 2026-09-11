# Independent review of claim-review20's mathematical dispositions

This is a bounded source/statement review of `CLAIM_REVIEW.md`, the supplemental
disposition/status drafts, and all seventeen current theorem bodies in
`OriginalClaimInterpretation.lean`. The frozen milestone19 source register and
original report chapters were read as evidence, not edited. Final public runner
execution and final status promotion are a separate closing check.

## Actionable findings and their resolution

1. **Arbitrary-reference intercept.** The original draft described
   `(p−1)F(x)+F(0)` as the unrestricted homogeneous intercept formula. The
   existing theorem proves that identity with reference point zero. In general
   the actual definition and Euler's identity give
   `(p−1)F(x)+F(xStar)−g·xStar`. The missing reference qualification matters even
   for a nonnegative convex positive-degree function with an optimizer: for
   `F(x)=max(0,x)^2`, reference optimizer `−1` and evaluation point `1`, the
   actual error is 3 while the origin-reference expression is 1. This example
   has no compact positive sublevel and is not a counterexample to R's theorem.
   The root updated the draft and the disposition row, and the proof scope now
   includes `degree_intercept_at_reference` with no minimizer premise. Its body
   unfolds the actual intercept, distributes the dot product and uses the actual
   derivative Euler theorem. The frozen milestone19 wording is expressly read
   with its origin-reference convention rather than silently edited.
2. **C cluster versus convergence.** The first supplemental status draft called
   compactness/strict contours/local switching the conditions for “C principal
   convergence.” These prove an affine-critical cluster; convergence to the
   minimum additionally needs source affine correctness on the sublevel. The
   updated status now has two rows and retains that additional condition, with
   the semialgebraic low-basin derivation distinguished from semialgebraicity
   alone. The main Lean statement was already correct.
3. **Conditional limit premises.** A blanket status statement denying all
   assumed limits in any proof premise was too broad for the inherited library:
   explicit source-conditional lifting and reusable helpers can take a projected
   or scalar limit. The revised text qualifies the denial to reviewed principal
   convergence/failure conclusions and preserves conditional helpers' premises.
4. **Which D objective.** “The current D objective” was ambiguous because D also
   contains the final embedded objective with minimum zero. The comparison in
   R182–187 is specifically with D231–245's four-piece coercive seed. The root
   made this identification explicit in the new review and disposition.
5. **Runner static scan.** The initial runner rejected the English word “admit”
   in the frozen GeometryContracts comment about smooth endpoint extensions.
   This was a tooling false positive, not a Lean tactic. The owner now masks
   nested Lean comments and quoted strings before scanning actual source tokens;
   no frozen Lean proof was altered. Fresh public execution still needs its own
   final evidence review.

No unresolved mathematical defect was found in the seventeen reviewed theorem
bodies or the revised classification of the listed source items.

## R's full compact-context argument, including every minimizer

Original R19–23 supplies finite convexity, an attained minimum and a compact
sublevel at `b>F*`. R180's illustration adds nonnegativity and degree-p
homogeneity. The new positive-dimensional theorem uses a point `z` with
`F(z)<b`; the original context supplies exactly such a point by taking a
minimizer. This is not an additional source assumption.

For `p≤0`, homogeneity at dilation 2, its nonincreasing power, nonnegativity and
midpoint convexity imply `F(x)≤F(0)` for every x. Midpoint convexity at x and −x
then makes F constant. The strict sublevel is consequently all of positive-
dimensional Euclidean space, contradicting compactness. Thus p>0 is derived.

The homogeneity definition uses nonnegative scalar dilations. Positive degree
then gives F(0)=0. Any minimizer has value zero by nonnegativity and comparison
with the origin. If a nonzero vector has value zero, its whole positive ray is
in the same sublevel. `zero_value_eq_zero_of_compact_sublevel` chooses a dilation
whose norm is larger than the actual bound furnished by compactness. This is a
literal contradiction, not an assumed coercivity or uniqueness oracle. Therefore
**every** minimizer equals zero. The final optimizer-intercept theorem applies
the actual derivative Euler identity after this proved equality.

This dilation convention does not exclude a function in the original compact
context if the undefined source word “homogeneous” is instead read using only
strictly positive dilations. The positive-degree contradiction uses dilation 2
only. After that deduction, finite convexity supplies continuity, and letting
t decrease to zero in `F(t x)=t^p F(x)` gives F(0)=0. The zero endpoint of the
formal convention therefore follows. This is a mathematical convention check,
not an additional independently exported strict-positive-dilation adapter in
the seventeen-declaration scope; no new source hypothesis is necessary.

The input does not assume p>0, a unique minimum, the chosen optimizer's location,
gradient continuity, or any BFGS convergence. It does assume positive dimension
explicitly through `Vec (n+1)`; the original illustration's reading in dimension
zero is kept separate. The proof is not presented as excluding a positive
constant under unconstrained or zero-dimensional hypotheses.

The first thirteen proof bodies also correctly distinguish the unrestricted
degree-zero test from the compact-context theorem, and give an actual global
smooth-plus-univariate decomposition for U's allowed zero-coupling case. The
additional four statements provide a compact-ray argument, arbitrary-optimizer
normalization, the compact formula, and the completely arbitrary-reference
formula. The latest independent owner/peer audit already supplies actual
ordinary type/axiom output and nine expanded contracts; this review read the
actual source rather than treating the old thirteen-declaration peer record as
evidence for the four later declarations.

## Classification checked against the literal original displays

* **G160–176:** N is defined using all active-gradient differences, while the
  preceding annihilation follows only for accessible jumps. The inference to
  the common full-active tangent can fail. The existing countermodel is an
  actual finite strongly convex objective with actual band certificates, not
  merely an arbitrary collection of vectors or a purported bad infinite run.
* **C236:** the source defines `n=(cos θ,sin θ)` and
  `T=(−sin θ,cos θ)`, hence `det(T,n)=−1`. The displayed signed determinant has
  the wrong sign in this frame. Taking its absolute value preserves the
  transport bound. This is an actual false identity with a corrected proof.
* **Q's printed epsilon/2 pair:** source Q explicitly states strict Armijo only
  for `c₁<2/3`. The exact non-strict range `c₁≤2/3` and the separate rho family
  extending to all allowed constants verify and extend that statement; they do
  not refute the printed restricted pair.
* **U395–421:** `‖c‖<1` includes zero. The explanatory variation/nonsplitting
  sentence needs nonzero coupling. The existential heading “need not split”
  remains true, and the convergence claim includes zero. The new proof actually
  exhibits both scalar and smooth functions at zero coupling.
* **C388–406:** C² gradients are C¹, so the checked constant-rank field is C¹.
  Its visibility/secant use does not require C-infinity. The text appropriately
  treats “smooth” as a regularity qualification, not a counterexample to the
  proved C¹ field or planar convergence.
* **L/D decimal displays:** the originals are approximate displays. The exact
  error bounds establish that they are valid within a printed unit. Different
  nearest rounding in one L entry and five D entries is a precision refinement,
  not proof that an approximation assertion was false. Exact oracle margins,
  actual derivative enclosures and spectral conclusions retain their scope.
* **R four-piece tuple:** an explicitly transformed coercive seed realizes the
  tuple and actual failure; this is an existence proof, not recovery of an
  unprovided historical objective. The current coercive D seed has a different
  optimizer. Neither it nor the final embedded D objective is renamed.
* **E and G archive claims:** newly executed jobs do not establish old execution
  counts, precision, timings, formula identities, or their negations. The draft
  says unsupported rather than proved false. The report-defined accumulating-
  kink obstruction is not relabelled as the missing archive identity or a bad
  infinite BFGS trajectory.

The supplemental rows preserve the source theorem hypotheses while separating
false formulas, legitimate restricted statements, regularity conventions,
approximate numerical displays, and unsupported historical assertions. Main
proof/library counts remain the frozen milestone19 counts; standalone review
declarations must be counted separately, including repeated report occurrences.

## Scope and evidence limits

`SOURCE_REVIEW_BINDINGS.json` records the reviewed drafts/source hashes and the
unchanged milestone19 register. The draft status was explicitly pending at this
review; this note does not promote its completion flags. A later final review
must inspect the public common-runner evidence, exact copied source hashes,
output inventories and final supplemental status. It need not rerun every
main-library theorem to validate these standalone checks, but must state that
the main proofs and earlier source reviews are inherited, not independently
reread wholesale in this bounded pass.
