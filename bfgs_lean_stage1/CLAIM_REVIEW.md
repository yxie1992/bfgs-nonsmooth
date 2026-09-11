# Review of the report's actual mathematical claims

The object of this work is the mathematics in the report: the stated hypotheses,
conclusions, quantifier order, and proof dependencies. Creating Lean files or
reproducing an execution count is not a substitute for proving those claims.
This review supplements the completed source register and corrects an overly
broad possible reading of its list of “corrections.”

The preserved report cannot be certified verbatim: it contains an incorrect
signed identity, a faulty accessible-span inference, ambiguous scope statements,
and unsupported historical attributions. Its retained mathematical claims have
Lean proofs, with the explicit qualifications in the
[corrected edition](CORRECTED_REPORT.md) and the more precise dispositions below.
An explicit conjecture remains a conjecture; an unsupported account of a past
computation remains unsupported. Neither is promoted to a theorem.

## What was checked against the original claims

The existing [source register](audit/REPORT_STATUS.json) partitions all 4,323
original chapter lines into 172 disjoint spans across all 14 modules. Each
mathematical span identifies its reviewed Lean exports and assumptions. That
register and the 737 main Lean sources are frozen at commit
`79ff4d82eece6d1c87b2ee177e43461cc822c8eb`. Their actual pinned compiler,
complete declaration/axiom audit, and source reconciliation are retained.

The new review directly reopens the most consequential statement boundaries,
rather than inferring mathematical completeness from that register's flags:

| Claim | Fresh statement and proof check |
|---|---|
| M.1–M.3, exact Gram sum, sharp potential | Actual principal-submatrix determinants of the actual inverse-BFGS update, every degree in arbitrary finite dimension, normalized hierarchy derived from the matrix theorem, original finite-horizon constants and indexing, reciprocal-mean divergence and superquadratic reciprocal sums. The raw sequence contracts derive all later matrix positivity from initial SPD and weak Wolfe. |
| A, finiteness and low affine-critical gap | Boolean-polynomial graph hypotheses, actual global supporting vectors, derived finite path covers, regularity of both the path and the objective along it, constancy and finite critical values. Final contracts do not assume the finiteness or path-cover conclusion. |
| C, principal affine-critical cluster and planar convergence | Expanded actual derivative, step, full matrix update, Armijo and weak Wolfe; actual affine hull of global supports and Euclidean distance; derived shrinking steps, field construction and reciprocal-energy contradiction. The cluster result retains the source geometric hypotheses; convergence additionally requires affine correctness on the sublevel, supplied by A in its low semialgebraic basin. |
| D/L, the negative examples | Actual objective geometry, actual infinite BFGS runs, exact accepted and rejected trials, differentiability at every query, identity initialization where claimed, fixed objectives before shrinking-neighborhood quantifiers, and discharged stable-manifold hypotheses. D's parameter independence and invariance of successful search under extra fuel have new explicit proofs. |
| R, homogeneous intercept | New proofs use nonnegativity, convexity, homogeneity and a compact sublevel containing a point strictly below its bound to derive positive degree. The arbitrary-optimizer issue is checked explicitly in the delivered proof. |
| U, variable jump example | A new proof exhibits the actual smooth-plus-univariate decomposition at the allowed parameter `c=0`, including smoothness of the quadratic part. This qualifies the explanatory nonsplitting sentence, not the convergence theorem. |

The bounded reviews and literal contract drivers are in
[the claim-review package](audit/claim_review20/README.md). They inspect actual
definitions and proof bodies and compare frozen literal propositions with
actual theorem types. Their transitive-axiom checks use Lean's ordinary
`collectAxioms` and `#print axioms`. The Python runner records processes and
validates evidence; it supplies no mathematical answers to Lean.

This is a fresh independent agent review of those critical chains, not a claim
that this additional pass independently reread every proof in the whole library.
Coverage of T, F, H, Q, G, the remaining M/A/C/R/U ingredients, and the detailed
D/L supplements also relies on the earlier preserved source-by-source reviews
and proofs. All of their frozen source and evidence hashes are revalidated.
The agents are not being represented as independent human referees. Reusable conditional results keep their stated premises, including projected-run limits in lifting implications; such helpers are not substituted for proofs of the principal convergence conclusions.

## Exact disposition of the disputed statements

The earlier list mixes false formulas with extensions, regularity conventions,
rounding refinements and provenance problems. They must not all be described as
counterexamples to the report's main theorems.

| Original item | Disposition after statement review |
|---|---|
| G160–176, accessible versus all-active tangent space | The inference from annihilating accessible jumps to annihilating every active-gradient difference is invalid in general. The verified finite strongly convex countermodel separates the spans. The accessible projection conclusion is valid; the all-active conclusion needs the stated spanning or annihilation condition. |
| Q200–256, printed epsilon/2 pair | Its exact Armijo range is `c1≤2/3`, consistent with the source's stricter stated range. The rho family extends the separation to every allowed `c1<1`. This is a verified scope boundary and extension, not a refutation of the correctly restricted printed example. |
| C, negative-orientation transport | The printed signed determinant has the opposite sign for `det(T,n)=-1`. The corrected identity is proved. Absolute transport bounds and the convergence conclusions are preserved. |
| U395–421, variable jump | `‖c‖<1` permits zero. At zero the jump does not vary with the tangential variable and the objective splits. Nonzero coupling gives the intended nonsplitting example. The heading “need not split” is existential and remains valid; convergence includes zero. |
| R176–180, degree-p intercept | At reference optimizer zero, the unrestricted-degree formula needs the term `F(0)`. For an arbitrary reference `xStar`, the general formula is `(p−1)F(x)+F(xStar)−g·xStar`. However, a positive constant does **not** refute the formula in R's compact positive-sublevel context in positive dimension. The new proof derives positive degree and proves that every optimizer is zero in that context, so neither fact is an added assumption. The source illustration is distinguished from a claim over unrestricted degree-zero functions or dimension zero. |
| R182–187, four-piece numbers | D’s four-piece coercive seed at D231–245 does not have the printed optimizer and support tuple. The explicitly defined transformed objective realizes that tuple and its actual BFGS failure mechanism. This proves the requested example's existence, not identity with an unavailable older objective. |
| C388–406, “smooth” common-rate field | C² branches yield a C¹ gradient family and C¹ field, which is sufficient for the proved claim. A C-infinity interpretation is not established. This is a regularity qualification, not a failure of the C¹ construction or convergence result. |
| L168–174, approximate Jacobian | The old entries are valid approximations within `10^-15`. One last digit changes under nearest rounding. The exact derivative enclosures and hyperbolicity proof are unaffected. |
| D141,206,333–334, approximate decimals | The old displays are within one unit of their last printed digit. Five nearest-rounding values are corrected with exact error bounds. These refinements do not invalidate the strict oracle margins or negative theorem. |
| E and VERIFICATION_REPORT, historical jobs | Newly run jobs cannot prove that the reported old jobs ran with the given counts, times or precision. Those historical assertions are unsupported, not proved false. The replacement execution record is explicitly new. Analytic claims are supported by their Lean proofs, not by a finite experiment. |
| G263 and E125–128, unspecified archived auxiliary | The report-defined accumulating-kink objective has an actual proof. Substituting it for an unspecified archive example does not recover the identity or execution history of the missing example. |

The formal homogeneity convention includes nonnegative scaling. In the compact positive-dimensional context, the degree-positivity argument uses only scaling by two; with the positive-scaling convention, finite convexity gives continuity and the zero endpoint follows once positive degree has been derived. This convention does not exclude an additional source-context function.

The origin-reference qualification also applies to the general-formula wording in the frozen earlier correction companion. The new general-reference formula and the compact arbitrary-optimizer theorem make the distinction explicit.

All original research files remain unchanged. The explicit new R construction
and replacement E evidence were authorized after the user explained that no
source inputs exist. That authorization changes what can be constructed; it
does not turn historical assertions into mathematical facts.

## Verification boundaries and reproduction

The unchanged main inventory contains 5,195 explicit theorems, 7,813 total
theorem declarations and 255 exact targets. These counts identify the audited
artifact; the source correspondence and theorem statements establish its scope.
The additional claim-review declarations live in a separate, reproducible Lean
package and are not added to those main-library counts. Repeated checks of the
same declaration in separate drivers are identified as repeated reports.

From `bfgs_lean_stage1`:

```sh
python3 scripts/validate_report_reconstruction_19.py
python3 scripts/verify_report_claim_review_20.py --run
python3 scripts/verify_report_claim_review_20.py
```

For a rebuild of the main library from its pinned inputs, run
`bash scripts/bootstrap.sh`, then source `scripts/env.sh` and run
`python3 scripts/check.py`. The new review uses that already compiled, hash-bound
library; it does not claim to have repeated the entire main build when compiling
its standalone drivers.

The [supplemental status register](audit/claim_review20/STATUS.json) records the
original-claim dispositions, inherited whole-report scope, newly proved results,
and exact fresh audit evidence. Its “review complete” status does not mean
“every sentence of the original is true.” No `sorry`, `admit`, custom mathematical
axiom or unchecked external computation is admitted; the allowed transitive
axioms remain `propext`, `Classical.choice` and `Quot.sound`.
