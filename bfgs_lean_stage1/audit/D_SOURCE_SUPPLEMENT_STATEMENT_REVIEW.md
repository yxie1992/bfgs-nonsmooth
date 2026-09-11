# D source supplement: statement and mathematics review

This six-module scope supplements the released actual Module D objective/run proof. It does not alter `report/chapters/D.tex`, whose SHA-256 remains `da61f165db0b2c06fa170540ebed403998ecd4d22412902d1c1b40cca61fdaf0`. Main theorem assumptions and original research sources remain unchanged. The complete static map partitions all 453 source lines; it is separate from the compiler/type/axiom evidence.

## Exact numerical semantics

`DDisplayActual.values` has 33 entries in source order: rho; the eight coordinates of four actual accepted points; nine actual trial objective values; three actual starting objective values; the six accepted Armijo/Wolfe ratios; and six actual scalar center/plateau-length values. The four accepted points use the actual final trial, with its equality to rho times the first point proved from the source full-BFGS cycle. Every trial uses the actual metric/gradient BFGS step. The Armijo quotient is actual objective decrease divided by the negative old-gradient/accepted-step dot product. The Wolfe quotient uses the actual next accepted gradient and the same accepted step. Actual derivatives/unique activity at every tested point are derived from the existing source certificate, not assumed by this scope.

`DDisplayRaw.values_bounds` proves closed outward rational interval bounds on a rectangle containing the entire original closed root box. Rational interval expressions are candidate-generated, and every addition, product, inverse and outward enlargement has a Lean proof term. All inverse intervals used by the generator are strictly positive; negative quotient signs are algebraically handled in the numerator. `DDisplayActual.values_eq_raw` checks every actual quantity against these exact rational expressions. The numerical Python code is neither an oracle nor a proof assumption.

`DDisplayPrecision.printedPrecision` retains the whole-box raw bounds, actual-value bounds, error below one displayed unit for every original entry, error below half a unit for every corrected entry, exact classification of the original rounding, and actual derivative existence at all base and trial points. The unit is 10^-30 for rho and 10^-12 for the tables. The Wolfe value at the first accepted step is exactly -1; applying a twelve-place tolerance to this integer only gives a redundant valid statement.

## Printed last-place corrections

All original displays remain valid as loose approximations with absolute error below one unit in the last displayed place. If the digits are intended to denote nearest rounding, exactly five entries require correction:

| Source quantity | Printed | Nearest twelve-decimal rounding |
| --- | --- | --- |
| Final accepted point, second coordinate (D141) | -0.004954238006 | -0.004954238005 |
| Final accepted Armijo quotient (D206) | 0.375205963572 | 0.375205963573 |
| Final accepted Wolfe quotient (D206) | -0.817119670486 | -0.817119670485 |
| Scalar center for b=2 (D333) | 0.468627450981 | 0.468627450980 |
| Lower plateau length for b=b* (D334) | 0.635765118558 | 0.635765118557 |

The exact theorem proves each changed original has error greater than half a unit and each unchanged original has error less than half a unit. No boundary tie is left undecided. These corrections change no activity, line-search decision, scalar plateau inequality, regularity bound or final run conclusion.

## Actual denominator scope throughout the original box

`DBoxDenominators.sourceBoxDenominators` is universal over every point in the original closed root box, without assuming either root equation. The actual three starting matrices are SPD, all their actual gradient energies are positive, and the actual prescribed lengths 1, 1/4, 1/16 have positive curvature products. The final curvature is strictly greater than 1/100, and the actual last updated matrix is SPD. Rho and 1-rho are positive throughout the box. The released `AlgebraicSeed.box_denominators_and_ratio` separately proves positivity of all six printed polynomial factors and U+129. Together these cover the algebraic formula factors and the actual prescribed-update inverse denominators; they do not claim an arbitrary unprescribed line-search update works at every point of the box.

`lastCurvature_eq_raw` expands the actual second matrix obtained from the quarter-step update, and then the actual sixteenth-step dot product. It does not replace that matrix with a matrix satisfying an assumed recurrence or with the root-only scalar closure. Matrix positivity is derived from actual full inverse-BFGS positivity and each actual positive curvature.

## Literal Euclidean D448 bound

`DEuclideanLocality.maxTrialNorm` is the maximum over exactly the nine original source trials, in the actual Euclidean norm. The initial accepted point is handled by the independently kernel-checked inequalities

`norm(z0)^2 < 1 < norm(trial 4)^2`.

Thus its norm is below the maximum even though it is not one of the nine trial entries. The other two base accepted points are actual accepted trials. All later accepted/trial points are actual positive rho-power scalings, with scale at most one. The exported bound is exactly

`a_n * norm((2,-32)) + a_n^2 * maxTrialNorm`.

It holds for every accepted iterate and every phase-compatible actual trial, for every natural n, and tends to zero. The proof uses Euclidean coordinate identification, norm homogeneity and the triangle inequality. No coordinate-sup norm is silently substituted for the source Euclidean norm.

## Explicit scope boundaries

The source theorem's excluded strong-Wolfe and positive-measure-basin claims remain excluded. Historical `verify_certificate.py`/SymPy execution correspondence is provenance; these programs are not proof premises, and no claim to have formally verified those historical executions is made. Source statements labelled immediate consequences in `SOURCE_MAP.md` are algebraic/logical consequences of the listed checked declarations, not new assumptions. The central released principal theorem remains unchanged.

## Reproduction

From the project root, `bash audit/scratch/d_source_closure/verify.sh` freshly compiles all six modules in dependency order, checks every explicit declaration's actual type and transitive axioms, checks the three complete target types, verifies frozen source hashes, and checks byte-identical regeneration of both rational candidate certificates and numerical candidate metadata. `validation.log` records completion; `rebuild.log`, `axioms.log`, `contracts.log`, and `regeneration.log` retain the actual evidence. Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` are allowed by the scoped validator.
