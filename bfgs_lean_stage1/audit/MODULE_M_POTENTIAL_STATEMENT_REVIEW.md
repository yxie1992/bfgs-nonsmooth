# Sharp finite-potential degree and literal horizon root limit

Source: unchanged `foundation.tex`151–154. This two-module scope closes the
sharp polynomial claim previously replaced in the growth proof by a sufficient
degree-n estimate. The already verified principal hierarchy and superquadratic
theorem are unchanged. Nothing in this scope is part of the frozen milestone17.

The actual polynomial is the finite sum of monomials
`r^j e(j+1) X^j` for `j ∈ range n`. Its evaluation is exactly the existing
`ScalarHierarchy.weightedPotential n (r*t) e`; no polynomial representation
premise is assumed. Its natural degree is at most `n-1`. The zero-dimensional
case gives the zero polynomial and the natural-degree convention yields zero.
The nonnegative coefficient estimate uses `j<n ⇒ j≤n-1`, giving the sharp
power, including dimension zero, rather than the former power n.

The source parameter is used literally: for horizon m≥2,
`eta = D/[c(m-1)]`. The principal coefficients are actual principal submatrix
determinants of H. The polynomial is evaluated at the real value m-1 and the
bound is the actual fixed potential with parameter D/c times `(m-1)^(n-1)`.
The generic identity even handles zero denominators under Lean's total field
operations; the actual run application supplies D>0 and c>0 before using the
source's optimizer. D is the actual summable tail `sum_i R.d(J+i)` and its
strict positivity follows from positive predicted decreases, not an assumption
about an unrelated budget. The tail J remains fixed throughout the horizon
limit. No uniform bound on H_J or the fixed polynomial is introduced.

The mth-root conclusion is proved explicitly as well. The positive trace slot
bounds the actual potential below; the sharp power bound bounds it above.
Raising both bounds to 1/m and using actual real-power limits gives convergence
to one. Positive dimension follows from the actual FullBFGSRun energy, while
PSD/principal-coefficient positivity follows from its matrices. The objective
run bridge already constructs this same full-matrix run from initial SPD,
actual weak Wolfe and ordinary updates. No assumed hierarchy, coefficient
bound, polynomial degree, or potential limit is a premise of the final target.

`sharpPrincipalPotential : SharpPrincipalPotentialTarget` jointly retains the
actual polynomial witness, its degree bound, exact optimized-potential
identity, sharp finite-horizon bound, and literal mth-root limit. It requires
only the actual full run, c>0 and summable predicted decreases. G may be any
real value because only G² enters this algebraic claim; the report's positive
gradient bound is therefore an allowed specialization, not a new assumption.
This result alone makes no additional claim about full-BFGS convergence.

Reproduce from the project using
`bash audit/scratch/module_m_potential_scope/verify.sh`. It rebuilds the actual
main normalization dependency, both owned sources and the 12-declaration
actual-type/transitive-axiom driver, and checks the complete target by strict
Lean definitional type comparison. No placeholder, custom mathematical axiom,
native computation, or unchecked external mathematical result is used.
