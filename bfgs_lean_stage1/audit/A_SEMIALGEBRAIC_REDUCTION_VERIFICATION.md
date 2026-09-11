# Genuine semialgebraic syntax and actual supporting-graph reduction

Three compiler-clean files contain 34 explicit declarations, with a fresh scoped build, complete actual types/standard transitive axioms, three strict infrastructure contracts, and unchanged hashes. This is a supporting infrastructure tranche, **not** a proof of `A:semialgebraic`.

`PolynomialFormula` is an inductive finite syntax with polynomial equality-to-zero and strict positivity atoms, conjunction and negation. There is no quantifier constructor and no path/decomposition premise. `IsSemialgebraic S` requires an actual such formula whose truth set is exactly S, on a finite coordinate type. Thus it is the ordinary Boolean-polynomial definition; it has not been redefined to include desired projection or regularity properties.

Polynomial substitution uses actual multivariate polynomial substitution and its proved evaluation identity. This derives polynomial preimage closure. Complement, intersections, unions, finite unions/intersections, nonnegative polynomial inequalities, and the empty/full sets are proved directly from finite syntax. Actual output-graph semialgebraicity is proved for polynomials and for any actual attained finite maximum of polynomials. Empty finite index types are not assumed nonempty; the actual maximum representation itself discharges that issue.

For an arbitrary everywhere real-valued semialgebraic objective F, `badSupportSet F` is an explicit set in variables (x,g,z,a,b). It enforces a=F(x), b=F(z), and the strict violation g·(z−x)>b−a. The two graph conditions are polynomial preimages of the actual graph of F; the violation is a literal polynomial inequality. This proves that the lifted set is genuinely semialgebraic without projection closure or objective convexity.

The exact equality `nonSupportGraph_eq_projection` proves that projecting this lifted violation set onto (x,g) gives the complement of the **actual global supporting graph**. The forward direction chooses actual F(x) and F(z), so there is no arbitrary value oracle. The reverse direction substitutes those graph equalities into the actual supporting inequality. This identity is unconditional for every F and handles dimension zero.

The final `supportGraph_semialgebraic_of_projection` takes projection closure as an **explicit conditional premise**. This premise is not an axiom, not hidden in any definition, and not discharged. It illustrates the precise next dependency. In particular, neither semialgebraicity of the actual support graph nor of the affine-critical set is claimed unconditionally yet.

The previous five-file affine-path tranche already proves signed affine representation by at most n+1 actual supports, path-composition constancy with finite derivative exceptions, finite-cover to finite-value assembly, and the finite-value low-level gap. The remaining source-proof layer consists of actual coordinate projection elimination and finite piecewise differentiable semialgebraic path decomposition, including composition regularity. These remain substantial, separate proof obligations. The pinned mathlib inventory contains no theorem supplying them.

Reproduce the delivered source with `bash audit/verify_affine_spatial_hessian.sh`. Main source hashes and declaration names are in `audit/a_semialgebraic_reduction_declarations.json`; the same prefix identifies actual compiler, axiom, contract and validation logs.


## Main-library delivery

The compiler-clean frozen snapshot was copied to `BfgsVerification/` after milestone 11. Only local import names changed to delivered main-library module names. Fresh main hashes, exact declaration/axiom drivers, and contract logs use the `a_semialgebraic_reduction` prefix in `audit/`. Reproduce with `bash audit/verify_affine_spatial_hessian.sh`; it uses no scratch source or object file. Original snapshot and peer-review evidence remain available. The scoped main manifest, not the old scratch hashes, describes the delivered source bytes.
