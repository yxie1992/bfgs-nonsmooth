# C three-dimensional canonical-field warning

Five frozen compiler-clean files, 55 explicit declarations, two exact source targets. The complete scoped rebuild, actual type/standard transitive-axiom audit, strict target checks and unchanged hashes pass. Source: `C.tex` lines 408–421. No original research text is altered.

The objective is literally xᵀQx/2 with Q=diag(1,2,3), and its actual gradient is Qx. Positive definiteness, convexity and arbitrary finite-order differentiability are proved. The base is (1,1,1); the step is (ε,0,−(ε+ε²)/3). Actual endpoint gradients yield y=Qs, d=ε², t=ε²(ε²+2ε+4)/3 and the actual column determinant 4ε²(1+ε)/3. Every 0<ε<1/10 pair is proved Armijo–weak-Wolfe eligible at the literal constants 1/4 and 1/2, and an actual SPD matrix realizes it as a first full-BFGS step. No accepted-pair or gradient oracle is an input.

The canonical common-rate field is exactly Qx/‖Qx‖², with Euclidean squared norm. Its denominator is nonzero at both endpoints, so actual differentiability of every finite order and the unit gradient pairing follow. The nonzero determinant proves that the new field is outside the span of the old field and the executed step. No finite scalar transport coefficients exist.

The source's stronger projected rank-one conclusion is also literal: for **every real multiplier a**, the matrix a Π_s(v(x)v(x)ᵀ)Π_s−Π_s(v(z)v(z)ᵀ)Π_s is not positive semidefinite. The explicit vector (−2(1+ε),10+ε,−6) is perpendicular to the step and the old field, while its pairing with the new gradient is 4ε(1+ε)>0. The proved perpendicular quadratic characterization of the projected Loewner condition gives the contradiction. Thus the result is not merely failure of a chosen coordinate decomposition.

The same objective has an actual radial secant certificate on every sublevel, proved by PSD Cauchy–Schwarz with bound 2b. The radial field x has visibility pairing 2F(x) and exact transport z=x+s. Compactness of sublevels and uniqueness of zero are derived, and every actual infinite admissible full-BFGS run on this quadratic is proved to converge to zero. This preserves the source's distinction: one canonical field fails transport, while a radial certificate works. No nonexistence of all certificates or BFGS counterexample is asserted.

Exact targets: `spatialCanonicalWarning : SpatialCanonicalWarningTarget` and `spatialQuadraticRadial : SpatialQuadraticRadialTarget`. Reproduce the delivered source with `bash audit/verify_affine_spatial_hessian.sh`. Main source hashes and declaration names are in `audit/c_spatial_warning_declarations.json`; the same prefix identifies actual compiler, axiom, contract and validation logs.


## Main-library delivery

The compiler-clean frozen snapshot was copied to `BfgsVerification/` after milestone 11. Only local import names changed to delivered main-library module names. Fresh main hashes, exact declaration/axiom drivers, and contract logs use the `c_spatial_warning` prefix in `audit/`. Reproduce with `bash audit/verify_affine_spatial_hessian.sh`; it uses no scratch source or object file. Original snapshot and peer-review evidence remain available. The scoped main manifest, not the old scratch hashes, describes the delivered source bytes.
