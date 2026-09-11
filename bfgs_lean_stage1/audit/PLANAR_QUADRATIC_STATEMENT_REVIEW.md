# C explicit three-quadratic example: statement review

Scope: `C.tex` lines 344–387, eight frozen files, 105 explicit declarations, five exact source targets. Original research files are unchanged. No mathematical correction to the printed example was needed.

## Literal model and actual calculus

`PlanarQuadraticExample.branch` is exactly the printed triple

- f0(u,v)=u+u²+v²/2;
- f1(u,v)=v+u²/2+3v²/2;
- f2(u,v)=−u−v+3u²/2+v².

`objective` is the actual maximum `max f0 (max f1 f2)`. Maximum attainment and local finite-max representation are proved directly. `gradient` is defined from the literal linear coefficients and diagonal matrices, and `branch_hasGradient` proves these are the actual Fréchet derivative coordinates at every point. `branch_second_hasFDerivAt` and `branch_actual_hessian` prove the actual second-Fréchet Hessian matrices are diag(2,1), diag(1,3), and diag(3,2). The Loewner bounds I≤Hess fi≤3I are proved as actual PSD differences, rather than assumed for a proxy matrix.

Actual branch convexity, Euclidean strong convexity with modulus one, and their inheritance by the actual maximum are proved. The branch average is exactly `sqNorm x`; this gives F(x)≥u²+v², F(0)=0, uniqueness of zero, and every compact sublevel. The Euclidean square is explicitly the sum of coordinate squares, irrespective of the ambient finite-Pi norm convention.

## Exact coefficients and basin

`denominator`, `numerator`, and `coefficients` are exactly the printed rational formulas. On the **closed** box |u|,|v|≤1/10, their proved lower bounds are 267/100, 23/100, 49/100, and 45/100. The code proves positive coefficients, sum one, and their actual gradient combination equal to zero. Polynomial elimination with the actual denominator proves affine independence; uniqueness proves that every affine zero representation equals the printed formulas. At zero, all branches are active, the actual gradients are the printed (1,0),(0,1),(−1,−1), and all three coefficients are exactly 1/3.

The actual finite-max subdifferential theorem and positive-barycentric stability give pointwise affine-critical correctness on the box. This uses global branch differentiability and local maximum attainment; no active-gradient identification is supplied as an unproved premise. The independent planar finite-max regularity bridge derives actual smooth or regular two-branch charts at every non-affine-critical point. Strong convexity independently excludes nontrivial segments in every objective-level boundary.

F≥sqNorm places the complete closed 1/100 sublevel inside the coefficient box. `fullBFGS_explicit_basin` therefore proves the exact printed strict start condition F(x0)<1/100 for every actual admissible infinite full-BFGS run, with both values and iterates tending to zero. The final theorem has no supplied compactness, geometric regularity, coefficient, active-gradient, hierarchy, metric, or convergence hypotheses. It quantifies over every run with arbitrary coupled SPD initialization and fixed valid Armijo–weak-Wolfe constants.

## Printed curve and real crossing pairs

`tieHeight u=(-1+sqrt(1+4u+2u²))/2` is the literal printed curve. For 0<u<1/10 the code proves its equation v+v²=u+u²/2, positivity, 3u/4<v<u, actual f0=f1 activity, and strict inactivity of f2. It proves the actual gradient jump and its radial pairing u²/2−v²<0. No tie, gradient, contour, or rank condition is assumed for the curve.

The pointwise bound |v(u)−u+u²/2|≤u³ proves the printed O(u³) expansion on its stated positive-side domain. Both the literal bound and the one-sided `IsBigO` conclusion are exported; no outward or negative-side extension is implied.

`oldPoint=(u,v+ε)` and `newPoint=(u,v−ε)` are literal. Strict activity of branch 1 at the old point and branch 0 at the new point is derived for all sufficiently small ε>0 from the curve equation and the positive third-branch gap. Actual endpoint derivatives follow from local objective equality with each branch.

The code proves the exact printed formulas:

- step=(0,−2ε);
- d=2ε(1+3v+3ε);
- t=2ε(1+2v+4ε);
- F(old)−F(new)=ε(1+4v)+ε².

The actual radial numerator is u²/2−v²+ε(1−2v)+4ε². This tends to the proved nonzero negative jump while t tends to zero through positive values. The squared radial quotient tends to positive infinity. All fields of `EligiblePair objective (1/4) (1/2)` are derived, including actual derivatives, positive descent, Armijo, convex-decrease, and weak Wolfe.

## Exact separation quantifiers

`eligible_radial_unbounded_on_neighborhood` states that for **every** neighborhood K of zero there is η>0, selected **before every** δ>0 and C, with actual differentiable pairs in K, η≤F(z)≤F(x), the printed eligible constants, d≤δ, and C*t smaller than the squared radial numerator. An actual SPD matrix H is also derived with `bfgsStep H g 1=z−x`; no assumed trial eligibility or matrix compatibility appears in the final statement.

The SPD witness realizes each individual pair. Neither an infinite trajectory following these pairs nor a BFGS divergence claim is asserted. The actual example converges in its explicit basin despite RS failing on every neighborhood and every positive sublevel. The no-RS theorem uses the same actual eligible pairs and the correct fixed-positive-band order of quantifiers.

## Validation and exact targets

Main source hashes: `audit/c_quadratic_source_hashes.json`. The independently reviewed source hashes are retained in `audit/c_quadratic_reviewed_source_hashes.json`; main imports are qualified, and the validator proves import-normalized equality to that reviewed snapshot. Declarations: `audit/c_quadratic_declarations.txt`. Reproduce from the delivered checkout with `bash audit/verify_c_quadratic.sh`; it uses only main sources and delivered audit artifacts, runs the pinned compiler, audits every explicit declaration's transitive axioms, and performs five strict `Meta.isDefEq` checks. The Python checker is structural/log-only and performs no mathematical computation.

Exact targets: `planarQuadraticModel`, `planarQuadraticCoefficients`, `planarQuadraticBasin`, `planarQuadraticCurve`, and `planarQuadraticSeparation`. Main logs: `audit/c_quadratic_build.log`, `audit/c_quadratic_axioms.log`, `audit/c_quadratic_contracts.log`, and `audit/c_quadratic_validation.log`. Independent review passed with no defects: `audit/PLANAR_QUADRATIC_PEER_REVIEW.md`, `audit/c_quadratic_peer_validation.log`, and `audit/c_quadratic_peer_contracts.log`. Original scratch correspondence is separately attested in `audit/c_quadratic_scratch_correspondence.log`; it is not a reproduction dependency.

## Remaining module-level boundaries

This tranche is only the explicit C example and its radial separation. The semialgebraic alternative, arbitrary-dimensional constant-rank partial construction, and three-dimensional canonical-field transport warning are separate C source claims. No original research source was altered and no conditional family theorem is labeled as an unconditional global result.
