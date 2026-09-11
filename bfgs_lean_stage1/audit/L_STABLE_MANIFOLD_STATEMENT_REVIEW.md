# Actual smooth local stable manifold for Module L

This frozen twenty-module, ninety-declaration scope addresses the ancillary geometric assertion in `report/chapters/L.tex` lines 197–214. The previous actual-orbit construction supplied convergent orbits but did not establish smooth parameter dependence, an embedded graph, or tangency. This scope derives those properties and explicit local forward invariance for the literal return map. Original research sources are unchanged.

## Final source contract

`LReturnStableGraph.lStableInvariantManifold` has exactly the named proposition `LStableInvariantManifoldTarget`. For the actual `LNormalizedReturn.returnMap μ`, its actual fixed point `seed`, and every prescribed neighborhood W of that point, it constructs one continuous linear coordinate equivalence E, one graph function h, and one open parameter neighborhood V in the actual two-dimensional real space. The parameterization is literally `seed + E (a, h a)`.

The same parameterization is C∞ on V, takes zero to seed, and is a topological embedding when restricted to V. Its actual Frechet derivative at zero is E composed with stable-coordinate inclusion. The range of that derivative has real dimension exactly two and is exactly the set of vectors whose powers under the actual return-map derivative converge to zero. This identifies the genuine linear stable space; no separate tangent-space or spectral-subspace premise is supplied.

Every parameter in V has an actual forward return-map orbit starting at its graph point, staying in W for all time and converging to seed. The physical scale equals the second stable parameter in the constructed chart, and the final contract includes points with scale in (0,eps) for every eps>0. There is also an open V0 containing zero with V0⊆V such that the actual return map sends this same graph over V0 into the same graph over V. This is explicit local forward invariance, rather than an implicit choice of stable-manifold terminology. The contract does not assert global invariance of an arbitrarily truncated local chart or classify all large forward orbits.

The map is rational and analytic near the actual fixed point for every real μ; the contract accordingly proves the stronger all-real-μ geometric fact. The original optimization application uses μ>0. Actual BFGS execution, accepted/trial queries and its objective embedding remain supplied by the existing return-map/oracle/run modules. No new algorithmic assumption is introduced here.

## Derived sequence-space regularity

The sequence construction uses the Banach space of actual bounded continuous functions on discrete natural numbers. Each finite-arity power-series coefficient is lifted pointwise as an actual continuous multilinear map. The lifted norm is at most the original coefficient norm, including arity zero. The pinned formal-power-series radius theorem therefore preserves a positive convergence radius. Evaluation by actual continuous linear maps proves that the lifted sum agrees with the original nonlinear remainder at every coordinate of every sequence in a positive-radius ball. This derives analytic superposition rather than assuming it.

Actual derivative uniqueness after each coordinate evaluation proves that a zero derivative of the original remainder yields a zero derivative of its sequence lift. This is a `HasFDerivAt`/`HasStrictFDerivAt` result, not just an equality involving Lean's total `fderiv` convention.

The sequence transformation is an explicit sum of a stable initial-coordinate injection, the two genuine linear recurrences, and the lifted nonlinear terms. Its linear sequence operator has norm at most max(norm A,norm B)<1. The residual map `(a,w) ↦ (a,w-Phi(a,w))` has the actual triangular derivative. The inverse of I-C is constructed with the pinned geometric-series unit, and the actual inverse-function theorem supplies the graph and exact derivative `(I-C)⁻¹ P`, together with local uniqueness.

The analytic regularity order is used deliberately. In the pinned calculus API, a C∞ germ alone does not automatically supply one neighborhood on which all orders hold together. Analytic data give the order-ω inverse and thus a C∞ graph on one actual open neighborhood. The literal return map supplies those analytic data.

## Actual orbit identification, tangency and invariance

The implicit-function solution is initially a bounded sequence. Each graph value is then proved equal to the existing actual vanishing-at-infinity contraction solution by local uniqueness, using radii small enough for both the pointwise series identity and the inverse-function neighborhood. Thus convergence of the selected sequence is derived; no assertion that all bounded sequences converge appears.

For the graph derivative, its unstable components satisfy an actual backward recurrence with the inverse-contracting block B. Boundedness and norm(B)^m→0 force each unstable component to vanish. The chart derivative follows by actual derivative composition. Separately, the actual linear conjugacy proves that the derivative's stable set equals the range of the stable inclusion. Its dimension follows from injectivity of that inclusion, and the chart inverse is the explicit stable projection of `E.symm(x-seed)`.

Small actual convergent orbit uniqueness is derived from the original sequence contraction estimate. The nonlinear Lipschitz radius and contraction constants are obtained from the actual zero derivative of the remainder. Comparing a shifted graph orbit with the graph orbit at its next stable coordinate proves local forward invariance. No orbit-wise uniqueness, recurrence, normal sequence, smooth selection, matrix convergence or manifold hypothesis is supplied as a final input.

## Source inputs and audit

The final source theorem derives its coordinate equivalence and stable/unstable contraction bounds from the already checked literal five-dimensional block derivative and actual shape-polynomial root bounds. The physical scale coordinate is exactly the second stable coordinate, not an assumed transversality statement. The actual local inverse of the return map is independently supplied by the existing `LReturnLocalInverse` module; this construction does not need to assume a diffeomorphism as an extra input.

`verify_stable_manifold.sh` freshly rebuilds all twenty files with the pinned toolchain, prints all ninety actual declaration types and transitive axiom reports, and checks both named source contracts using `Meta.isDefEq` with no added parameters. `source_hashes.json`, `declarations.txt`, `build.log`, `axioms.log`, `contracts.log`, and `validation.log` record the frozen scope. Only propext, Classical.choice and Quot.sound are permitted. The earlier sixteen-file geometric core audit is preserved as `core16_*`; the final release scope includes the four-file local-invariance extension.

## Main integration

The twenty reviewed sources were copied into BfgsVerification with only their owned import prefixes qualified. Delivered reproduction is `bash audit/verify_l_stable_manifold.sh`. Its validator uses the delivered source hashes and reviewed normalized hashes, declarations, actual compiler/axiom reports, and strict target logs. It does not require the excluded scratch directory. The one-time scratch correspondence is recorded separately in l_stable_manifold_scratch_correspondence.log. The central whole-project audit and status register are the root integration task.
