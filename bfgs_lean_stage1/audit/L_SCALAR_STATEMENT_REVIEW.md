# L scalar regularity and exact affine neighborhoods

Main integrated scope: 14 Lean modules, 203 explicit declarations, five exact target types. The original `L.tex` is unchanged. This tranche verifies the literal smooth scalar construction at lines 236–279 and the requested explicit nonvanishing curvature peaks. The countably affine step-ramp variant at line 358 is a separate subsequent obligation.

## Literal ramp and scalar definition

The code uses exactly r=1/128, epsilon=1/1024 and center=(1-(1+r)/b)/(1-r). The parameter interval is the **closed** 17/10≤b≤34; this is stronger than the strict source range and contains both certified seed values. Every division used in the proofs has its positive denominator derived from these bounds or from the positive geometric scale.

`LScalarRamp.ramp` reuses the already checked cubic unit ramp 3t²−2t³ through the literal new affine coordinate. Its zero, transition and one pieces are explicit and proved. The actual derivative is bounded between zero and 768. Its primitive is defined by the corresponding quartic and affine pieces, and the fundamental theorem of calculus proves equality to the actual interval integral from zero for every real argument. Thus the source's J is not an assumed primitive. Its integral on [0,1] is exactly 1-center.

The two plateau lengths have proved exact formulas 129/128−1151b/131072 and 130945b/1024−129, and both exceed one half throughout the closed parameter interval. Transition endpoints lie strictly inside (0,1).

The positive scalar function is an actual infinite sum of ramp primitives with coefficients b a_n²(1-r)². Absolute convergence is proved from a summable first-derivative majorant, and the compiler checks equality with **every** literal closed positive interval formula

(r a_n)² + b a_n²(1-r)[r xi +(1-r)J(xi)].

The proof evaluates all later affine tails by actual geometric infinite-sum identities; earlier terms are exactly zero. It proves the outer value 1+x−b for every x≥b. Adding the explicit negative piece x²/2 for x≤0 gives the complete source function, with value zero at zero. No selected interval, assumed sum convergence or unchecked numerical evaluation is used.

## Actual regularity and curvature

The first derivative is the actual uniformly convergent series of slope components. Its continuity follows from a summable norm majorant. Consequently the function is globally C1, including the accumulation point zero. Each positive point has a neighborhood where the infinite slope series reduces to a finite sum plus a constant tail, and the value series to a finite sum plus an affine tail. This proves actual C2 regularity everywhere on (0,infinity), including interval nodes and the positive outer join. The negative side is the literal quadratic and is C2 there.

Curvature components have disjoint active transition intervals. Their pointwise infinite sum has at most one nonzero term and is bounded by 768/b. This series is **not** asserted to be a globally continuous derivative of the slope: its value at zero is only a defined sum, and the actual second derivative at zero is proved not to exist. Actual differentiation of the slope series is justified locally at strictly positive points by its finite-tail identity.

Each finite partial slope sum has actual derivative between zero and 768/b, so the mean value theorem gives a common Lipschitz constant. Passing to the actual pointwise sum gives global Lipschitz regularity of the positive slope. The explicit negative slope is 1-Lipschitz. Their sum is Lipschitz with the sufficient constant 1+768/b, proving the source's global C1,1 claim. The **sharper source second-derivative bound** max{1,768/b} is separately proved for every actual second derivative; it is not replaced by the larger Lipschitz witness.

The complete function is proved convex, nonnegative, coercive at both infinities and on the cocompact filter, and uniquely minimized at zero. Positive-side O(x²) and O(x) bounds for the value and first derivative are also exported.

## Exact nodes, plateaus and failure at zero

At each positive node b a_n, the actual value is a_n², its actual first derivative is a_n, and its actual second derivative is zero. The affine formula a_n²+a_n h holds for the entire **closed** neighborhood |h|≤a_n/2, including the outer node n=0. Actual derivative equality throughout the open plateau is derived from local equality, not assumed as an endpoint oracle.

The two source positive sequences b a_n and (b+1/4)a_n both converge to zero through nonzero positive values. Their actual derivative ratios are exactly 1/b and 1/(b+1/4). These distinct limits contradict any actual derivative of the first derivative at zero. The exported conclusion is `not DifferentiableAt (deriv phi) 0`, not merely a total Lean `deriv` equality. This resolves the exact intended C1,1-versus-C2 distinction on the positive side itself.

The explicit peak sequence b a_n[r+(1-r)center] lies strictly inside each positive interval and tends to zero. At every peak, the actual second derivative exists and equals the fixed positive value 768/b. The curvature peak sequence is proved not to tend to zero. No iterate, matrix, hierarchy, metric-convergence or accepted-pair premise occurs in this scalar infrastructure.

## Validation and boundaries

Reproduce the delivered main snapshot with `bash audit/verify_l_scalar.sh`. The script compiles all 14 modules in dependency order with the pinned toolchain, prints the transitive axiom dependencies of all 203 explicit declarations, and checks the five exact target types using strict `Meta.isDefEq`. The checker is structural and log-only; it performs no mathematical computation. Source hashes, declaration inventory, compiler/axiom/contract logs and the validation result are under `audit/l_scalar_*` and `audit/L_SCALAR_*`.

Exact targets: `lScalarRamp`, `lScalarDefinition`, `lScalarRegularity`, `lScalarNodes`, `lScalarPeaks`, in namespace BfgsVerification. This scalar tranche is not the multidimensional L embedding or its local-copy BFGS oracle: those are separate root-owned tasks. No original research source correction was needed. Main integration follows the eleventh release. The delivered reproduction script and both source manifests are self-contained and require no scratch files.

Independent review subsequently passed with no defects: `audit/L_SCALAR_PEER_REVIEW.md`. The reviewer read all 14 files/203 declarations against the source, independently matched all hashes and standard-axiom report names, and reran the five strict target contracts. Evidence: `audit/l_scalar_peer_validation.log` and `audit/l_scalar_peer_contracts.log`. The scoped full run also passed in `validation.log`; no source bytes changed after freezing.
