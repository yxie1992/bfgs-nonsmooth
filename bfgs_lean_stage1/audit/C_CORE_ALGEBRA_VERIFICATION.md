# C: angular, active-family, and actual energy infrastructure

Main imports: `BfgsVerification.PlanarTransportAlgebra`, `BfgsVerification.PlanarActiveGeometry`, and `BfgsVerification.ScalarTransportEnergy`. All three passed the pinned main build. `C_PlanarAlgebraAxiomChecks.lean` checks all 30 explicit declarations; `planar_algebra_full_build.log` and `planar_algebra_axioms.log` record compiler and standard-only transitive axiom evidence.

`PlanarTransportAlgebra` proves the actual trigonometric unit normal and tangent identities, reconstruction of any vector, the corner frame formula, visibility pairing, scalar derivatives, and the angular derivative `(h+h'')T`. It also proves the determinant-ratio representation and positivity when the endpoint determinants have equal sign. These are equalities for actual coordinates and derivatives.

The determinant identity explicitly corrects the printed source's orientation. For `n=(cos θ,sin θ)` and `T=(-sin θ,cos θ)`, `det(T,n)=-1`. Thus, in the ordered basis `(T,n)`, a triangular derivative with columns `(a,0)` and `(b,e)` gives

`det(s,Dw s) = s_n ((a-e)s_T + b s_n)`.

The displayed source has the opposite sign. Absolute-value estimates and all subsequent transport conclusions are unchanged. The original source is preserved; this is a documented mathematical correction.

`PlanarActiveGeometry` identifies Euclidean and coordinate affine criticality, proves that a noncritical affinely independent planar family has at most two members, shows that distinct dependent planar gradients have an affine line through zero, and constructs the exact common-rate vector through the actual inverse gradient matrix. The local C2 chart construction is not claimed here.

`ScalarTransportEnergy` derives C's exact scalar energy identity from the actual full-BFGS Hessian update and its annihilated step. It proves a finite linear reciprocal-sum bound under summable multiplicative drift, then uses only M's qualitative reciprocal-average divergence for the contradiction. The source logarithmic bound gives an explicit square multiplier constant once `d≤1`. The final compact-run tail criterion derives bounded gradients, summable decreases, the sufficiently late threshold, and this multiplier estimate from the objective/run hypotheses; it does not assume a matrix or iterate limit.

The endpoint transport, visibility, and secant estimates remain explicit hypotheses in these intermediate criteria. They must still be derived by constructing the joined field near the whole hypothetical cluster set from C's objective-level regularity and strict contours. No theorem in this tranche claims that construction or the forced affine-critical cluster theorem is complete.

Shared `ClusterSetGeometry` is separately main-built and audited for all eight declarations (`ClusterSetAxiomChecks.lean`, `cluster_set_geometry_full_build.log`, `cluster_set_geometry_axioms.log`). It derives compactness/nonemptiness, eventual trapping in every open neighborhood of the whole cluster set, distance convergence, and the positive common limiting level under absence of an affine-critical cluster. It makes no singleton or connectedness assumption.
