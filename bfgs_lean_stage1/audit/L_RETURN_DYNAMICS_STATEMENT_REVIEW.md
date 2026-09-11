# L return derivative, spectral certificate, and actual normalized dynamics

The actual main-library aggregate build passed for all 17 modules. The separate scoped audit records all 147 explicit declarations and three generated Jet declarations, their actual types, transitive axiom dependencies, and source hashes. This is a scoped result; the whole-report status is maintained separately by the root audit.

## Actual derivative chain

LReturnJets proves ordinary scalar derivative rules for a pair of a value and its derivative. The vector/matrix helpers are literal two-coordinate sums and products, and inverseUpdate is the actual full inverse-BFGS formula. Its derivative rule requires the actual curvature to be nonzero; LShapeDerivative discharges this at the seed using the already checked full-BFGS seed matrices and curvatures. The shape derivative is identified with the actual Frechet derivative of the five-dimensional return map by chain rules and derivative uniqueness. LShapeMapDifferentiability also exports the actual two-dimensional shape-map derivative directly.

LReturnParameter proves a literal global semiconjugacy under scaling only the last state coordinate by mu. Differentiating that equality proves that all four-by-four horizontal derivative entries are independent of mu and that the top four entries of the last column are mu times their values at mu=1. LReturnParameterBlock packages precisely the source's fixed C/a/b blocks and factors of mu. This is derived from the actual map; no claimed Jacobian oracle is assumed.

## Checked numerical-candidate mechanism

The candidate generator is an ordinary Python program using exact fractions to propose interval endpoints. It is not trusted by Lean. The revised certificate attaches bounds to explicit LReturnJets operations and proves each real addition, multiplication, negation and reciprocal bound by ordinary theorems and norm_num. Each denominator interval is separated from zero before a reciprocal inequality is applied. The shared Jet nodes are then identified with each actual derivative-update recurrence and each final Jacobian entry. The complete generated certificate compiled in the main library, including the exact linkage between every shared Jet node and the actual derivative recurrence. The generator's interpretation of the actual derivative operations is therefore kernel checked. A failed earlier global expression expansion is not counted as evidence.

The verified exact enclosures are J00 in [1.1123986249,1.1123986253], J01 in [0.6459701025,0.6459701029], J10 in [0.7515015701,0.7515015708], and J11 in [0.4905136882,0.4905136890]. These certify the source's four strict characteristic-polynomial signs and its exact eigenvalue intervals. They do not assert that every digit in the source's illustrative fifteen-place decimal matrix is correctly rounded. The input box is explicitly derived from the actual algebraic root ball.

## Spectral and local-inverse scope

LShapeSpectralAlgebra proves the two real roots by the intermediate value theorem and proves the complete quadratic factorization. The exact-diagonalization helper constructs the actual change of coordinates from the source block form and root inequalities; the scale coordinate is exactly the second stable coordinate. Its characteristic-polynomial theorem is for the actual LinearMap.charpoly, obtained by invariance under conjugacy and the characteristic polynomial of actual diagonal maps. It therefore preserves the repeated alpha eigenvalue as a squared factor. This is stronger evidence than a list of numerically estimated eigenvalues.

LBlockInvertibility proves actual injectivity of the block derivative from its three nonzero diagonal determinants, builds a continuous linear equivalence, and applies the actual inverse-function theorem. The source-specific wrapper supplies its determinant sign from the certified shape roots and uses the actual analytic map. Its two inverse identities hold on actual neighborhoods.

## Orbit-existence replacement

LReturnOrbitCore applies the constructive complete-C0-space contraction theorem only after deriving the actual block form and actual strict Frechet derivative. LReturnStableOrbit discharges every spectral premise with the interval certificate, derives an actual normalized orbit in any prescribed neighborhood, and intersects that neighborhood with the actual deterministic-oracle neighborhood. Positive scale at every iterate follows from the literal tau-next=tau*r equation and r>0. No stable orbit, iterate convergence, matrix convergence, matrix limit, or invariant manifold is inserted as an assumption.

The constructive orbit theorem proves the trajectory existence needed by L's global failure theorem. It does not itself prove the source's stronger assertion of a smooth two-dimensional stable manifold tangent to the stable eigenspace. That auxiliary manifold statement remains a separate obligation unless further established. The physical-run transfer is independently reviewed in scratch/l_run/INDEPENDENT_PEER_REVIEW.md. The original research source is unchanged.

## Actual global failure target

LGlobalFailure.actual_global_failure quantifies over every positive mu, actual admissible parameters 0<c1<=1/3 and c1<c2<1, and every neighborhood U of physical zero. It constructs an actual AdmissibleBFGSRun for the literal Q_mu. The statement includes points, matrices and objective values tending to zero; strictly positive and strictly decreasing accepted values; the exact periodic accepted lengths; the complete fuel-five deterministic bracket-search results and histories at every iteration; differentiability and positive values at every compatible accepted or rejected query; containment of all these points in U; convergence to zero of every time-varying compatible query selection; strict Armijo and weak-Wolfe comparisons; and nonstationarity of the origin. No orbit, recurrence, derivative oracle, matrix convergence or spectral assertion is assumed in this final theorem.

LGlobalFailure.source_global_failure specializes to the literal source parameters (1/10000,1/2). The actual objective geometry and explicit negative minimum are separately exported by LQuadraticSeed.quadratic_seed_contract. The actual normalized-state witness and the exact phase formulas remain accessible through actual_orbit_data and LFlatten.Data.phase_parameters. The final import is BfgsVerification.LGlobalVerification.

## Source coverage and exact qualifications

- L.tex return-map agreement and the source shape derivative/Jacobian block: actual maps, actual derivatives, actual branch decisions and the mu dependence are verified.
- The four rational sign tests and eigenvalue intervals: verified by exact kernel arithmetic and the intermediate value theorem. The literal display to fifteen decimal places is illustrative; correct rounding of each of those extra digits is not asserted.
- The full characteristic polynomial, including the repeated rho-inverse eigenvalue: verified for the actual LinearMap.charpoly. The actual real diagonalization and a rho eigenvector with last coordinate one are exported. Nonzero spectrum and absence of complex unit-circle roots are explicit.
- The local diffeomorphism assertion: verified as an actual smooth local inverse with both inverse identities on neighborhoods.
- The actual global counterexample and small-physical-orbit property: verified by the constructive C0 contraction orbit proof and exact full-run/search conversion.
- The source's smooth two-dimensional stable-manifold regularity and tangency assertion remains open as an auxiliary assertion. The verified theorem uses a different proof of the needed actual orbit existence.

The reproducible command is `bash audit/verify_l_return_dynamics.sh`. Its generator check verifies byte-identical regeneration; the compiler, not Python, checks all mathematical certificate steps. Older abandoned scratch approaches and their logs are not imported, counted, or used as evidence.
