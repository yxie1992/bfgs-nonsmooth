# Actual centered rectangular spectral norm

Integrated into the main library after eighth milestone 01c1511. Original research remains unchanged. The eighth frozen whole-project audit does not include these additions; the new main build and independent importing audit are recorded here.

`CenteredSpectral.matrix` bijectively identifies Vec(m*n) with actual rectangular m-by-n real matrices. Injectivity and surjectivity are proved for all natural dimensions, including zero. `coordinate_pairing_frobenius` proves that the ordinary coordinate dot product used by the full-BFGS model is exactly the matrix Frobenius pairing. Thus the coordinate formalization does not change the algorithm's underlying Euclidean pairing.

`objective` is the actual matrix `Matrix.L2OpNorm` norm from the pinned Mathlib. `objective_operator_norm` explicitly proves equality with the continuous-linear-operator norm between Euclidean spaces. This identifies the intended spectral norm and prevents an accidental entrywise/Pi-norm substitution. It does not assume eigenvalue or singular-vector simplicity, nor assert global differentiability of this norm. A separate equality to a largest-singular-value formula is not required by the source statement and is not independently exported here.

Convexity, positive degree-one homogeneity, nonnegativity and the unique zero are all derived from the actual matrix norm and coordinate map. Compactness of every sublevel follows from the proved finite convex unique-minimum localization theorem. The actual inward supporting error is exactly zero at every actual differentiable point. IR holds on every set, and RS holds on each compact set.

`fullBFGS_convergence` applies to every actual admissible full-BFGS run on this arbitrary rectangular spectral norm centered at zero. It derives value and iterate convergence to zero using homogeneity and the proved bounded zero sublevel. There are no assumed matrix or iterate limits, gradient regularity, rank restrictions or algorithm changes. This does not extend nonzero spectral residual smoothness or the separate general-dimensional nuclear norm identification.

Main build: `radial_continuation_build.log`. Complete importing axiom audit: `CenteredSpectralAudit.lean`, `centered_spectral_axioms.log` and `centered_spectral_validation.log`. All 18 declarations depend only on propext, Classical.choice and Quot.sound. The original scratch source/evidence remains preserved.
