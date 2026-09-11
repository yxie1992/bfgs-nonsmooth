# R rectangular nuclear norm and first-difference families: statement review

Scope: six new files, 82 explicit declarations, four independently named source contracts. The frozen source hashes are in `rectangular_nuclear_source_hashes.json`. This reviewed snapshot is integrated after the tenth release. The scratch backup remains unchanged; main files differ only in import prefixes. Fresh main build/audit logs are separate from the tenth global audit.

## Exact source and representation

The retained source is `BFGS_MASTER_REPORT_LaTeX/report/chapters/R.tex`, lines 219–235 (centered norms, gauges, mixed powers), 236–238 (fused/generalized ℓ1 at nonzero minimizers), and the centered nuclear comparison at the end of lines 274–299. Original research files are unchanged.

`RectangularNuclear.nuclear A` is **defined** as the sum, over every column index, of the nonnegative square roots of the eigenvalues of the actual Gram matrix `Aᵀ*A`. The pinned Hermitian spectral theorem supplies these actual eigenvalues with multiplicity. Rectangular matrices with more columns than rows retain the zero Gram eigenvalues; no pruning, ordering, strict positivity, or full-rank premise is present. Both dimensions may be zero. The checked `nuclear_eq_trace_sqrt` gives equality to the trace of the canonical positive semidefinite Gram square root.

The matrix norm in every partner bound is the scoped `Matrix.L2OpNorm`, identified by pinned mathlib with the actual continuous linear map between Euclidean spaces. It is not a default entrywise/Pi norm. The objective on `Vec (m*n)` uses the existing bijective `CenteredSpectral.matrix` coordinate map. `coordinate_pairing` proves equality of the ordinary BFGS dot product to the exact matrix Frobenius pairing.

## Derived algebra, without norm assumptions

1. `rightFrame` is the actual Gram eigenvector orthogonal matrix. Both orthogonality identities and the Gram diagonalization are derived from the pinned spectral theorem.
2. `normalizedColumns = A*rightFrame*diag(1/singularValues)` uses the total inverse at zero. Its Gram matrix is proved to have diagonal entry zero for a zero singular value and one otherwise. This proves its Euclidean operator contraction, including all zero cases.
3. `polar = normalizedColumns*rightFrameᵀ` is an actual attaining contraction. `pairing_polar` proves its Frobenius pairing is exactly the singular-value sum.
4. The upper variational bound for every partner follows by rotating both actual matrices by `rightFrame`, bounding each column with Euclidean Cauchy–Schwarz and the actual operator norm, and summing. No singular-value perturbation theorem or numerical computation is used.
5. Triangle, real absolute homogeneity, and zero iff the matrix is zero follow from that variational theorem. Only then is `nuclearSeminorm` bundled using `Seminorm.of`. Convexity and continuity infrastructure therefore do not assume the desired norm properties.

The norm target includes the literal singular-value identity, trace-square-root identity, all-contraction upper bound, actual attainment, nondegeneracy, every real scalar, and every matrix sum. Thus compilation cannot silently replace the requested model with an abstract seminorm hypothesis.

## Actual-run conclusions and quantifiers

`fullBFGS_convergence` has only an actual `AdmissibleBFGSRun (m*n) objective` parameter. Convexity, a zero global minimizer, uniqueness, and compact sublevels are proved for the concrete nuclear objective. The existing verified Module H/M chain supplies objective-value and iterate convergence. There are no final hierarchy, metric convergence, iterate convergence, bounded-gradient, singular-vector continuity, or chosen-direction premises.

`inward_error_zero` proves the exact supporting-error equality for every actual derivative and every `t ≤ 1`; it does not assume differentiability at the inner point. `radial_bounds` then supplies the source RS condition on every compact set. The centered target explicitly retains the actual derivative equality and compact-set RS conclusion.

`mixed_nuclear_powers_radial` and `mixed_nuclear_powers_convergence` instantiate the source finite family using actual rectangular nuclear objectives and actual linear maps, with possibly different dimensions and every real exponent at least one. Compactness is required only for the full objective's initial sublevel, as in the source. The actual-run conclusion includes Euclidean distance to the whole minimizer set; uniqueness is required only for convergence to a specified minimizer. Individual terms/maps may have null directions and need not be coercive. A `Fin r` exact target is provided; the underlying declarations cover any finite index type.

## Named first-difference example and source scalar decomposition

`FirstDifference.differenceMatrix n` has exactly -1 on its diagonal and +1 immediately above it. Its actual action is proved to be `x(i+1)-x(i)`. The weighted penalty is literally `weight*Σ|x(i+1)-x(i)|`, with `weight≥0`; its identity with the matrix ℓ1 penalty is proved. Length one and weight zero are included. Translation by an arbitrary constant vector leaves this penalty unchanged, so no standalone coercivity or false unique-minimizer claim is introduced.

`local_fullBFGS` applies to the actual smooth-loss-plus-first-difference objective at any unique global minimizer, with merely local C1,1 loss and full-objective convexity. It derives a positive basin **before** quantifying over every admissible run, retains all-iterate membership in the stated open neighborhood, and derives values and iterates converging. It assumes no difference-matrix rank, nonzero residual, or zero minimizer.

The two auxiliary scalar-residual declarations prove exactly the source explanation: a residual zero at the minimizer becomes a centered absolute value after translation, and a nonzero residual equals one affine branch on an actual open neighborhood. They do not use an iteration sequence.

## Validation and remaining scope

The reproducible main command is `bash audit/verify_rectangular_nuclear.sh`. The development scratch command was `bash audit/scratch/nuclear/verify_nuclear.sh`; it is not needed for delivered reproduction. It compiles the six actual files in dependency order using the pinned environment, prints every explicit declaration's transitive axioms, checks all four theorem types with strict `Meta.isDefEq`, and validates the frozen hashes. The checker is structural/log-only; it performs no mathematical evaluation. Actual outcomes are recorded in `rectangular_nuclear_build.log`, `rectangular_nuclear_axioms.log`, `rectangular_nuclear_contracts.log`, and `rectangular_nuclear_validation.log`.

Independent review passed with no defects: `audit/RECTANGULAR_NUCLEAR_PEER_REVIEW.md`. It independently matched all 82 declarations, six frozen scratch hashes, standard transitive axiom reports and four strict contracts. The reviewed snapshot manifest is copied to `audit/rectangular_nuclear_reviewed_source_hashes.json`. The main validator hashes each main source after normalizing only import prefixes and compares it with that delivered manifest; it requires no scratch directory. The one-time original-file correspondence check is retained in `audit/rectangular_nuclear_scratch_correspondence.log`. Root imports and the next whole-project audit remain parent responsibilities.

This tranche closes the R general rectangular nuclear-model identification and the named first-difference export. It does not resolve the separate historical four-piece optimizer attribution `(-1,5),25/4`; it does not assert smoothness of arbitrary nuclear residuals near arbitrary nonzero low-rank matrices, and it does not alter the already verified nonzero-centered nuclear RS counterexample.
