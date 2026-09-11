# Independent review: literal rectangular nuclear norm and R families

Reviewed the six frozen modules in `audit/scratch/nuclear/source_hashes.json` against `R.tex`'s centered gauge, mixed-power, and fused-penalty statements (roughly lines 219–238), and its explicit distinction between centered nuclear penalties and nonzero rank-deficient residuals. Scope: `NuclearGram`, `NuclearVariational`, `NuclearNormFacts`, `CenteredRectangularNuclear`, `FirstDifferencePenalty`, and `RectangularNuclearTargets`.

**Result: no mathematical or statement defect found.** The nuclear norm is the literal finite sum of square roots of eigenvalues of the actual Gram matrix; its norm properties and the ensuing BFGS hypotheses are proved rather than postulated.

## Spectral and norm construction

`gramEigenvalues` uses the actual Hermitian matrix `Aᵀ A` and its standard spectral decomposition. Nonnegativity follows from its PSD property. `rightFrame` is its actual orthogonal eigenvector matrix, so the spectral columns of `A * rightFrame` have squared Euclidean norms equal to the Gram eigenvalues. The rectangular spectral columns are not presumed to form a square orthogonal matrix.

The contraction estimate and all variational target norms use `Matrix.L2OpNorm`, explicitly opened in the source and target modules. `opNorm_le_one_of_gram` translates a checked quadratic Gram bound to the norm of the actual continuous linear map on Euclidean space. This prevents confusion with the default entrywise or Pi matrix norms.

`normalizedColumns = A V diag(σ⁻¹)` is safe when singular values vanish: Lean's inverse of zero is zero, and the proof branches on zero explicitly. Its Gram matrix is diagonal with entries zero or one, from which the contraction bound is proved. `polar = normalizedColumns Vᵀ` remains a contraction. The Frobenius pairing with this actual matrix equals the literal sum of singular values, again with an explicit zero-singular-value case. Thus variational attainment is constructive at the level of the chosen standard spectral data; no full rank or inverse Gram assumption is hidden.

The variational upper bound follows from Cauchy–Schwarz on spectral columns and the Euclidean operator norm. Homogeneity, symmetry, triangle inequality, and definiteness are then derived. In the zero-norm implication, entry squares are bounded by the Frobenius self-pairing, which the variational estimate forces to vanish. Empty row or column dimensions require no exceptional theorem assumption: either the relevant finite sums are empty or the matrix equality follows by extensionality over an empty index type. The theorem also proves equality with the trace of the canonical PSD Gram square root.

## Actual objective and run statements

The rectangular coordinate objective applies this exact function to the already checked bijective matrix-coordinate map. Convexity and degree-one homogeneity are proved from the norm construction. Unique zero and finite convexity yield compact sublevels by the existing verified localization theorem. The homogeneous Module H theorem consequently applies to every actual admissible full-BFGS run and every SPD initialization; value and iterate convergence are conclusions, with no run convergence or matrix hypotheses added.

The inward supporting error is exactly zero by the proved degree-one identity for actual differentiable points. Its target allows `t ≤ 1`, consistent with nonnegative radial scale `1−t`; the source's `0 ≤ t < 1` is included. Compact radial secant bounds are derived by the existing actual inward-to-radial theorem.

The mixed nuclear-power wrapper permits arbitrary finite rectangular dimensions, singular linear maps, arbitrary finite numbers of summands, and exponents `p_j ≥ 1`. Compactness is required only of the full objective's initial sublevel within the local smooth region, as in the source. It makes no false coercivity claim about individual terms. The full objective is convex through the actual-run structure; the smooth summand need only satisfy the stated local C¹,¹ condition, a valid strengthening of the source's convex smooth summand case.

The fused wrapper uses the literal first-difference matrix with `−1,+1` entries, including the one-coordinate zero-row case. A nonnegative weight is absorbed in the actual matrix and the absolute-value equality is proved. The neighborhood threshold is chosen before all admissible runs, at any unique minimizer, with actual compact-basin localization derived. Nonzero scalar residuals are reduced to a fixed signed affine branch on an actual open neighborhood, whereas zero residuals are exactly centered. No residual-identification assumption is made about the iterates.

This tranche makes no claim that a general nuclear norm of a nonzero rank-deficient residual is locally smooth or satisfies the radial condition. It therefore preserves the source's separate spectral obstruction rather than contradicting it. The norm and convergence targets concern real rectangular matrices, matching the report's real finite-dimensional formulation.

## Audit evidence

The frozen snapshot's fresh pinned rebuild, complete 82-declaration transitive-axiom audit, and four strict `Meta.isDefEq` exact-target checks passed. The independent review checks the source statements and their dependence on actual spectral, derivative, and full-BFGS definitions. Final independent name/axiom/hash validation is recorded alongside this review below; all changes in this scope remain outside the frozen main library until the next release permits integration.

Independent validation completed: all 82 requested declaration names exactly match the actual axiom reports; only `propext`, `Classical.choice`, and `Quot.sound` occur. All six recomputed source hashes match the frozen manifest, and all four strict contract results are present without errors.
