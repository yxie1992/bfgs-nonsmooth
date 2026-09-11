# Pinned nuclear-norm infrastructure

Pinned mathlib search found no SVD, singular-value list, Schatten norm, or nuclear-norm implementation. Relevant available source is `Mathlib/LinearAlgebra/Matrix/Spectrum.lean` (Hermitian eigenvector unitary, actual Gram diagonalization), `Mathlib/LinearAlgebra/Matrix/PosDef.lean` (Gram PSD, nonnegative eigenvalues, canonical square root), and `Mathlib/Analysis/CStarAlgebra/Matrix.lean` (actual rectangular Euclidean operator norm and multiplication bounds).

The new implementation avoids an unproved SVD interface: construct the right orthogonal eigenframe V of AᵀA; normalize the mutually orthogonal columns of AV using zero-safe inverse singular values; derive the normalized Gram diagonal of zeros and ones; form the polar contraction Z; prove trace(AᵀZ)=Σσ. Rotating every competing partner by V gives the reverse dual bound column by column. This proves the variational characterization, then the norm properties. The literal equality to trace√(AᵀA) follows from cyclic trace and V's orthogonality.

All matrix/eigenvalue/trace calculations are Lean proofs from the pinned library. No custom norm laws, external eigenvalue calculations, or rank assumptions are introduced. This construction supplies the missing library infrastructure rather than recording it as an unresolved mathematical premise.
