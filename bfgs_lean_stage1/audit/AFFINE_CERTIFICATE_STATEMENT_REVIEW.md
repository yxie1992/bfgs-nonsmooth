# Affine certificate covariance: independent statement review

Reviewed `AffineCertificateAlgebra.lean`, `AffineCertificates.lean`, and `AffineCovariance.lean` against the affine-covariance paragraph of Module T. No mathematical gap or strengthened field-regularity hypothesis was found.

The coordinate convention is explicit: the new point is `A*x+b`, the new objective is `F(A^-1*(z-b))`, and the new field is `A*W(A^-1*(z-b))*Aᵀ`. `A.det != 0` is exactly the source invertibility condition. The affine inverse identities are proved, not assumed. The result does not require `A` to be orthogonal or preserve the Euclidean norm.

`transformed_gradient` and `original_gradient` use actual `HasFDerivAt` chain rules. Gradients transform by `A^-T`, and the reverse derivative transforms by `Aᵀ`. The PSD-domain proof obtains a true coordinate derivative from `DifferentiableAt`; it does not assume the existence of an externally assigned gradient oracle.

Predicted decrease, objective difference, and curvature product are preserved exactly. `eligible_pair_affine_iff` retains all differentiability and acceptance comparisons in both directions. `transformed_band_iff` is an equivalence for the exact image domain, with unchanged objective gap and minimum-value reference. Thus the transport and suppression quantifiers still cover every eligible pair in the band satisfying the original decrease threshold.

Field PSD follows by congruence. All tested scalar energies are preserved exactly. Projected transport is handled through its verified perpendicular-quadratic characterization: testing the new inequality at `a` corresponds to the old inequality at `Aᵀ*a`, and the inverse transpose supplies the reverse direction. This is the correct argument for a general affine coordinate change; the proof does not equate Euclidean projectors across different coordinates.

`transform_constants` confirms the same `m`, `C`, `L`, and `delta`, including arbitrary real suppression constant `C`. No boundedness or continuity of the certificate field is used. Translations are included in the domain and objective, and disappear correctly from the step differences.

`hasBandCertificates_affine_iff` proves both directions by the actual inverse affine map. The auxiliary `twice_objective` and `twice_domain` theorems prove recovery of the original objective and domain; reverse existence is not assumed. Convexity, compactness, and attainment of a minimum are separately preserved, where relevant, by the verified wrappers.

The certificate covariance statements are more general than the source ambient setting because their algebra does not need convexity, compactness, or a minimizer as additional premises. This does not weaken the source claim. They remain statements about the complete objective-pair certificate, not an assertion that arbitrary chosen finite predecessors belong to a common BFGS trajectory.

Dimension zero and empty domains are admitted without exceptional mathematical assumptions. They cause no inverse issue for an invertible zero-dimensional matrix and no hidden nonempty-band premise in the all-band existence equivalence.
