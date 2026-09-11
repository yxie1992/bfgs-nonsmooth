# Source R fractional-radius versus norm-scaled convention

Integrated into the main library after eighth milestone 01c1511. Original research remains unchanged. The eighth frozen whole-project audit does not include these additions; the new main build and independent importing audit are recorded here.

`positive_band_radius_lower` derives the literal η/G≤norm₂(x−star) inequality from the actual finite convex supporting inequality and an actual Euclidean gradient bound. `compact_positive_band_radii` derives positive G and R from finite convexity and compactness, so no gradient regularity or extra radius premise is added. It proves η/G≤norm₂(x−star)≤R on every actual differentiable positive-band point. All norms are explicitly `euclideanVector` norms, with actual sum-of-squares identities; the default Pi norm is not silently substituted.

`HasNormScaledInwardBounds` is the source inward error predicate with the explicit additional norm₂(x−star)² factor, the same positive-band quantifiers, and the same inner sample (which may be nondifferentiable). `inward_iff_norm_scaled_on_compact` proves exact equivalence with the original IR predicate. In the forward direction the constant becomes max(M,0)*(G/η)²; in reverse it becomes max(M,0)*R². Taking the maximum handles the source's arbitrary real displayed constants without an added sign assumption. The inward radius theta and its interval constraints are preserved. Empty bands and dimension zero remain included.

The proof only needs finite convexity and compact K, so its implication applies in particular to the source compact-sublevel/minimizer setting. It does not change the objective, algorithm or accepted endpoint assumptions.

Main build: `radial_continuation_build.log`. Complete importing axiom audit: `RadialNormConventionAudit.lean`, `radial_norm_convention_axioms.log` and `radial_norm_convention_validation.log`. All 4 declarations depend only on propext, Classical.choice and Quot.sound. The original scratch source/evidence remains preserved.
