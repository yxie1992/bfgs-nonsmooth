# Module G geometry and pointwise feasibility: statement review

Source reviewed: `BFGS_MASTER_REPORT_LaTeX/report/chapters/G.tex`, G.2–G.4. Original research sources are preserved. This tranche is imported through `BfgsVerification/ModuleGGeometry.lean`. It adds 81 explicit public definitions/theorems: 40 in `CertificateGeometry`, 16 in `PointwiseCertificateFeasibility`, seven in `IncomingPolarGeometry`, and 18 in `AccessibleJumpGeometry`.

## Actual Euclidean ellipsoids and ranges

`CertificateGeometry.euclideanUnitBall` is the actual sum-of-squares ball `sqNorm v<=1`. `euclideanUnitBall_eq` proves that it is exactly the preimage of the closed unit ball in `EuclideanSpace`, not the default finite-Pi unit ball. The latter is used only as an auxiliary compact bounding set in a separately proved inclusion.

`ellipsoid hW` is literally the image of this Euclidean ball by mathlib's PSD matrix square root `hW.sqrt`. Square-root existence and its square identity come from the pinned mathlib theorem; no external spectral computation is used. `ellipsoid_support` proves the literal real supremum of the dot-product image equals `sqrt(metricEnergy W a)`. The upper bound and attainment are also exported. The zero matrix, singular matrices, and dimension zero are all included.

`ellipsoid_visibility_iff` proves the source descent-direction interpretation. `ellipsoid_suppression_iff` proves the source incoming-jump testing interpretation with a sign-exact statement: `energy<=b` iff `0<=b` and all ellipsoid tests are bounded by `sqrt b`. The nonnegative right side is derived on the forward implication, avoiding a hidden assumption that an arbitrary source suppression constant is positive.

`projected_ellipsoid_subset_iff` proves actual image-set inclusion iff the corresponding projected PSD matrix order, for an arbitrary matrix `P`. `step_projected_ellipsoid_subset_iff` is the exact orthogonal step-projector specialization. The converse uses Hahn–Banach separation of the actual compact convex image, together with the proved attained support formula.

`matrixRange_mul_transpose`, `matrixRange_sqrt`, and `projected_matrixRange` prove the intermediate finite-matrix range identities. In particular, the projected PSD matrix range is exactly the projected range of the original PSD matrix. The range arguments use the verified algebraic double-annihilator theorem, with every finite-coordinate functional represented exactly as a dot product.

`range_le_sup_span_of_projected_order` proves the source necessary range inclusion `range Z <= range W + span{s}`. `rankOne_direction_mem_plane` proves the source rank-one consequence. No matrix rank lower bound, invertibility, nonzero step, or continuity of a field is introduced. The projected order here is the source's normalized nonexpansion order; its equivalence to the original existential expansion condition was verified previously.

## Exact extended-real pointwise feasibility

`PointwiseFeasibility.descentCapacity` is the literal supremum in `ENNReal` of the nonnegative absolute dot product over all vectors satisfying all incoming-jump inequalities. It is not a finite real surrogate. `uniformDirections_iff_capacity` proves that its infimum is strictly positive iff there is a uniform positive real visible-direction bound. Complete-lattice suprema and infima retain infinite capacities, empty predecessor types, and empty target types.

`uniformPSD_iff_capacity` proves the source criterion for arbitrary target types and arbitrary dependent incoming types. There is no finite sampling, finite active-set assumption, compactness condition, rank restriction, or regularity hypothesis on the selected field. `rankOne_of_uniformDirections` constructs the explicit rank-one field with suppression constant one. The reverse construction takes an attained support direction of each PSD ellipsoid and scales it; it does not assume that an arbitrary supremum in the incoming-direction set is attained.

The source suppression constant `C` is any real number. The proof enlarges it to `max C 1` using nonnegative curvature, then scales the selected directions. This covers `C=0`, negative `C` where feasibility is vacuous, and empty predecessor families without a separate positivity premise. Pointwise choices use only the standard classical-choice axiom.

The actual source bridge is `visibility_secant_iff_source_capacity`. Its left side is existence of the project's `VisibilitySecantCertificate` with its threshold **equal to** the supplied positive `delta`; its right side is the strictly positive infimum of the actual source capacities. `BandPoint` contains every differentiable point in the exact band. `IncomingPoint` contains every eligible predecessor in that band with the original threshold. Both endpoint gradients are the actual coordinates of `fderiv`; actual derivative uniqueness proves that these are equal to every gradient quantified by `EligiblePair` or the certificate. Extending an indexed field by zero outside its differentiable band reconstructs an actual global matrix-valued field without changing any relevant pair quantifier.

The only scalar assumptions on this bridge are `c2<1` and `delta>0`. They derive positive eligible curvature and provide the original threshold, respectively. The source's stronger ambient convexity, compact-band and line-search assumptions are not needed for the algebraic equivalence. No theorem in this module concludes the transport condition from pointwise selection.

`IncomingPolarGeometry` proves the literal polar statement using mathlib's bilinear `polar` and `closedAbsConvexHull`. The closed absolutely convex hull is built from the full range of normalized jumps `y/sqrt t`. `sourceIncomingPolar_eq_closedHull_polar` specializes this to every actual eligible predecessor and derives the needed strict curvature positivity from weak Wolfe. `incomingPolar_empty` proves the empty-predecessor direction set is all of the ambient vector space.

## G.4 accessibility correction and exact scope

`jumpSpace` is the exact vector span of all differences in an arbitrary family of Euclidean gradient vectors. `common_tangential_projection` proves that every member has the same projection onto its orthogonal complement. `tangent_projection_zero_iff_zero_mem_affineSpan` proves the source affine-hull equivalence. These are exact algebraic statements for arbitrary index types, including infinite families; a chosen index supplies the needed nonempty member without imposing a separate blanket nonemptiness assumption.

`posSemidef_limit`, `suppression_limit_annihilates`, and `visibility_limit` prove the required limiting facts from actual matrix and vector limits. `accessible_jump_annihilated` is an actual certificate/pair theorem: eligibility, band membership, vanishing predicted decrease, vanishing curvature, the limiting jump, and an explicit finite field-value limit are retained. The threshold is derived on a tail from vanishing decrease. No inference of accessibility from mere gradient limits occurs. The optional `...of_continuousAt` wrapper explains one way a full continuous extension supplies the field limit; the main theorem only needs the limit along the accessible family, so it also applies to a continuous extension relative to the source domain.

There is a genuine missing qualification in the source wording at G.tex lines 160–176. It defines `N` using **all** active-gradient differences, then proves annihilation only for **accessible** differences. Consequently the phrase “Visibility then requires a nonzero common tangential gradient” is justified for that full `N` only if the accessible jumps span `N` (or one otherwise establishes annihilation of all its generators). The source later acknowledges that some active jumps cannot be crossed by arbitrarily small pairs satisfying the fixed Wolfe inequality, so accessibility cannot be supplied automatically.

The correction is preserved explicitly:

- `range_orthogonal_to_accessible_jumps` proves the limiting range lies in the orthogonal complement of the span of jumps actually annihilated.
- `visible_accessible_projection_ne_zero` proves a visible gradient has a nonzero projection onto that complement, without any additional spanning assumption.
- `visible_tangent_projection_ne_zero` gives the common full-active-space conclusion **conditionally on** annihilation of all active-gradient differences. That hypothesis is displayed rather than silently inferred from accessibility of some jumps.

`active_accessible_span_countermodel` verifies the algebraic distinction: active vectors 1 and 2 in dimension one, an empty accessible family, and the identity matrix have positive visibility. The full active-difference tangent projection is zero, whereas the accessible-span tangent projection is nonzero. It is explicitly an algebraic scope countermodel, not a claim about actual objective accessibility or a failing BFGS trajectory. An objective-level counterexample to the unqualified wording would require its own fixed-Wolfe accessibility proof and is not asserted here.

The informal references to “suitable partly smooth settings,” the illustrative `u^2+|v|` model, and generic vertices are not relabeled as new general theorems. This tranche verifies the precise linear-algebra and accessible-limit implications stated above; it does not introduce an unspecified partial-smoothness definition or silently infer a full active-stratum accessibility theorem.

## Reproduction

From `bfgs_lean_stage1`, source `scripts/env.sh` and run:

```sh
lake build BfgsVerification.ModuleGGeometry
lake env lean audit/ModuleGGeometryAudit.lean
```

The exact compiler and axiom outputs are `audit/module_g_geometry_build.log` and `audit/module_g_geometry_axioms.log`. The scoped audit enumerates all 81 declarations, including supporting definitions, generic results, actual-pair wrappers, and the algebraic countermodel. Only standard `propext`, `Classical.choice`, and `Quot.sound` dependencies are allowed. No admitted proof, custom mathematical axiom, or unchecked external computation is used.
