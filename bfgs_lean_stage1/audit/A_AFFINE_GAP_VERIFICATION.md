# Module A compact affine-gap closure

This six-file tranche proves the retained paragraph beginning “There is also local lower semicontinuity of γ” in `report/chapters/affine_geometry.tex`, and connects it to the already verified actual finite-max barycentric-stability theorem. It contains 31 explicit declarations and one exact original-objective target. Pinned clean rebuild, complete actual types/transitive axioms, strict exact-target check, and all six frozen hashes pass in `validation.log`. All six files are now integrated into the main library with the additional main validation recorded below.

## Actual affine distance and the formula

`objectiveDistance F p` is literally the Euclidean distance from zero to the affine hull of the actual supporting-vector subdifferential. `subfamilyDistance` similarly uses actual affine hulls of finite indexed gradient images. Neither is an arbitrary scalar proxy.

For a nonempty affinely independent finite family, let A have columns `(1,g_i)`, K=AᵀA, v=K⁻¹1, and d=Σv_i. The source places the weight row last; this harmless row permutation leaves the Gram matrix unchanged. The implementation proves K positive definite from actual affine independence and d positive using K⁻¹ positive definite. The normalized weights w=v/d sum to one. The explicit affine point a=Σw_i g_i satisfies `g_i·a=d⁻¹−1` for every i. Since a is in the affine hull, the common pairing equals ‖a‖²; the previously proved minimum-norm characterization therefore identifies a with the actual closest affine point. All statements cover singleton families without a separate difference-Gram convention.

Continuity of A, K, K⁻¹, d⁻¹, and a is proved at every independent family. Local full rank is derived from the continuous nonzero determinant; it is not assumed in a neighborhood. This gives continuity of the actual affine distance for every nonempty fixed subfamily.

## Active sets and lower semicontinuity

For a finite local maximum, originally inactive indices remain inactive nearby by their actual value gaps and continuity. The finite set of possible active subfamilies may shrink. At the base point, the affine hull of each nonempty subfamily is contained in the full active affine hull, so its distance is at least the actual gap. Fixed-subfamily continuity yields the lower estimate for each possibility, and a finite intersection of these neighborhoods yields lower semicontinuity. The proof never chooses a convergent active-set subsequence or assumes an active set eventually stays fixed.

`objectiveDistance_lowerSemicontinuousAt` uses the exact proved equality of the actual subdifferential with the convex hull of active actual branch gradients. Its generic actual-gradient interface requires genuine `HasFDerivAt` statements nearby, pointwise gradient continuity, and independence at the base point; these are discharged in the final C¹ source wrapper.

## Compact positive bands and final source target

A nonnegative lower semicontinuous function on a nonempty compact set attains its minimum: the proof constructs a closed epigraph truncated between zero and the value at a fixed point, uses compactness of the actual product set, and minimizes the continuous height coordinate. The affine distance is nonnegative and vanishes exactly at affine-critical points. Local affine-critical correctness therefore turns every compact strictly positive objective band into an attained strictly positive affine-distance minimum.

`finiteC1MaxAffineGap : FiniteC1MaxAffineGapTarget` assumes the finite convex objective is locally the finite maximum of C¹ branches on an open neighborhood. Only the originally active actual gradients need be affinely independent and carry strictly positive weights summing to one with weighted gradient zero. Originally inactive branches are removed by the proved local representation reduction. The wrapper derives the actual gradients and their local continuity from C¹ regularity, then derives local rank persistence, local correctness, lower semicontinuity, and every compact-band conclusion. There is no assumed gap, visibility constant, gradient alphabet, or sequence/matrix convergence. Individual branch convexity is not needed by this stronger theorem; the report's convex-branch hypotheses instantiate it directly.

The band quantifiers are: one open neighborhood V around the base point first; then **every** nonempty compact K⊆V with F(base)<F(p) throughout K; then an actual point p∈K at which the positive minimum is attained. A compact positive objective band in the source is a special case. Empty K are excluded only from attainment, as they must be.

## Limits of this completion

This establishes geometric visibility, not an arbitrary-dimensional full-BFGS transport theorem. It does not change the separate rank-loss counterexample, does not assert global lower semicontinuity under pointwise affine correctness, and does not prove the source's semialgebraic finite-critical-value proposition. The final general-dimensional convergence statement explicitly labelled a conjecture remains a conjecture. Existing research sources have not been edited.

## Main integration verification

PASS: actual main pinned Lake build; 6 modules/31 explicit declarations; complete actual type and standard transitive-axiom reports; 1 strict exact-target checks; all 6 frozen main hashes unchanged; main proof text equals clean-rebuilt scratch except import prefixes.

Main evidence: `audit/a_affine_gap_declarations.json`, `a_affine_gap_axioms.log`, `a_affine_gap_contracts.log`, `a_affine_gap_validation.log`, and shared `audit/affine_gap_finite_max_build.log`. This is a post-tenth-release scoped integration, not a replacement of the released whole-project register.

Delivered-source reproduction is now available as `bash audit/verify_affine_gap_finite_max.sh`, with `audit/validate_affine_gap_finite_max.py`. Both depend only on the delivered main sources, manifests and audit drivers; no scratch source or scratch olean is required. The fresh rerun passed all main source hashes, declaration/standard-axiom checks and strict targets.
