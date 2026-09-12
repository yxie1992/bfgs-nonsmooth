# Revision-scope review

**All 31 theorem/lemma/proposition/corollary/definition environments are byte-identical to commit `dbe14e9aacacd72d84a4bd9a457bb503e1aee4bc`.** I independently extracted and compared the actual blocks in all 19 paper TeX files, and read the actual eight-file diff; this result is not inferred from the existing preservation JSON. Individual block and file hashes are recorded in the companion JSON.

No mathematical error or hypothesis loss was found in the revisions. One literal formal-correspondence gap, already present in the unchanged lower theorem statement, has been closed with a separately authorized, compiled and audited supplement.

## Determinant

`paper/sections/local.tex:341-354`: **Correct clarification.** For augmented gradient columns (1+2u,v,1), (u,1+3v,1), (-1+3u,-1+2v,1), subtracting the third column gives determinant (2-u)(2+v)-(1-2u)(1-v)=3(1+v-uv). The prior coefficient and basin proof is unchanged.

Actual source support:

- `bfgs_lean_stage1/BfgsVerification/PlanarQuadraticCoefficients.lean:64 (gradient_affineIndependent; uses the same determinant identity)`
- `bfgs_lean_stage1/BfgsVerification/PlanarQuadraticConvergence.lean:63 (fullBFGS_explicit_basin)`

## Physical preimages

`paper/appendices/lower_curvature.tex:151-179`: **Correct quantifier clarification.** All phase and candidate maps are continuous at the zero-scale normalized seed and vanish there. Their finite preimage intersection is a neighborhood of the seed even when prescribed V is merely a neighborhood, and a local stable orbit can be chosen inside it. The forward-orbit containment is constructed after choosing the neighborhood, not presumed for an arbitrary stable point.

Actual source support:

- `bfgs_lean_stage1/BfgsVerification/LFlattenNeighborhood.lean:12 (physical_neighborhood; all three physical phases and all nine queries)`
- `bfgs_lean_stage1/BfgsVerification/LReturnStableOrbit.lean:29 (source_oracle_orbit)`
- `bfgs_lean_stage1/BfgsVerification/LGlobalFailure.lean:11 (actual_orbit_data)`
- `bfgs_lean_stage1/BfgsVerification/LGlobalFailure.lean:27 (actual_global_failure)`

The finite map family should be read as including phase points as well as the nine trial candidates, matching physical_neighborhood. The separate physical-iterate argument already covers the phases.

## Branch restriction

`paper/appendices/lower_curvature.tex:250-254`: **Mathematically correct; the literal branch export is now compiled and audited.** b_i=q_i·c_*>17/10 implies q_i is nonzero; v_i=c_*/b_i gives q_i·v_i=1. Then f_i(tv_i)-mu*t^2*||v_i||^2/2=psi_bi(t). Differentiability at zero of the branch derivative would transfer to differentiability of psi_bi prime, contradicting the two unequal node limits. Invertible precomposition preserves the fderiv-based second-differentiability convention.

Actual source support:

- `bfgs_lean_stage1/BfgsVerification/LEmbeddingObjective.lean:44 (parameter_bounds), :55 (residualBranch_old)`
- `bfgs_lean_stage1/BfgsVerification/LScalarRegularity.lean:102 (phi_not_twice_differentiable_zero)`
- `bfgs_lean_stage1/BfgsVerification/LEmbeddingRegularity.lean:69 (branch_hasGradient)`
- `bfgs_lean_stage1/BfgsVerification/AffineWhiteningHessian.lean:68 (second_differentiableAt_iff)`

LWhitening.SmoothLocalFailureTarget does not itself contain this branch-specific negative regularity clause. Root authorized a new isolated supplement to close that literal export gap without modifying original Lean.

## Trims

`paper/sections/global.tex; failure.tex; introduction.tex; verification.tex`: **No hypothesis loss or stronger conclusion found.** Removed global prose repeats the still-present admissibility definition and introduction caveat. Failure conclusions and surviving questions are consolidated in verification: the fixed implementation, separate parameter ranges, absence of positive-measure assertions, and open strongly convex C2 local class remain. The introduction now states bounded gradients and predicted decreases tending to zero for reciprocal divergence. Formal-foundation and human-review limitations remain explicit. The theorem statements and essential proof calculations are unchanged.

## Other diffs

`paper/appendices/planar_geometry.tex; seed_certificate.tex; named proof headers`: **No mathematical effect.** Two reference sentences are rephrased and redundant Proof of text is removed from proof headings. No equations, lemma hypotheses or proof steps are removed.

## Limits

This is a source-level review of the changes. It does not claim a build, visual PDF inspection, or fresh axiom audit. The new stable-manifold reference locators were not reopened online in this bounded review; the actual mathematical application was checked against the existing formal invariant-manifold and oracle-neighborhood contracts. No TeX or original Lean source was edited. The isolated branch supplement has separate compiler/dependency evidence; it does not constitute a fresh rebuild of the original library.

## Resolved literal branch contract

The separate `branch_formal/runs/branch_regularity_01/SUMMARY.json` records a successful pinned Lean 4.19.0 compile and full structural audit: **3 module-owned theorem declarations, 37,525 reachable checked declarations, and only `propext`, `Classical.choice`, `Quot.sound`**. Exact kernel-root type/value agreement and per-root ordinary collector agreement passed. All 761 frozen original audit inputs were checked unchanged. Original library objects were reused; no fresh original-library rebuild is claimed.

The canonical combined endpoint is `ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction`, whose exact audited signature is:

```lean
BfgsVerification.LWhitening.SmoothLocalFailureTarget ∧
  ∀ (i : Fin 3), ¬DifferentiableAt ℝ (fderiv ℝ (BfgsVerification.LWhitening.smoothBranch i.castSucc)) 0
```

The two other exports prove the actual original and whitened branch obstructions separately. The derivative convention is differentiability of the Fréchet derivative at zero, with the original branches already globally continuously differentiable. There are no added mathematical assumptions. The model-assisted peer review also independently checked the restriction and whitening argument and found no semantic concern; this is not an external human-review claim.
