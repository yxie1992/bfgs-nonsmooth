# Independent review of the actual Module D embedding

Reviewed the complete `report/chapters/D.tex`, all ten main modules frozen in `audit/d_embedding_declarations.json` (74 declarations), and the actual objective module frozen in `audit/d_embedding_objective_declarations.json` (54 declarations). Also inspected the exact two D targets/wrappers in `ReportEmbeddingTargets.lean` / `ReportEmbeddingEndToEnd.lean`, the underlying deterministic search definition, simultaneous secant-pair scaling identity, and source trial indexing. This is a bounded review of the embedding closure, building on the earlier algebraic root, finite-cycle, scalar-construction, and deterministic-seed audits; it does not assert completion of Module L's separate perturbed orbit.

**Result: no statement or proof defect found.** The generic transfer structures are completely instantiated from the fixed literal objective's actual plateau values and actual derivatives. They are not assumptions in either final D target.

## Source and quantifiers

- `DEmbedding.objective` is precisely the same four-piece function for every scale index and every allowed pair of line-search parameters: the first three pieces are `phi 2 u`, `phi 2 (-u-v/8)`, and `phi bStar (seedC*u+seedD*v)`, and the fourth is `v`. The literal formula is separately proved. The exact algebraic seed enters through the already verified root, not a floating-point replacement.
- `ObjectiveGeometryTarget` proves four globally convex actual `C²` branches, compact sublevels, unique minimum zero at the origin, and nondifferentiability there. Its Hessian is the matrix of the actual second Fréchet derivative. Both PSD inequalities are explicit with common upper bound `64 I`; the Euclidean operator-norm Lipschitz bound `60000` is also proved. The one-sided directional derivative at zero is the source `max 0 h₂`.
- `EmbeddingFailureTarget` fixes `center n = (1/16)^n • (2,-32)` and starting point `center n + ((1/16)^n)^2 • z₀`. Its universal parameter block is exactly `0 < c₁ ≤ 1/3` and `c₁ < c₂ < 1`, with the source restriction `n ≥ 1`. The coordinates, full matrices, gradients, accepted step lengths, and exact trial histories do not depend on these parameters; they occur only in proofs and the run's line-search fields.
- The neighborhood quantifier precedes an eventual scale bound and **all** accepted indices and all phase-compatible trial indices. Therefore an entire accepted-and-trial trajectory lies in every prescribed neighborhood for all sufficiently large scales. The bound is proved in the Pi norm, which gives exactly the same finite-dimensional neighborhoods as the source Euclidean statement; the target is itself topological and has no norm mismatch.

## Actual objective and actual deterministic oracle

`phi_hasDerivAt_plateau` derives the actual derivative from equality with an affine function on an open neighborhood of a strict interior plateau point. Closed slab membership suffices for exact values; the certified accepted and trial points satisfy strict slab inequalities, so the derivative argument never uses a boundary derivative without justification. The parameter interval `2 ≤ b ≤ 34` is discharged for both literal scalar parameters.

The first two slabs bound the vertical coordinate; this makes the fourth branch strictly negative while every plateau branch is positive. `local_cone` consequently proves the exact local equality to `a_n³ + a_n² G(h)`. Unique active seed branches yield an actual neighborhood equality to a smooth branch, hence a true `HasFDerivAt` for the four-piece objective. Every accepted point and each of the nine phase-indexed trial points receives its own actual value/gradient certificate. Scaling preserves the strict active branch and the slab bounds because `a_n ≤ 1/16` and the already checked seed branch bounds are strict.

`actualData` and `actualOracleData` discharge all fields of `SeedEmbedding.Data` and `OracleData`. In particular, values scale by `a_n⁴` and gradients by `a_n²`; the additive center value cancels in Armijo. `trial_predicates` proves equivalence of the actual and seed comparisons. The search proof executes the actual recursive lower/upper bracket algorithm from lower bound zero, no finite upper bracket, and initial trial one. Its result is the actual accepted length **and the entire ordered history**:

- phase 0: `[1]`, accepting `1`;
- phase 1: `[1, 1/2, 1/4]`, accepting `1/4`;
- phase 2: `[1, 1/2, 1/4, 1/8, 1/16]`, accepting `1/16`.

A successful result with five units of fuel proves termination within five trials; fuel is not a mathematical modification of a failing trajectory. The final theorem connects each returned length to `R.α k` and uses `fromMetric`, which computes the actual objective gradient and ordinary `−H g` direction. The accepted lengths are thus not merely externally assigned admissible values. The main exact target uses the source strict inequalities. The source's additional observation about identical non-strict acceptance follows from strict margins but is not separately represented by an alternative non-strict search definition in this tranche.

## Full update and conclusions

`SeedEmbedding.metric_update` uses the proved identity for simultaneous nonzero scaling of both secant vectors in the unmodified full inverse-BFGS formula. It neither rescales a stored matrix as an algorithmic action nor skips an update. The actual `AdmissibleBFGSRun` has `H₀ = I`; SPD at every finite step is derived by the verified full-update theorem. Accepted gradients are actual and nonzero.

All limiting behavior is a conclusion. The explicit three-phase sequence yields iterate convergence to the nonzero center and value convergence to its positive cubic value. Strict value decrease and strict separation above the limit are also derived. Nonstationarity uses the actual global supporting-vector predicate and the strictly lower value at zero; an independent one-sided directional derivative along `(-1,16)` equals `−a_n² < 0`. The proof assumes no matrix convergence, iterate convergence, summability, or chosen step lengths beyond the already derived deterministic search outputs.

## Independent audit evidence

Independently matched all 74 + 54 declaration names against their complete transitive-axiom reports: only `propext`, `Classical.choice`, and `Quot.sound` occur. Independently recomputed all ten root source hashes plus the objective hash from its main validation record. Additional strict `Meta.isDefEq` checks for both exact D target/wrapper pairs are recorded in `audit/D_EMBEDDING_PEER_CONTRACTS.lean` and `audit/d_embedding_peer_contracts.log`. This review leaves historical source material unchanged and does not replace the next whole-project audit.

## Supplemental retained source estimates

Also reviewed `DScalarSmallBounds.lean` and `DEmbeddingBounds.lean` (eight further declarations). The scalar estimates are for the literal assembled function and its proved first/second derivative functions, on the right-hand punctured neighborhood of zero. They derive `O(x³)`, `O(x²)`, and `O(x)` from the actual geometric interval cover, endpoint values, monotonicity, and interval curvature, with fixed positive parameter-dependent constants. The embedding supplements prove the horizontal slab bound, the source lower bound `a_n³/2` for each active plateau branch, exact center active-set membership, and actual values at every phase-compatible deterministic trial. No new premise replaces a construction property. Independently matched all eight axiom reports (standard axioms only) and both hashes in `audit/d_embedding_supplement_declarations.json`. Both strict exact-target peer checks above completed successfully.
