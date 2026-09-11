# Independent review: A Hessian completion and L identity-initialized failures

Scope: the five frozen files in `declarations.json` under `rank_loss_hessian` and `l_identity`, comprising 54 declarations and five exact targets. The reviewer is independent of this implementation. Verdict: **PASS, no defect found in the statements or proofs reviewed.** Main release files were not edited.

## Literal A curvature claim

I compared the new rank-loss Hessian module with the objective and branch definitions in `AffineRankLossObjective.lean` and the rank-loss paragraph of `report/chapters/affine_geometry.tex`. The branches are the literal x+x²+y²±xy quadratics. The proof first establishes actual second Frechet derivatives, then identifies their actual matrix as [[2,±1],[±1,2]]. It proves symmetry, the characteristic polynomial and shifted determinant, and the precise real eigenvalue equivalence with 1 or 3, including actual nonzero eigenvectors for both values. Modulus-one Euclidean strong convexity is proved directly by subtracting half the squared Euclidean norm and expressing the remainder as a linear function plus a positive semidefinite rank-one quadratic. Taking the maximum proves the actual objective has the same modulus. This fills the source's stated curvature assertion; it does not turn the existing geometric rank-loss example into a BFGS failure claim.

## Same identity matrix for an actual family

I read all three new L identity modules and checked their application boundaries against the existing actual-copy and fixed-coordinate-whitening modules. The coordinate matrix is the square root of one fixed actual source initial SPD matrix, chosen once from `LSeedCopies.run`. The smooth and step embeddings use that same source trajectory and matrix, and the exact copy construction leaves the inverse-Hessian matrices unchanged at every scale. Thus `failure_initial` proves H₀=I for every member using one fixed coordinate change; neither the objective nor its curvature constants are chosen anew for each start.

`IdentityFailureTarget F` places the single objective F outside the entire run family. Its proofs instantiate `CopyData` from the actual literal embedding identities, not a supplied arbitrary model or orbit. The underlying actual seed trajectory and its convergence were already constructed by the reviewed L return dynamics. No orbit, spectral, iterate-limit, matrix-limit or eventual-search premise survives in either concrete failure theorem.

The contract contains the source line-search parameters, actual unmodified full-BFGS runs, exact periodic accepted lengths, and the complete ordered deterministic histories at every iteration. Affine invariance preserves all comparison pairings and the complete search, including rejections. Accepted and rejected compatible queries have actual differentiability and positive values; arbitrary compatible query selections converge to the corresponding nonstationary center. Accepted values strictly decrease to their strictly positive center value. Starts and centers tend to zero across the family. Uniform locality has the necessary order: for every neighborhood of zero there is a family threshold, after which every iteration and every compatible query lies in that neighborhood. There is no dependence on a finite time horizon.

## Source geometry after the fixed coordinate change

I compared `LIdentityGeometry` with L's identity-initialization paragraph and both local-failure alternatives. The fixed positive lower constant is μ times the smallest eigenvalue of the one source initial metric, and the upper constant is 512 times its largest eigenvalue. Their ordering and positivity are proved. The targets include actual strong convexity, compact sublevels/coercivity, the quadratic lower bound, unique zero optimizer and actual nondifferentiability at that optimizer.

For the four-branch alternative, all branches have actual global C1 regularity and actual globally Lipschitz gradients with the stated Euclidean constants. The literal finite maximum equality is included. Its Hessian bound uses the already-reviewed generic actual finite-max Hessian theorem, with explicit first differentiability near the base and actual differentiability of that derivative at the base. It does not assume a globally Lipschitz gradient for the maximum or globally C2 branches.

For the countable-polyhedral alternative, the exact actual Hessian is the fixed SPD matrix μH₀ at every differentiability point; actual second differentiability is proved there. The target also exposes the countable attained affine maximum for the residual and the exact quadratic-plus-residual decomposition. The same lower/upper constants bound its quadratic form. These statements match the source distinction between the four-C1,1-branch and countable-polyhedral alternatives.

## Independent audit evidence

I reran the pinned `Audit.lean` driver under `peer_axioms_contracts.log` and independently validated all five frozen source hashes, all 54 transitive-axiom reports and all five strict `Meta.isDefEq` target checks. Only `propext`, `Classical.choice` and `Quot.sound` occur. `peer_validation.log` and `peer_report_validation.log` record the checks. These are next-tranche scratch artifacts; they do not modify the frozen main-release evidence.

## Main source correspondence

Root copied the five reviewed files to BfgsVerification using only namespace-preserving import path replacements. The main scoped manifest records both source hashes. The separate eight-file whitening review is WHITENING_PEER_REVIEW.md. Main compilation, all 158 type/axiom reports and all five exact targets are reproduced by verify_l_identity.sh.
