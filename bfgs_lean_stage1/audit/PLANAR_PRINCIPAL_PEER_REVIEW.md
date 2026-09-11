# Independent review: planar secant and affine-critical cluster theorem

Reviewed the frozen 13-file, 53-declaration snapshot in `audit/scratch/c_principal_source_hashes.json` against Module C's bounded-secant lemma, principal affine-critical cluster theorem and affine-correctness/local-basin consequences. No mathematical or theorem-statement defect was found. I read all thirteen files, with particular attention to the five requested corner/crossing/field/run modules and the all-pair compactification and final target wrappers.

The retained corner data comes from the actual local convex C² branches used to represent F. Actual branch gradients are identified with actual accepted endpoint gradients using finite-max support uniqueness. Opposite active branches yield an actual tie point on the closed segment by the intermediate value theorem; no finite-intersection property of a curved interface is assumed. At the tie, the same field annihilates the jump. All gradient/field Lipschitz constants, boundedness and row-inverse bounds are derived on a buffered compact ball, from actual continuity and a nonzero determinant. The Euclidean/Pi norm conversions are explicit and their extra constants are included consistently.

The crossing numerator is first order in step length. Row control, the actual descent pairing and weak-Wolfe lower curvature produce the crossing-specific linear curvature bound after a uniform small-step absorption. There is no uniform positive-Hessian assumption. Same-branch and smooth pairs instead use a derived compact cocoercivity bound from local convex C² regularity. Their union is quantified over every sufficiently close differentiable pair satisfying the required descent/curvature conditions; the result is stronger than needing an Armijo decrease premise at this stage. Constants precede pair selection.

The finite buffered cover provides one open neighborhood, one positive distance and one nonnegative correction bound. It permits an empty compact set. Close endpoints lie in the same larger chart, and all intermediate points stay in that convex chart. `exists_secant_structured_visible_field` constructs exactly one field from the retained charts, and that field carries both the transport geometry and secant control; the proof does not splice independently chosen fields.

The final contradiction works near the whole actual compact cluster set. Under the contrary hypothesis it derives a positive limiting value and vanishing executed steps from strict contours. It obtains one objective-constructed field, applies the released actual transport theorem, derives the actual secant budget, selects only the resulting tail transport coefficients, and invokes the already checked actual scalar-energy/full-BFGS contradiction. No iterate convergence, metric convergence, energy hierarchy, secant budget or comparison field is a final premise. The declared run remains the unmodified full BFGS run with arbitrary SPD initialization and differentiable accepted iterates.

The final source targets impose regularity only outside affine criticality. Positive contour hypotheses range through the supplied sublevel value. Affine correctness gives values and distance to the whole minimizer set, including actual Euclidean distance; uniqueness is needed only for the point limit. The local positive basin is chosen before every admissible run and its fixed valid line-search constants or initial metric.

Independent validation checked all 53 recorded transitive-axiom reports against the standard whitelist and all thirteen source hashes. The author's clean rebuild and scoped audit pass. I additionally compiled strict `Meta.isDefEq` tests for all three target inhabitants in `audit/C_PRINCIPAL_PEER_CONTRACTS.lean` (with the scratch import path); all passed in `audit/c_principal_peer_contracts.log`. Main-copy build evidence is separately the author's responsibility; the source hashes below identify exactly the reviewed scratch snapshot.

This review covers C's principal cluster/convergence statements and the local affine-correctness wrapper. Finite-max automatic affine correctness, the explicit quadratic basin/separation example, tame-geometric assertions and the higher-dimensional warning remain separate source obligations; they are not inferred from this audit.

Frozen source hashes:

- `audit/scratch/PlanarCrossingAlgebra.lean`: `eac8a5efb5c463ade623bf6c55d987bb8b1bc9a141e66ba354ebae9814a3ebd0`
- `audit/scratch/PlanarConvexCorner.lean`: `045fd296846f9f009c1816b8ae7d14adbd4377ca0d97f14f449d17ceeed2fabf`
- `audit/scratch/PlanarBranchGeometry.lean`: `cd3280cef245502797e93dbab0cd3ac4d6059f30697754fe4f387db021019ea5`
- `audit/scratch/PlanarPairControl.lean`: `fecd695cfc433d8678d1ff3753155473606f5927859e6fbf13a5c08c655da7bd`
- `audit/scratch/PlanarCrossingSecant.lean`: `29082735a7d7f68b16294c56acd7f5087a6d69cc718ba826bb0249c038d02900`
- `audit/scratch/PlanarCornerBounds.lean`: `57b1dfe30a3fcc96d3d87320e578e9024219052cb7e4349f5f840ab1a3a0f0ff`
- `audit/scratch/PlanarLocalSecant.lean`: `b8a8f98b4d68eb8b0ef80b058dd494b2c9a4f28757e04471639b0602d8161c25`
- `audit/scratch/PlanarCompactSecant.lean`: `41fa6d5d3be679619e528ca67a15e656c54d4725a42976682cdcbca8a63865f7`
- `audit/scratch/PlanarSecantField.lean`: `52b66fadb577a9aeeade797ec1d9b0f9c6ce40cd91176c8217e7e93975225f78`
- `audit/scratch/PlanarSecantRun.lean`: `69dce92e05475056a2b448b4b8802ee3240d179d6aa620e9ad4a436a7d7cd9d8`
- `audit/scratch/PlanarConvergence.lean`: `a81186226f8045c47e74a219b8704c6c89c598230326f0a0b7b2fd428180af8c`
- `audit/scratch/PlanarPrincipalTargets.lean`: `79f82a08eb42b98de44595026b0b48832c57470d7458ecc43482f7b41dfefb65`
- `audit/scratch/PlanarPrincipalEndToEnd.lean`: `ee32d3ef47afd92b75feed42a14451022d37c4357a55769fc5d0abc2bb4e6ab9`
