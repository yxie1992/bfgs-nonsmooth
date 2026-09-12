# Second editorial pass: narrative, scope and readability

I read the actual assembly in `paper/master.tex`, its included article sections and the three in-document appendices. I also inspected the separate related-work draft; it is not included in the assembly and therefore does not create repeated related-work prose in the paper. This pass follows the independent positive proof review and the negative contract/arithmetic reviews. It is an agent review, not human peer review or a PDF-layout inspection.

The central contrast is clear: local finite polyhedral geometry plus smooth cell extensions yields one basin for arbitrary initial SPD matrices, while four smooth convex formulas can encode bad configurations at shrinking scales. The introduction states the actual runs and the quantifiers before discussing proof machinery. It distinguishes successful accepted-step runs from termination of a specific implementation. The two negative theorems and comparison table preserve the incompatible regularity regimes, and the initial-matrix and all-query clauses remain visible.

The development has a coherent mathematical path. The mixed ridge explains surviving common descent; the seed figure is expressly illustrative. The energy identity motivates the secant budget before the full matrix hierarchy is used. The radial equivalence converts that sufficient budget into recognizable classes. The negative section derives one finite strict trial tree, proves its exact infinite scaling, and then embeds it into one fixed objective. The separate lower-curvature appendix explains why adding a quadratic requires an actual stable-manifold orbit and does not reuse a rounded seed as an exact trajectory.

The related-work framing distinguishes established tools and antecedents from the complete stated theorem contracts. It credits determinant/trace analysis, cocoercivity, separation, root enclosure and geometric structures, and identifies unpublished items as preprints. No first-ever, exhaustive-priority, generic-failure or dynamical-classification claim is made. The companion-only section expressly identifies its extensions as outside the independently established article theorems; it does not insert an essential proof-free dependency into the article core.

Two minor clarity refinements were sent to the assembling author:

- In the introduction, “a fixed radial direction” should mean the direction toward a fixed minimizer; the actual vector varies with the current point.
- In the geometric motivation, a “positive gap” at the wrong seed corner should refer explicitly to the coercive realization, or simply say that a strict descent direction remains. The initially defined homogeneous seed is unbounded below.

Neither issue changes a formal theorem or invalidates the supplied proof. The final verification paragraph must be tied to the final combined audit, including the newly added article-only wrappers, and any statement about completed review passes must correspond to completed artifacts. The root task owns that final reconciliation. I did not infer a passed render from source readability or from file hashes.

The final example wording in the positive section now expressly assumes locally C1,1 convex losses. The independent arithmetic review passed the complete displayed root/query certificate and the four shape-Jacobian bounds and spectral signs. The article-only convex-balance wrapper also compiled cleanly with pinned Lean 4.19.0 and uses only `propext`, `Classical.choice` and `Quot.sound`; its compiler output is being incorporated into the separate article audit.

## Source snapshot

- `paper/master.tex`: `d286b565c9072091768b6e578ebd1b98651b66faff2cf90accaa5a37b367ee2b`
- `paper/sections/introduction.tex`: `fa8824b6d9a940cabb0bd4e92f690c0c05bf47b72c47d3eca43b1544d83dcdec`
- `paper/sections/geometry.tex`: `9f993ff41442605fb9f25110332a3327d2c22606502149a1ff7b969cd05d72b6`
- `paper/sections/energy.tex`: `cf23294356740d167aa6a034f642007123067dc4d32b97256a3c4f82cf239206`
- `paper/sections/positive.tex`: `14d661bdc166839b228bc4610f078306e78a2585a83d60d4d136fb2b69d93598`
- `paper/sections/beyond.tex`: `7309f7822e6a922c189e91cccfd1392f3b6af602bc5121643d3784527380b317`
- `paper/sections/failure.tex`: `d404fd698f98823fab4344a41de8ca1aef5889536b4c1a0d6f2768a6942f3d9d`
- `paper/sections/verification.tex`: `679c8117500c3d0463fcdb7459c6e5653472c940bc2ada65c21535e64ae612de`
- `paper/appendices/matrix_algebra.tex`: `c388eb5210324adbe4a194b8ef25d599b3960c6d2758b06f052bae0427322f0a`
- `paper/appendices/seed_certificate.tex`: `2f2f76962f7adfdd036d9ebd602f79fd607d4ace435c4665f035ec7713ebdf98`
- `paper/appendices/lower_curvature.tex`: `09c01518b02a6337d3a95a92010c379a3c2b9b15774fe450a0fdaad9f0bb434f`
