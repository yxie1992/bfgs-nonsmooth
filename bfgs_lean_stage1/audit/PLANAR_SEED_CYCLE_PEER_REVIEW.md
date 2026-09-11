# Independent review: planar BFGS and algebraic seed closure

Reviewed `PlanarBFGSUpdate.lean` and `AlgebraicSeedCycle.lean` against original `report/chapters/D.tex`, lines 69–169, including the actual inverse-BFGS update definition and the imported certified-root factor bounds. No source edits or mathematical defect were found in the displayed matrix closure.

`PlanarUpdate.projector_formula` is the exact dimension-two outer-product factorization of `I-s yᵀ/(yᵀs)`. `inverse_formula` consequently computes the actual project-defined full inverse-BFGS update. It needs only nonzero curvature, not symmetry or SPD, because this is an algebraic identity. `aligned_identity` derives the scalar identity matrix after an actual aligned step from the displayed transverse-energy equation and the nonzero scale and displacement norm. That energy equation is not passed as an assumption to the source-root theorem: the seed file derives it explicitly.

The definitions of g0, g1, g2 and M1 agree exactly with D, including 129/256, −1/16, and the −1/8 gradient component. `first_step`, `first_update`, `middle_step`, `middle_curvature` and `middle_update` check the actual displacements and matrix update. The middle matrix is an exact two-rank-one expression, including the 16512 coefficient. The beta, gamma, and rhoTilde expressions match D's 66048 and 2064 constants and all polynomial factors.

`middle_metric_gradient`, `middle_perpendicular_energy`, `gamma_scale`, `last_step_generic`, and `last_perpendicular_energy` implement the source derivation rather than assuming matrix closure. `generic_closure` nests the actual updates. Its explicit nonzero T and K conditions ensure the implied BFGS curvatures are nonzero; they should remain visible when paraphrasing the source's phrase “denominators nonzero”, which includes the update's curvature denominators, not merely the displayed scalar fractions.

`source_root_polynomials` uses the proved exact root equations, not decimals or residual tolerances. `source_parameters` derives beta=1/4, gamma=1/16 and rhoTilde=rho using the checked positive factor bounds on the certified box. `source_cycle` has no root, closure, SPD, or convergence assumptions: it proves the actual three-update equality at the chosen unique certified root. The root's 0.060<rho<0.061 bounds and all factor positivity follow from `AlgebraicSeedRoot.box_denominators_and_ratio`.

The source s0 displacement is directly exported; s1 is `middle_step` specialized to 1/4. The source s2 displacement follows from `last_step_generic` and `source_parameters`, with `middle_update` identifying the actual M2. A convenience theorem specializing all three simultaneously is not required for correctness but would make the exact source target more direct.

## Scope that must not be inferred from this algebraic unit

These two files do not yet construct z0 or prove z3=rho*z0, certify the active objective gradients at those points, prove all intermediate matrices SPD, verify Armijo–weak-Wolfe acceptance or deterministic trial rejections, or construct an infinite run. The root positivity plus actual curvature formulas should discharge SPD in the orbit assembly, but this is not silently counted as an exported theorem here. Independent Hessian-form update/secant cross-checks mentioned by D are likewise outside this exact inverse-update unit. None of these boundaries invalidates the proved closure; they distinguish it from the remaining objective/algorithm certificate.

## Dependency evidence

The existing main build logs show both modules compiler-clean. An independent importing audit, `PlanarSeedPeerAudit.lean`, printed all 35 explicit declarations (25 theorems and 10 definitions) from the two files. `planar_seed_peer_axioms.log` contains only `propext`, `Classical.choice`, and `Quot.sound`, including the transitive certified-root dependencies of `source_cycle`. `planar_seed_peer_validation.log` records exact source/audit hashes and validation. No custom mathematical axiom, sorry/admit, native_decide or unchecked external computation was used. Rational simplification uses kernel-checked tactics.
