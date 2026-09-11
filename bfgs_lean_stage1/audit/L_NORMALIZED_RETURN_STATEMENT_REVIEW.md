# Module L actual normalized return map: statement review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/L.tex`, the five normalized coordinates and equations L:eq:formal1, L:eq:formal2, L:eq:return, together with the algebraic diagonal blocks in L:eq:jacobian. Original sources are unchanged.

Module: `BfgsVerification/LNormalizedReturn.lean`, namespace `BfgsVerification.LNormalizedReturn`. There are 85 declarations: 66 theorems, 17 definitions, and 2 abbreviations. The stable unit is integrated after the tenth whole-project milestone; the original scratch source and logs are retained. The final target is `normalized_return_contract`; it makes no stable-orbit or actual deterministic-search claim.

## Exact map and state

`State` is the literal five-dimensional real coordinate space. The coordinates are (z0,z1,b,e,tau), with `point w=[w0,w1]`, `shape w=[[1,w2],[w2,w3]]`, and `scale w=w4`. The seed is the actual algebraic initial seed point followed by (0,1,0). The parameter mu is fixed and arbitrary in this algebraic/analytic unit; the physical quadratic failure theorem will require mu>0.

`currentGradient`, `step`, `secant`, and `substep` implement precisely the displayed formulas with the actual cyclic seed slopes, lengths 1,1/4,1/16, and actual `inverseBFGS`. The `internal` recurrence always uses the original input `scale w`; it does not renormalize or change tau between the three substeps. The return factor is the actual final matrix entry (0,0). `returnMap` divides the two final point coordinates and final matrix entries (0,1)/(1,1) by that factor, and returns tau times the factor as the fifth coordinate.

All operations are total Lean functions. Claims of regularity restrict to a proved neighborhood where denominators are nonzero. Values at singular denominators elsewhere are not asserted to represent the source return dynamics.

## Seed and regularity

`internal_seed_zero/one/two/three` identify all four actual finite states with the exact seed states, ending in (rho*z0,rho*I). The source finite-cycle identities and actual update theorem discharge the equations. `seed_denominator_positive` derives each positive curvature from the actual strict accepted seed descent and Wolfe inequalities. `seed_returnFactor` identifies the actual denominator with rho, and `seed_fixed` proves the actual return fixes the seed.

`Regular mu w` includes all three positive curvatures, the positive return factor, and e>b^2 for the input shape. `regular_analytic_neighborhood` constructs an actual open neighborhood containing the boundary seed on which `Regular` holds and the actual return map is real analytic. The source's artificial negative-tau extension is legitimate because this is a neighborhood in the full five-dimensional real space; the proof does not restrict the domain to tau>=0.

The analytic proof differentiates no oracle. It composes exact finite-coordinate polynomial operations and reciprocal functions, with every reciprocal's nonzero value proved first. Matrix intermediates use the explicitly installed local entrywise-sup matrix norm and the corresponding finite product norm. The final state-space analyticity has the usual finite-Pi norm; this choice introduces no unproved numerical operator-norm constant.

`shape_posDef` uses the exact quadratic identity (v0+b*v1)^2+(e-b^2)*v1^2. `internal_posDef_of_regular` proves positive definiteness of all four internal metrics up through the third update by induction and actual inverse-BFGS positivity. No metric convergence or orbit convergence is assumed.

## Physical coordinate identities

`physical_branch_gradient` identifies the actual branch-gradient formula at tau*Z with g_j+mu*tau*Z. `physical_step`, `physical_secant`, and `physical_update` prove the source's exact scaling equations: physical step tau*S, physical secant Y, and physical updated matrix tau*M_next. They use the already verified actual branch derivatives and matrix algebra. They do not assert that the selected branch is active for the full objective; that is the separate oracle-agreement obligation.

`internal_isSymm` holds algebraically. `return_point` and `return_shape`, then `normalization_preserves_point/metric`, prove that the returned chart gives the same physical final point and stored matrix whenever the return factor is nonzero. Thus normalization is a change of representation, not a reset or rescaling operation in the algorithm.

## Actual derivative blocks already proved

On the artificial boundary tau=0, `internal_boundary_translate` shows that changing only the input point translates every internal point by the same vector and leaves every internal metric unchanged. `returnMap_boundary_translate` gives the exact affine point-translation law for the actual return map; it is independent of mu on that boundary.

`return_restricted_point_hasFDerivAt_seed` is an actual two-dimensional Frechet derivative. The chain rule gives `return_derivative_point_columns`: D T(Pstar)(pointLift v)=rho^(-1)*pointLift v. This proves the literal upper-left rho^(-1)I2 block and all zeros below those first two columns. `return_derivative_last_row` proves the final component of the actual full derivative is rho*v_tau for every five-dimensional direction, deriving the whole last row (0,0,0,0,rho) from the actual product tau*r.

## Remaining source obligations

No shape Jacobian entries, characteristic-polynomial signs, spectral intervals, invertibility, stable eigenvector transversality, or nonlinear stable orbit are assumed or proved here. The mu-proportional upper tau blocks are not yet exported. Neither the actual nine-query neighborhood agreement nor the infinite perturbed BFGS orbit follows from this algebraic unit alone; strict active-branch gaps and the finite decision tree still need their own proved neighborhood transfer. No old unperturbed orbit is claimed to survive the quadratic perturbation.

The next finite task can use the actual map to construct the shape derivative recurrence and its exact interval certificate. Actual oracle-neighborhood agreement can proceed independently from the same map definitions. The abstract stable-orbit contraction theorem remains a separate analytic prerequisite, as recorded in `audit/L_RETURN_MAP_PROOF_SPLIT.md`.

## Audit

The compiler log is `build.log`. `LNormalizedReturnAudit.lean` contains the exact scratch source followed by one `#print axioms` request for every declaration, including the two abbreviations. `axioms.log` contains transitive results; `validation.log` records matching requests, allowed axioms, source-token scan, and artifact hashes. This scratch result is excluded from the frozen tenth whole-project audit.
