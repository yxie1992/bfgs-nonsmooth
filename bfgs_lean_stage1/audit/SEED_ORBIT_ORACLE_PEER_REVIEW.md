# Independent source and dependency review: exact seed orbit and oracle

Reviewed the stable main files `IntervalBounds`, `BFGSScaling`, `AlgebraicSeedOrbitData`, `AlgebraicSeedOracleData`, `AlgebraicSeedOracleBridges`, `AlgebraicSeedOrbitGeometry`, `AlgebraicSeedOrbitHomogeneity`, `AlgebraicSeedFiniteCycle`, and `AlgebraicSeedInfiniteOrbit`, together with `scripts/generate_seed_oracle.py`, against original D.tex lines 104–223. Source and implementation files were not edited. No mathematical or table-index defect was found.

## Actual objective, points and matrices

`SeedOrbit.objective c d` is the actual finite maximum of the three source linear forms, with zero affine offsets. `initialPoint` agrees with D's z0 formula. The second and third phase points use the correct cumulative displacements −1 and −897/1024 in the first coordinate, and 0 and 1/64 in the second. The phase directions are the actual −M_j*g_j directions: `source_direction` proves this from the exact source-root matrix theorem for every scalar length. In particular the phase-2 direction is 16*rho*(1−c,−d), and multiplication by the accepted 1/16 gives the source last displacement.

`source_metric_posDef` derives all three base matrices SPD from the initial identity and actual positive BFGS curvature. It does not assume matrix SPD or use a numerical Sylvester verdict. `phase_zero_step`, `phase_one_step`, and `source_phase_two_step` prove the exact point cycle including the wrap z3=rho*z0. The three source metric-update theorems likewise supply the exact wrap rho*M0.

Strict branch dominance is defined using the actual source dot products. `objective_of_active` and `hasGradient_of_active` identify both the actual maximum value and actual Fréchet derivative, rather than treating table branch indices as oracle assumptions.

## All nine source table entries

The arrays and individual certificate declarations agree exactly with the source table:

| q | Phase | Length | Active branch | Decision |
|---|---|---|---|---|
| 0 | 0 | 1 | 1 | accept |
| 1 | 1 | 1 | 0 | reject |
| 2 | 1 | 1/2 | 0 | reject |
| 3 | 1 | 1/4 | 2 | accept |
| 4 | 2 | 1 | 0 | reject |
| 5 | 2 | 1/2 | 0 | reject |
| 6 | 2 | 1/4 | 0 | reject |
| 7 | 2 | 1/8 | 0 | reject |
| 8 | 2 | 1/16 | 0 | accept |

The accepted table rows are selected as q=0,3,8 and their new gradients are nextPhase=1,2,0. This matches both the point and matrix phase transitions. Every certificate also proves strict branch dominance, all three branch values in (−3,3), second coordinate below 2, and strictly positive actual objective value. The three base points have the same bounds.

The raw candidate arithmetic checks strict Armijo with c1=1/3, negative current-gradient pairing, and positive new-gradient pairing at accepted rows. Thus the Wolfe ratio is negative. The bridge to every 0<c1≤1/3 correctly reverses the c1 inequality when multiplying by the negative predicted pairing. Any positive c2 works for these strict Wolfe comparisons; the actual run constructor separately imposes c1<c2<1. Rejected rows prove the stronger actual value increase above the current value, and `actual_reject` derives strict Armijo rejection for any positive c1. The source's decimal values/ratios are explanatory; this unit proves their needed strict inequalities, not decimal-rounding equalities.

## Generated intervals are proof candidates only

The generator uses exact Python `Fraction` endpoints and emits `Bounds a x b` claims with ordinary Lean proof bodies. Every constant leaf is justified by `IntervalBounds.exact`; every arithmetic node applies a proved real interval rule followed by kernel-checked `norm_num`. Positive reciprocals require a checked positive lower endpoint. Every final positivity claim is a proved rational lower bound followed by transitivity. `OracleBridges` unfolds the actual objective coordinates and proves the candidate expressions imply the named certificates. Consequently neither Python's arithmetic output nor its selected expression tree is accepted as an unchecked theorem.

The exact root is placed in the stated tighter c,d rectangle by `root_tight_box`, using the certified radius and coordinate norm inequalities. `tight_ratio` derives the actual rational ratio enclosure from c,d, so r's enclosure is not a new assumption in `source_trial_certificate` or the final run.

## Infinite actual full-BFGS run

The general `BFGSScaling` theorem scales the current matrix and actual step by the same nonzero scalar while leaving the gradient difference unchanged. The inverse-BFGS projection factors are proved invariant and the rank-one term is proved to scale correctly. This is the exact source scaling law; no modified update is introduced.

The orbit uses `phase k=k mod 3`, `period k=k/3`, and rho raised to the period. `phase_period_cases` proves all successor cases, including the period increment at phase 2. The three point/matrix closures then yield actual `orbit_step` and `orbit_update` at every natural index. Positive rho powers preserve strict activity, actual gradients, and strict accepted inequalities.

`SeedOrbit.run` is an actual `AdmissibleBFGSRun 2` for the source finite convex maximum, for every 0<c1≤1/3 and c1<c2<1. It supplies actual gradients, nonzero gradients, positive lengths, initial SPD, the full inverse-BFGS recurrence, Armijo and weak Wolfe. No iterate/matrix convergence or objective-gradient assignments are assumed. Subsequent SPD of the run follows from the existing generic run invariant, in addition to the independently proved base metric SPD.

## Remaining scope

This tranche itself does not prove that the listed lengths are outputs of the particular deterministic bracket/halving search interpreter; it proves the finite strict trial decisions and constructs the admissible run using the displayed accepted lengths. That distinction should remain until the interpreter connection is proved. The orbit's limiting values and nonoptimality, the coercive D embedding with all local scaled trials, and the L stable-set/embedding construction are also outside the reviewed files. The seed maximum must not be relabeled the final finite coercive counterexample.

## Actual axiom evidence

`SeedOrbitPeerAudit.lean` independently imports the final main run module and prints all 106 explicit declarations across these nine files, including all 13 raw interval theorem contracts, all finite certificates and the run constructor. The importing audit completed successfully. Its transitive dependencies contain only `propext`, `Classical.choice` and `Quot.sound` (some declarations use fewer or no axioms). No custom mathematical axiom or proof bypass occurs. `seed_orbit_peer_axioms.log` records the actual output; `seed_orbit_peer_validation.log` validates all requested names and records exact source/audit hashes. This is scoped evidence after seventh whole-project milestone f820c46.
