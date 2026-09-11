# Final deterministic seed review and target audit

This extends `SEED_ORBIT_ORACLE_PEER_REVIEW.md` through `DeterministicLineSearch`, `AlgebraicSeedFailure`, `AlgebraicSeedDeterministicTests`, `AlgebraicSeedDeterministicTrace`, and `ReportDynamicsTargets/EndToEnd`. These stable main files and the original D source were reviewed without edits. No defect was found.

## Exact search interpreter

`DeterministicLineSearch.search` faithfully represents D.tex lines 23–37: initial lower bound 0, upper infinity represented by `none`, and initial length 1. Armijo failure updates the upper bound; otherwise Wolfe failure updates the lower bound; otherwise the trial is accepted. A finite upper bound gives the midpoint, and no upper bound gives twice the new lower bound. Both tests use the source strict comparisons and the actual objective, with `coordinateGradient` tied to actual derivatives by the proved bridge. The current direction in `fromMetric` is the actual ordinary −H*g, not a prescribed table vector.

The fuel counts the number of permitted trial evaluations. A success with fuel five is a proof of a finite successful prefix of the source search, not an assumed termination result. The recursion records every attempted length in order, including the final accepted one. Along the certified orbit all queried points have actual derivatives, so the generic total definition of coordinateGradient away from differentiability does not create an oracle loophole.

`scaled_search_zero/one/two` actually unfold the reject/accept transitions and prove histories [1], [1,1/2,1/4], [1,1/2,1/4,1/8,1/16]. Their respective accept lengths are 1,1/4,1/16. `orbit_search` then uses the actual current objective derivative and actual metric at every iteration to prove these are search outputs. Thus the former implementation-selection gap in the earlier seed-unit review is now closed.

`orbit_all_trials_differentiable` and `orbit_trial_point_certificate` cover every table trial at its actual scaled orbit point; the phase-index condition matches the appropriate row set. The accompanying histories contain exactly those rows. `trialHistory_length_le` proves the five-trial bound. `orbit_phase_parameters` exports the literal source formulas at index 3*m+j for points, matrices, gradients and lengths. No finite-switching or eventual branch-identification assumption appears.

The strict inequalities also provide the margins used in the source remark that non-strict tests make the same decisions. A separate interpreter defined with non-strict predicates is not exported in this tranche; the theorem targets correctly specify the source strict interpreter.

## Actual nonstationary limit

`AlgebraicSeedFailure` proves the period tends to infinity, the actual scale tends to zero and the actual points tend to zero using only boundedness of the finite base-point family. Continuity of the actual finite convex maximum gives value convergence. Values remain strictly positive and strictly decrease by the proved run's Armijo decrease.

The source direction (−1,16) has first two gradient pairings exactly −1 and third pairing strictly below −1. The actual objective on its nonnegative ray equals −t. Testing the definition of the convex subdifferential at this direction proves zero is not a subgradient at the limiting point. Hence `actual_run_failure` and `actual_deterministic_seed_failure` establish genuine failure of this actual deterministic full-BFGS seed run, not merely failure of a convergence certificate.

This objective is the homogeneous seed and is unbounded below on that proved downhill ray. The target documentation explicitly says so by distinguishing the seed subtheorem from the later coercive/local C2 embedding. Nothing here proves the final D/L finite coercive counterexamples or their unique minimizers, Hessian bounds or arbitrarily near-minimum initializations.

## Final contracts and evidence

`ExactSeedCycleTarget` uses actual full updates at the certified root and actual intermediate SPD matrices. `DeterministicSeedFailureTarget` quantifies over all source parameters 0<c1≤1/3 and c1<c2<1, constructs the actual admissible run, and states initial H=I, convergence to zero, strictly positive decreasing values tending to zero, nonstationarity of the limit and the exact interpreter output at every iteration. `AllSeedTrialsTarget` concerns the actual full-space derivative and actual point bounds of every source trial. `ReportDynamicsEndToEnd` proves all three contracts directly from this chain, with no added assumptions.

The independent importing audit `DeterministicSeedPeerAudit.lean` passed for all 42 new declarations in these six files, including the three target definitions and three final proofs. Combined with the prior 106-declaration orbit audit and 35-declaration planar/closure audit, the reviewed chain has actual transitive-axiom evidence throughout. Only propext, Classical.choice and Quot.sound occur. `deterministic_seed_peer_axioms.log` contains the actual output, and `deterministic_seed_peer_validation.log` validates every requested name and records source/audit hashes. No custom axiom or unchecked generated computation is used.
