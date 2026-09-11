# Literal unexcited-metric example

Source: families.tex, first paragraph of the final matrix/line-search section.
The original source is unchanged. `UnexcitedMetric.lean` contains 24 theorems
and seven definitions, including the fully constructed actual admissible run.
All 31 declarations are directly axiom-audited, including the run definition
and its proof fields. Build/audit logs are `unexcited_metric_build.log` and
`unexcited_metric_axioms.log`; only the three standard axioms occur.

The objective is literally u²+|v|. Its convexity, nonnegativity, unique zero
minimizer, actual gradients at every prescribed iterate, and true tangential
second derivative 2 are proved. For arbitrary A>0, v0>0, ordinary constants
0<c1<c2<1 and 0<rho<(1-c1)/(1+c1), `run` constructs an actual
AdmissibleBFGSRun with x_k=(0,(-rho)^k v0), H_k=diag(A,(1+rho)/(2rho)*rho^k*v0),
and alpha_k=2rho. The sign representation (-1)^k and positive radius are
proved equal to the literal source formula.

Every step and every full inverse-BFGS update is proved from the exact matrix
formula. Initial SPD, nonzero actual gradients, positive steps, actual Armijo
and weak-Wolfe are proof fields, not extra hypotheses about a guessed sequence.
The literal acceptance ratios are (1-rho)/(1+rho) and -1; the source rho bound
derives the required Armijo inequality and rho<1. No limiting information
is used in these recurrence or acceptance proofs.

`run_limits` then proves values and iterates tend to zero and the actual
inverse matrices tend to diag(A,0). Their first entry is exactly A at every
iteration. Since A was arbitrary, convergence to a universal tangential
inverse curvature is not implied. This example itself has a matrix limit;
it does not exhibit a divergent matrix sequence or a bad objective trajectory.
The source's separate finite-ray-singularity step-existence argument is not
claimed by this module.
