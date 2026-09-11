# Module G scalar nonnecessity: statement review

Source reviewed: `BFGS_MASTER_REPORT_LaTeX/report/chapters/G.tex`, sections G.6 and G.7. The source is preserved. The two new modules concern failure of a sufficient certificate condition while all admissible scalar runs converge. Neither module constructs a failing BFGS trajectory.

## Shifted quadratic plus absolute value

`ScalarCounterexamples.lean` defines the literal real objective `(t+2)^2/2+|t|`, together with its exact `Vec 1` representation. It proves `StrongConvexOn univ 1`, the minimum value `3/2` at `-1`, uniqueness, and compactness of every scalar and coordinate sublevel. Coordinate gradients are actual `HasFDerivAt` derivatives, obtained from actual scalar derivatives; they are not assigned oracle data.

The exact source crossing `x=epsilon`, `z=-epsilon/2` has the source gradients, values, predicted decrease and curvature. `crossing_strict` proves every displayed eligibility comparison strictly for every positive epsilon, a stronger range than needed. `crossing_quotient` gives its exact quotient and `crossing_quotient_tendsto` proves divergence to `atTop` as epsilon tends to zero from above, not merely unboundedness along a selected finite sample.

`shifted_no_band_certificate` fixes the compact sublevel `F<=3` and fixed positive band gap `1/4` above the minimum. Both crossing endpoints are proved in this band for `0<epsilon<=1/8`. The proof quantifies over every proposed positive decrease threshold and every finite Lipschitz bound; it invokes the previously verified exact scalar equivalence. `shifted_no_band_certificates` then refutes the all-positive-band condition on this sublevel. The source's phrase “a sublevel containing zero” is instantiated by `F<=3`, which contains a neighborhood of zero; no universal claim is made for every level with zero on its boundary.

`shifted_scalar_run_converges` proves objective and iterate convergence for every `ScalarMetricRun shiftedAbs`, with arbitrary positive scalar metrics. `shifted_actual_bfgs_converges` is the actual `AdmissibleBFGSRun 1 shiftedObjective` specialization. Compactness is derived from the objective rather than passed as an extra condition. Neither theorem assumes metric, Hessian, gradient, or iterate convergence.

## Accumulating kink series

`AccumulatingKinks.lean` uses zero-based `knot j=(1/4)^(j+1)`, so Lean index zero is source `a_1=1/4`. The objective is the actual infinite `tsum`, not a truncation. `term_summable` proves absolute summability using the nonnegative geometric majorant `knot j * |x|`. `series_uniform_on_compact` proves uniform convergence of the actual partial sums on every compact scalar set. Termwise convexity and summability prove convexity of the series; strong convexity of the objective is then proved with constant one.

`objective_lower`, `objective_zero`, `objective_minimum`, and `objective_unique` prove the quadratic lower bound and unique minimizer zero. `objective_sublevel_compact` proves compactness of every real sublevel, and the coordinate version does likewise. `objective_coercive` additionally exports the standard coercivity statement `Tendsto objective (cocompact ℝ) atTop`. Thus both the standard limit, direct quadratic lower bound, and all-sublevel compactness are available.

Exact geometric sums yield `objective_formula_below` and `objective_formula_above`, including boundary equality, and `objective_knot = 13/10*(knot j)^2`. Local equality to these polynomials proves actual derivatives on both open adjacent intervals. `hasDerivWithinAt_knot_left` and `hasDerivWithinAt_knot_right` prove left and right derivatives `2a` and `5a`; uniqueness of derivatives proves nondifferentiability at every knot. A separately proved quadratic upper bound proves `hasDerivAt_zero`, so regularity at the optimizer is not assumed. `nonsmooth_in_every_neighborhood` proves the accumulation assertion.

For each fixed knot, the actual endpoints `a+epsilon` and `a-epsilon` have the exact source gradients and values. `crossing_decrease`, `crossing_curvature`, and `crossing_values` give `d=10a*epsilon+2epsilon^2`, `t=6a*epsilon+4epsilon^2`, and `Delta=7a*epsilon`. `crossing_strict` and `crossing_eligible` prove the exact `(c1,c2)=(1/4,1/2)` inequalities for `0<epsilon<=a/8`. `crossing_quotient` is the literal source quotient; `crossing_quotient_tendsto` proves its one-sided divergence to positive infinity at each fixed knot.

`no_quotient_near_knot` works for every set `K` containing a neighborhood of that fixed knot, on the fixed positive band gap `13a^2/20`. It refutes every proposed threshold and finite quotient bound. `no_visibility_secant_near_knot` consequently excludes visibility and suppression alone, allowing singular, discontinuous, and unbounded finite-valued fields. `no_band_certificate_near_knot` excludes the transported certificate. No regularity assumption on a certificate field is introduced.

`every_neighborhood_no_certificates` states that **every** `K` in the neighborhood filter of zero fails the all-positive-band certificate condition. The proof first chooses one knot with a whole neighborhood inside `K`, then fixes its positive band and only then sends epsilon to zero. This preserves the source's band-dependent constants and does not interchange the knot and crossing limits. This statement applies in particular to every sufficiently low positive compact sublevel, since those are neighborhoods of the continuous minimizer.

Finally, `scalar_run_converges` and `actual_bfgs_converges` prove objective and iterate convergence to zero for all arbitrary-positive-metric scalar runs and all actual dimension-one full-BFGS runs respectively. All initial sublevel compactness is derived.

## Reproduction and scope

From `bfgs_lean_stage1`, source `scripts/env.sh`, then run:

```sh
lake build BfgsVerification.ScalarCounterexamples BfgsVerification.AccumulatingKinks
lake env lean audit/ScalarCounterexamplesAudit.lean
lake env lean audit/AccumulatingKinksAudit.lean
```

The current joint compiler output is `audit/scalar_examples_build.log`. Per-module transitive axiom outputs are `audit/scalar_counterexamples_axioms.log` and `audit/accumulating_kinks_axioms.log`. The audit files enumerate all 39 and 76 public definitions/theorems, respectively, including supporting declarations and actual-run conclusions. Only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies are permitted. No source correction, extra mathematical assumption, admitted proof, custom mathematical axiom, or unchecked external computation was needed.

This review covers these two example modules. The separate geometric interpretation and pointwise feasibility claims elsewhere in G remain separate obligations; completing the examples does not relabel those claims as verified.
