# R's four-piece reference: current-model correction and historical gap

R.tex, lines 182–187, names an optimizer `(-1,5)`, minimum -1, and supporting errors `0,0,25/4` for “the four-piece counterexample.” The preserved report defines D's current four-piece objective with optimizer `(-1,16)`. Repository-wide source search and the available git history did not recover a different objective defining R's numerical example. The older attribution is therefore unresolved historical evidence; its numerical assertions are not claimed verified for the current D objective.

`historical_point_not_current_optimizer` in `CoerciveSeedIntercept.lean` (namespace `BfgsVerification.SeedOrbit`) proves the actual current objective at `(-1,5)` is at least `3/8`, so that point cannot have the reported value -1. The mathematical correction for the report's current D objective uses its already verified unique optimizer `(-1,16)` and exact supporting heights

`0, 0, -1+c-16*d`,

where `c,d` are the actual certified algebraic seed. The third height is strictly positive. `coercive_intercept_at_active` derives these heights from the actual objective and actual active gradients; `coercive_orbit_intercepts` applies them at every point of the genuine deterministic full-BFGS orbit. `orbit_secant_tendsto_zero` proves that the actual endpoint secant curvature tends to zero, by its exact scale-times-phase formula and a finite bound on the phase factors. No curvature convergence is supplied as an input.

The current objective fails both the full radial-secant condition and the equivalent supporting-plane height condition on the actual initial sublevel. These conclusions use the proved full-BFGS run and compact-sublevel convergence theorem contrapositively: the condition would force objective values to converge to -1, contradicting the independently proved actual limit 0. This proves the intended interpretation for the current counterexample without inventing the missing historical objective or assuming an earlier infinite certificate.

The original source remains unchanged. The report status register records both the verified current-model correction and the unresolved attribution of the older numbers. The scoped source/types/axiom evidence is in `CoerciveSeedInterceptAudit.lean`, `coercive_seed_intercept_axioms.log`, and its declaration/hash record. This correction does not affect the completed homogeneous/coercive seed proof or the separate C2 local embedding obligation.
