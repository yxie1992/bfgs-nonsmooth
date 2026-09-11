# Independent review: Module L step-ramp scalar variant

Result: PASS, no defects found in the frozen eight-file, 78-declaration,
four-target scope listed by `audit/scratch/l_step/source_hashes.json`.

I read all eight source modules and target types against L.tex's step-ramp
variant, including the reused exact geometric ratio, center, interval and
half-scale plateau data from the previously reviewed smooth scalar construction.
The original mathematical source is unchanged.

The ramp uses precisely the printed strict convention (zero at the center,
one above it). Its actual interval integral is proved to equal the positive
part primitive for every real argument; the discontinuous endpoint is handled
by the interval integral's measure-zero endpoint semantics. The full scalar is
an actual convergent infinite hinge sum plus `max(0,-x)`. Summability, finite
convexity, continuity, nonnegativity, coercivity and unique zero are derived.
No finite-valuedness or geometric tail identity is assumed.

The exact positive-interval and outer formulas are proved from the actual
series. The same actual node values and derivatives, and the full closed
`abs(h) <= scale(n)/2` affine neighborhood, are established for every natural n,
including n=0. Derivatives follow from local identities, with strictly open
neighborhoods used where derivative existence is needed.

The countable affine family is explicit and its maximum is actually attained
at every real point. Each positive line is a global support obtained from the
verified convex function and its actual node derivative; the appropriate line
attains on each positive interval, and `-x` attains on the nonpositive half-line.
At zero the other lines approach the value without attaining it. The proof
correctly avoids applying a finite-family active-gradient rule at this
accumulation point.

Every nonzero scalar point has a genuine local maximum-of-two-affines
representation. At a differentiability point, strict winners persist and a tie
forces equal actual derivatives by Fermat's theorem, hence equal affine germs.
Zero is proved nondifferentiable using the two actual global lower supports.
The resulting zero second derivative is stated as
`HasDerivAt (deriv (phi b)) 0 x`, with derivative existence proved, and all-order
local smoothness follows from the affine germ. No total-derivative shortcut or
assumed Hessian value is used.

The target hypotheses are the explicit closed coefficient range
`17/10 <= b <= 34`. The target conclusions cover the literal scalar definition,
geometry/attained countable maximum, all node/plateau formulas, and actual local
regularity at every differentiability point. This is a scalar prerequisite;
the multidimensional countably affine objective, fixed matrix transformation,
and actual infinite BFGS embedding remain separate parent-owned work.

I independently reran all eight frozen hashes and the complete 78-name
transitive-axiom/declaration validation (`audit/l_scalar_step_peer_validation.log`)
and all four strict `Meta.isDefEq` contracts
(`audit/l_scalar_step_peer_contracts.log`). Both passed. Every dependency report
uses only `propext`, `Classical.choice`, and `Quot.sound`; the peer snapshot
matches the recorded pinned compiler-success evidence.
