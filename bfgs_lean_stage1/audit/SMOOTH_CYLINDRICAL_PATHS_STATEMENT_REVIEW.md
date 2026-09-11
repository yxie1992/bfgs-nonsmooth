# Actual smooth paths through cylindrical graphs and bands

This is objective-independent infrastructure for the remaining Module A finite-path argument, followed by an actual lifted-objective-graph bridge. It does not assume or claim that an arbitrary semialgebraic set already has a finite cylindrical decomposition. The original report is unchanged.

The frozen snapshot comprises five files, 37 explicit declarations and eight constructor/projection reports for `PiecewiseSmoothPath`, with four exact contracts and seven strict source/wrapper comparisons. `verify.sh` builds the two declared main dependency targets, freshly builds every owned file, and prints all 45 actual types and transitive axioms. The source hashes and declaration inventory are in `declarations.json`; actual gate output is in `validation.log`.

## Actual path predicate and calculus

`PiecewiseSmoothPath S x y` contains an actual function `curve : ℝ → E`, continuity on `[0,1]`, the actual endpoint equalities, containment of every parameter in `[0,1]` in `S`, a finite set of real exceptional parameters, and `ContDiffAt ℝ ∞ curve t` at every interior parameter outside that set. Here `∞` means C-infinity, not analyticity. No smoothness or containment outside `[0,1]` is required. `PiecewiseSmoothPathIn` is existence of that data.

The proofs establish reflexivity for points of `S`, symmetry, transitivity and an equivalence relation on the subtype `S`. Concatenation is the literal curve `p(2t)` up to `t=1/2` and `q(2t-1)` afterward. Endpoint matching proves continuity at the join. The new exception set is exactly the union of the two affine images of the old finite sets, with `1/2` adjoined. Away from that set the relevant original interior parameter is nonexceptional, and actual eventual equality to its affine composition proves smoothness. In particular, smoothness of either original path at its endpoints is never assumed.

The mapping theorem takes actual `ContDiffOn ℝ ∞ G S` and `MapsTo G S T`. It proves a path in `T` under the actual composite `G ∘ curve`. This only needs smoothness **within** `S`: at an interior parameter, composition within `[0,1]` gives actual smoothness at the parameter because `[0,1]` is its neighborhood. No global extension or smoothness off `S` is introduced. Ordinary `JoinedIn`, `IsPathConnected` for nonempty sets, and `IsPreconnected` without a nonemptiness requirement are also derived from the actual curves.

## Graphs and bands

`PiecewiseSmoothConnected S` is the all-pairs path property on `S`; it permits an empty set. From it the scope derives the same property for:

- the actual graph `{(x,t) | x∈S ∧ t=f(x)}` when `f` is C-infinity within `S`;
- the open band `{(x,t) | x∈S ∧ a(x)<t<b(x)}` when both boundaries are C-infinity within `S` and `a<b` throughout `S`;
- either one-sided open band above `a` or below `b`;
- the entire cylinder `{(x,t) | x∈S}`.

The graph proof uses the actual map `x ↦ (x,f(x))`. The generic `cylinder_of_section` proof first moves vertically from the initial point to a smooth section, follows the mapped actual base path, and then moves vertically to the final point. Convexity of the actual vertical fiber keeps the two actual linear segments inside the target. The open-band section is `(a+b)/2`; the one-sided sections are `a+1` and `b-1`; the full-cylinder section is zero. All section membership inequalities and fiber convexity facts are derived. There is no omitted bound, positivity condition at an endpoint, assumed path selector or interpolation computation.

## Lifted actual objective graph

`lifted_graph_piecewiseDifferentiablePath` takes an actual smooth path in a set `T` satisfying only:

`z∈T → z(none)=F(z∘some) ∧ z∘some∈S`.

It produces the existing `AffineSupportPath.PiecewiseDifferentiablePathIn F S` between the actual retained-coordinate endpoints. The projected curve is continuous and differentiable by coordinate projection. Its actual objective composition agrees with the lifted `none` coordinate on all of `[0,1]`; at each interior parameter this is neighborhood equality, so the derivative of the `none` coordinate gives the derivative of **the actual composite** `F ∘ projectedCurve`. No differentiability of `F`, gradient selection, continuity of gradients or separate differentiability premise for the composite is used.

`affineCriticalGraph_path_project` specializes to the actual critical graph already proved definable, and `objective_eq_of_smooth_criticalGraph_path` invokes the checked two-sided convex supporting-path derivative argument to prove equality of endpoint objective values. The latter has the actual finite convex objective premise and an actual path in its actual critical graph; it does not claim path existence from semialgebraicity.

## Boundaries of this tranche

These are conditional construction lemmas from actual smooth base paths and actual smooth boundary functions. General finite root delineation and the finite cylindrical-cover induction remain separate work. This predicate does not additionally assert that the parameter curve's graph is semialgebraic; the ordinary finite piecewise-smooth paths constructed here suffice for the source value-constancy argument. A literal stronger theorem about semialgebraicity of every constructed path would need the corresponding path-graph closure bookkeeping and is not claimed by these targets.

The critical-graph bridge controls both differentiabilities using one lifted path, replacing any need to assume regularity of the nonsmooth objective along an independently supplied path. Finite critical values and a positive low-level gap still require the actual finite cover/path-existence construction. No such final conclusion is encoded as a definition or assumed by these helper proofs. Only standard Lean axioms are permitted by the scoped audit; all arithmetic, interval, continuity, smoothness and set-containment steps are kernel checked.
