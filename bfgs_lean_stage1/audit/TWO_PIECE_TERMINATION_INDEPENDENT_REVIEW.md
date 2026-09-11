# Two-piece finite-termination scope: final independent review

Result: **PASS, no mathematical or statement defect found.**

This extends `CORE_INDEPENDENT_PEER_REVIEW.md` to the final nine-file scope: all622 lines,68 explicit declarations and two final targets. The six core proof files are unchanged from the prior independent review. I additionally read `TwoPieceRay`, `TwoPieceProjection`, `TwoPieceTargets`, both exact target definitions, and the relevant actual-step-existence and affine-projection dependencies. No proof source was edited.

The scope verifies the two-piece result cited in H403–408. The comparison source remains [Xie–Wächter, arXiv:1712.08571v1, SectionsII–IV](https://arxiv.org/html/1712.08571v1). This is pre-existing research. The retained model uses arbitrary initial SPD matrices and arbitrary accepted Armijo–weak-Wolfe steps at differentiable accepted points. The report's explicit limitation for the many-piece family is preserved.

## Terminal ray

`finite_bad_ray` derives the actual finite set of nondifferentiability parameters. If the first direction component is zero, the ray stays off the kink because the initial point has an actual derivative; otherwise at most one parameter can reach the kink. Neither a nonzero first direction component nor differentiability at every parameter is assumed.

For `p=-H*g`, the asymptotic slope is `|p0|+p1`. The proof establishes two concrete bounds for all nonnegative parameters:

```text
If |p0|+p1 >= 0:  f(x+t*p) >= x1-|x0|.
Always:             f(x+t*p) <= f(x)+t*(|p0|+p1).
```

At a terminal state, a nonnegative asymptotic slope would give a ray lower bound. `FiniteRayLineSearch.fullBFGS_step_exists` then supplies an actual differentiable trial with strict Armijo and strict weak Wolfe, using the derived finite singular set, current actual derivative, nonzero gradient and SPD metric. The proof constructs the next `State` from that trial and the original full inverse-BFGS update. Its positive definiteness is derived from the new actual positive curvature. This contradicts terminality of the accepted-transition relation. Thus the asymptotic slope is negative; the second bound proves actual `Tendsto ... atTop atBot` along the current full-BFGS search direction.

This closes the concern from the core review: the terminal-state restriction to SPD matrices cannot artificially create failure by excluding an otherwise acceptable next update. The hypothetical acceptable next update is proved SPD and explicitly packaged. The proof also handles a direction parallel to the kink without any division by its first component.

## Arbitrary-dimensional projection

`fullRowRank_of_row_independence` derives injectivity of the actual transpose action from actual linear independence of the rows. `rowMatrix u v` and `image_objective` identify the literal objective `|dot u x|+dot v x`; the target explicitly retains the independence condition. The full-row-rank premise rules out the impossible dimensions automatically, without an additional unstated dimension assumption.

`no_infinite_linear_image` applies the released `AffineProjection.projectRun`. I inspected that dependency and its actual derivative/compression statements. The projected metric is exactly `Q*H*Q.transpose`, including all contributions of the original arbitrary SPD matrix. Actual derivatives descend through a right inverse at the accepted point, the lifted projected gradient equals the original gradient, and the original full inverse update compresses exactly. Positive definiteness, step sizes, Armijo and weak Wolfe are all transferred. There is no discarded off-plane coupling, assumed invariant matrix block, assumed projected gradient, or assumed convergence.

Consequently an infinite accepted run for the independent-linear-form objective would produce an infinite actual run for `|u|+t`, contradicting the core theorem. The target asserts precisely this arbitrary-dimensional no-infinite-run conclusion; it does not silently substitute it for a separately formulated arbitrary-dimensional terminal-state/ray theorem.

## Exact final statements

`twoPieceTermination : TwoPieceTerminationTarget` asserts convexity of the literal two-dimensional objective and, for every valid fixed pair of line-search constants, both:

- well-foundedness of **all** actual accepted-step choices;
- from every actual differentiable SPD state, a finitely reachable terminal state whose actual search ray tends to negative infinity.

The reverse-relation orientation and reachability direction remain correct. Well-foundedness excludes every infinite accepted continuation; the finite reachable terminal witness supplements that statement and is not an assumption of it. The theorem does not specify numerical trial-search iteration behavior after the terminal direction is reached.

`twoPieceLinearImage : TwoPieceLinearImageTarget` asserts impossibility of infinite actual accepted runs for arbitrary finite-dimensional full-row-rank linear images and for explicit independent vectors `u,v`. It has no extra initial matrix normalization or limiting-state premise. A finite terminal-ray theorem in arbitrary-dimensional `State` syntax, a universal statement including dependent linear forms/affine offsets, or finite termination for general many-piece objectives is not claimed by this target.

## Independent validation

The source inventory independently matched all nine files and all68 declaration names in `declarations.json`. `peer_final_source_hashes.json` records the unchanged frozen hashes. Fresh `PeerFinalAxioms.lean` compilation printed all actual types and transitive axiom reports; only `propext`, `Classical.choice`, and `Quot.sound` occurred. There are no proof placeholders, custom mathematical axioms or unchecked native computations in the reviewed source.

`PeerFinalContracts.lean` independently restates both conclusions, expanding the literal objective as `|x0|+x1`, and checks strict definitional equality of both actual theorem types. Both passed. The logs are `peer_final_axioms.log`, `peer_final_contracts.log`, and `peer_final_validation.log`. The earlier three independent core contracts also remain available.

This final review is separate from the root's fresh nine-module scoped rebuild/audit and eventual main/release integration. It establishes no claim beyond the two reviewed targets.
