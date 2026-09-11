# Independent review: actual L smooth invariant stable manifold

Review result: PASS. No mathematical or contract defect found in the twenty-source snapshot recorded by `source_hashes.json` (90 explicit declarations, two exact contracts). I read every frozen source file, the source discussion in `report/chapters/L.tex` lines 197–214, and the relevant existing actual-return derivative/splitting and vanishing-sequence contraction interfaces. The source statement review accurately distinguishes the earlier actual-orbit proof from this new smooth embedded-graph and local-invariance result.

The independent checks reran the frozen-source validator, the complete actual-type/transitive-axiom driver and both strict target comparisons with the pinned Lean compiler. `peer_validation.log`, `peer_axioms.log`, `peer_contracts.log`, and `peer_report_validation.log` record these checks. All twenty source hashes remain unchanged. All ninety dependency reports use only `propext`, `Classical.choice`, and `Quot.sound`. Both final proof constants have exactly their named proposition types under `Meta.isDefEq`. This is independent validation of the owner's fresh passing full build; it does not replace theorem-statement review with compilation alone.

## Sequence-space analyticity and fixed point

The coefficient lift is an actual pointwise continuous multilinear map on bounded sequences. Its operator-norm estimate follows from the original coefficient bound and the norm bound for each sequence evaluation. This includes arity zero; no positive-arity assumption enters the construction. The coefficient norm inequality gives a lifted convergence radius at least the original radius. Applying bounded evaluation maps to the actual convergent series and using uniqueness of sums identifies the lift with the original nonlinear function at every coordinate of every sequence inside one positive-radius ball. No unproved superposition theorem or external series computation is used.

The zero-derivative result uses actual derivative existence, coordinate evaluation, eventual equality on that ball and derivative uniqueness. The resulting strict derivative is derived from analyticity. There is no substitution of a bare total `fderiv = 0` assertion for differentiability.

The linear sequence operator correctly combines the stable forward recurrence with the backward unstable recurrence. Its norm is bounded by `max ‖A‖ ‖B‖`, where B is the inverse of the expanding block. The nonlinear operator shifts the stable remainder and applies negative B to the unshifted unstable remainder, giving exactly the desired equation. The inverse of I minus the linear sequence operator is constructed from the proved norm bound. The residual map has an explicitly invertible triangular derivative; the actual inverse function theorem supplies the parameterized fixed point, its derivative and local uniqueness.

The use of analytic regularity produces a single neighborhood on which the graph is smooth to all finite orders. The implicit solution is initially only a bounded sequence. It is then identified, by the derived local uniqueness and explicit radius comparisons, with the independently constructed vanishing-at-infinity contraction solution. Thus convergence and the actual forward recurrence are established for every parameter in the resulting neighborhood; they are not assumptions on the implicit solution or on all bounded sequences.

## Tangency, embedding and literal return map

The derivative's unstable sequence satisfies a genuine backward recurrence. Its boundedness and powers of the inverse-contracting block force every unstable coordinate to vanish. This proves the graph's zero unstable derivative by composition with actual sequence evaluation.

The coordinate change is a continuous linear equivalence; the chart is literally `seed + E (a, h a)`. Stable projection of `E.symm (x-seed)` is an explicit inverse on the graph, so the restriction to the open parameter neighborhood is a topological embedding. Smoothness of the chart and its actual derivative at zero are proved. The derivative is the stable inclusion transported by E, whose injectivity gives rank two.

The proof separately identifies the range of that inclusion with the set of vectors whose powers under the actual return-map derivative converge to zero. Forward contraction gives one inclusion; a bounded backward unstable recurrence gives the other. This is equality with the genuine stable space of the actual derivative, rather than a renamed supplied subspace.

The literal application derives E and both contraction bounds from the previously verified actual five-dimensional block derivative and certified source shape roots. In particular, the second stable coordinate is exactly the physical scale for every vector under E. Since the seed has zero scale, the same identity holds for every point of the nonlinear graph, independent of its unstable graph component. Choosing a small positive second parameter in the open neighborhood gives arbitrarily small positive scale. The final theorem has only μ and an arbitrary prescribed neighborhood of the actual fixed point as inputs; it has no supplied spectrum, orbit, matrix limit, recurrence or manifold premise. Proving this geometric statement for every real μ is consistent with the actual return-map analyticity; the optimization application separately uses μ>0.

## Same-graph local invariance and source quantifiers

The last four files add a substantive invariance conclusion to the same graph. A common uniqueness radius for small convergent forward orbits is derived from the zero derivative of the remainder and the original contraction estimate. Two actual orbits staying in this radius and sharing their initial stable coordinate are proved identical.

The constructed graph's orbits are chosen within that uniqueness radius. Continuity gives an open smaller parameter neighborhood V₀ whose next stable coordinate lies in V. Comparing the shifted graph orbit with the graph orbit at that next coordinate proves that the actual return map sends the graph over V₀ into the same graph over V. The proof does not switch to a separately selected graph or assume orbit uniqueness. Both compared orbits satisfy the common radius, convergence and actual recurrence conditions before uniqueness is applied.

In the final contract, the prescribed ambient neighborhood W precedes construction of E, h and V; every parameter in V has a full actual forward orbit that stays in W at every time and converges to the actual fixed point. The explicit local-invariance conclusion uses V₀⊆V and the same E and h. This is the appropriate local statement: it does not claim global invariance of every arbitrary truncated chart, nor classification of distant orbits. Together with the smooth embedded two-dimensional graph and exact tangent space, it supplies the ancillary stable-manifold assertion used in the source. Actual BFGS execution and physical embedding are already separate verified results; this scope does not falsely claim to rederive them from a new assumed orbit.

No source correction, added final hypothesis, or weakening was found necessary in this tranche.

## Main source correspondence

The reviewed twenty-file snapshot was copied to BfgsVerification with only the owned import prefixes qualified. The delivered validator compares every main source both to its delivered hash and, after normalizing those imports, to the frozen reviewed hash. The main build and fresh main actual-type/transitive-axiom/strict-contract logs are separate from the independent scratch evidence above. Delivered reproduction does not require scratch.
