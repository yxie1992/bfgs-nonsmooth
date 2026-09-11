# Actual piecewise-smooth path components

The two frozen files prove twelve declarations, one exact joint contract, and two strict source/wrapper comparisons. The reproduction script freshly compiles the three frozen generic smooth-path dependencies and both owned sources before auditing actual types and transitive axioms. Run `bash audit/scratch/smooth_path_components/verify.sh` from the Lean project.

`piecewiseSmoothComponent S x` is the actual set of points reachable from `x` by a continuous real-parameter path contained in `S`, smooth at every interior parameter outside a finite exceptional set. It is the equivalence class of the previously proved symmetric/transitive/reflexive-on-`S` path relation, not an assumed component operator. It is empty when `x` is outside `S`.

The prefix lemma constructs the actual path `u ↦ p(t*u)` for any `t ∈ [0,1]`. For `t > 0`, its exceptional set is the finite image of the original exceptions under division by `t`; interior smoothness follows from the actual derivative composition. At `t = 0`, the constant path is used. Thus every point of a path belongs to its source's component, and the path itself has image in that component. Concatenation then proves every actual component is itself piecewise-smooth connected. No component smoothness or local connectivity premise is assumed.

Given a finite cover by actual piecewise-smooth connected pieces, an entire cover piece belongs to one path component as soon as it meets that component: concatenate the reaching path with the piece's connecting path. This proves an exact union of whole pieces for each actual component. It also makes the image of each piece under the component map a subsingleton, so the actual component family is finite.

When each cover piece is semialgebraic, each actual component is semialgebraic by the proved finite-union closure. No openness, closedness, disjointness, or nonempty-piece assumptions are added. Empty sets and empty finite covers are included. The final target states finiteness of the actual family and semialgebraicity plus internal piecewise-smooth connectivity of every actual component.

This supplies the component interpretation used literally in Module C line 336 once the separate finite semialgebraic smooth cover has been derived. The result does not assume or prove that ordinary connected components equal these path components. Nor does it claim that the witnessing path graphs are semialgebraic: they have the actual finite-piece-smooth regularity needed for the objective path calculus, while the resulting component sets are semialgebraic. The stronger semialgebraic-path wording in Module A is separate source scope.

The finite cover remains an explicit prerequisite. This module alone does not assert a global semialgebraic cell decomposition. Original research and shared root audit files are unchanged.

## Main integration

The two delivered `BfgsVerification` files differ from the frozen, independently reviewed scratch sources only by the two import-line normalizations. `audit/verify_smooth_components.sh` rebuilds the actual main import and validates all twelve declarations and the exact target. The delivered validator also compares every main source byte against the normalized frozen original. Independent review: `audit/scratch/smooth_path_components/INDEPENDENT_PEER_REVIEW.md`. Main import: `BfgsVerification.SmoothComponentTargets`.

## Delivery independence

The public declaration manifest embeds each independently reviewed original source SHA and the exact import correspondence. Validation reconstructs the reviewed original from delivered main text and compares that SHA; it does not read the original scratch tree. The actual independent peer review, build/axiom/validation/reproducibility logs, and import-normalized peer driver are copied into public `audit/` files and hashed in the manifest. A separate validation run rejects every attempt to open a path under `audit/scratch/` and still passes. The proof sources and closed compiler/axiom logs remain unchanged.
