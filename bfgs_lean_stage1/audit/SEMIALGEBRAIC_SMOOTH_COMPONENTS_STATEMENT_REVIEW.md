# Unconditional actual smooth-path components of semialgebraic sets

One frozen source proves three declarations: `semialgebraic_smooth_components`, the exact `SemialgebraicSmoothComponentsTarget`, and its wrapper `semialgebraicSmoothComponents`. The sole mathematical premise is actual semialgebraicity of an arbitrary set in finite real coordinate space.

The finite smooth semialgebraic cover is derived from the proved dimension-induction theorem `semialgebraic_finite_smooth_cover`. Its actual finite set is enumerated using `Finset.equivFin`; both directions of the exact cover equality and membership of every enumerated piece are proved. The previously audited actual component theorem then gives finitely many actual smooth-path components, and semialgebraicity plus internal piecewise-smooth connectivity of every actual component.

No finite-cover, root-sign, query, genericity, objective-regularity, or component-connectivity premise survives in the final statement. Empty sets, dimension zero, and arbitrary degree or zero polynomial presentations are included through the cover theorem. This is objective-independent and matches Module C line 336's finite piecewise-smooth path-component assertion. It does not identify these components with ordinary connected components, and it does not assert semialgebraicity of the individual witnessing path graphs. The latter is separate stronger wording in Module A.

The scratch dependency overlay is needed only to prevent duplicate names from mixed scratch/main module imports. Four previously frozen sources are copied with import lines alone normalized to `BfgsVerification.*`. The manifest records both original and normalized hashes. Existing main objects are symlinked into the private package directory, while all four normalized dependencies and all ten actual cover source dependencies are freshly compiled by the delivered reproduction script. Every reachable main source hash is frozen too. No source proof body is altered by normalization.

Reproduce with `bash audit/scratch/semialgebraic_smooth_components/verify.sh` from the Lean project. The validator checks owned/dependency hashes, compiler success, all three actual type/transitive-axiom reports, and strict source/wrapper equality to the exact target. Original research and shared root audit files remain unchanged.

## Main integration

The delivered main source is exactly the frozen, independently reviewed source with its cover import normalized to `BfgsVerification.SemialgebraicSmoothCover`. The private scratch overlay is unnecessary for the delivered main build. `audit/verify_semialgebraic_smooth_components.sh` checks the actual main import, all three transitive axiom reports, strict source/wrapper contracts, and exact import-only source equality. Peer review: `audit/scratch/semialgebraic_smooth_components/INDEPENDENT_PEER_REVIEW.md`.

## Delivery independence

The public declaration manifest embeds each independently reviewed original source SHA and the exact import correspondence. Validation reconstructs the reviewed original from delivered main text and compares that SHA; it does not read the original scratch tree. The actual independent peer review, build/axiom/validation/reproducibility logs, and import-normalized peer driver are copied into public `audit/` files and hashed in the manifest. A separate validation run rejects every attempt to open a path under `audit/scratch/` and still passes. The proof sources and closed compiler/axiom logs remain unchanged.
