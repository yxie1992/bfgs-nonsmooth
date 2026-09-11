# Independent review: actual component definability

PASS. Reviewed both declarations in the frozen `SemialgebraicComponents.lean`, rebuilt that source into a separate peer object directory, and checked the actual transitive axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The second theorem was compared by strict definitional equality against an independently restated contract; the universe-polymorphic source was instantiated only for this comparison.

`connectedComponentIn_eq_union_cover` identifies the actual component through an arbitrary point with the union of exactly those finite-cover pieces that meet it. For the reverse inclusion, a common point identifies the piece's connected component with the target component, and preconnectedness places the entire piece inside it. There is no hidden relative openness, closedness, disjointness, or nonempty-set assumption. In particular, a point outside the set has an empty component and the displayed union is empty.

`connectedComponentIn_semialgebraic_of_finite_preconnected_cover` applies the existing proved finite-union closure to that exact equality. The filter defining the finite family need not itself be semialgebraic: it selects finitely many actual semialgebraic pieces. This is valid and requires no selection oracle.

The remaining prerequisite is explicit: an actual finite preconnected semialgebraic cover must still be supplied. These statements alone do not prove that every semialgebraic set has such a cover, and they do not prove critical-value finiteness. They correctly close component definability once the separately constructed cover is available.

Evidence: `ComponentPeerAudit.lean`, `component_peer_source_hashes.json`, `component_peer_build.log`, `component_peer_axioms_contracts.log`, and `component_peer_validation.log`. No owned source was changed.
