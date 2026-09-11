# Full derivative matching at a cell boundary

`CellDerivativeMatching.lean` separately closes the literal intermediate assertion from the proof of R:thm:plq: if the actual objective and a differentiable extension agree on the relevant part of an adjacent full-dimensional convex cell, their derivatives agree at any common differentiable point, including the cell boundary.

Full dimensionality is expressed as nonempty interior of the cell. This is used through `uniqueDiffOn_convex`, not assumed derivative convergence. The representation holds only on the intersection of the cell with an open neighborhood of the point. Equality of the functions there gives equality in the neighborhood filter restricted to the cell, and uniqueness of the restricted derivative identifies the full continuous linear maps. `actual_gradients_eq_on_cell` then derives equality of the actual coordinate gradients using injectivity of `gradientFunctional`.

No sequence of interior gradients, continuity of the objective gradient on a neighborhood, or preexisting full-gradient matching is assumed. Lower-dimensional cells remain covered by the independently verified radial convergence proof, but the full-gradient equality statement correctly retains its full-dimensionality hypothesis.

The main import build passed. The two explicit declarations in `CellDerivativeMatchingAudit.lean` match the captured axiom output exactly and depend only on `propext`, `Classical.choice`, and `Quot.sound`. The source file has no forbidden proof placeholders, custom mathematical axioms, or unchecked native computations. Logs: `cell_derivative_matching_build.log`, `cell_derivative_matching_axioms.log`.
