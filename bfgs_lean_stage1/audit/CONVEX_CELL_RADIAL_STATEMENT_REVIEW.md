# Finite polyhedral cells: source and statement review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/R.tex`, Theorem `R:thm:plq` (“Finite polyhedral partitions”) and its subsequent piecewise linear-quadratic corollaries.

## Main theorem verified

`BfgsVerification/ConvexCellRadial.lean` builds under the pinned toolchain. The scoped audit requests all ten explicit declarations; captured outputs match exactly and their transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom `axiom`, or `native_decide` occurs. Logs: `convex_cell_radial_build.log`, `convex_cell_radial_axioms.log`; audit source: `ConvexCellRadialAudit.lean`.

`finite_polyhedral_basin` uses actual cells given by finitely many affine inequalities `dot (a i j) x ≤ b i j`. Their closedness and convexity are proved from this representation. A finite family covers an open neighborhood of the attained unique minimizer. On each cell in that neighborhood, the actual finite convex objective equals its supplied extension; each extension is locally C1,1 on its own open neighborhood of the relevant part of its cell. Those neighborhoods need not initially coincide. Equality with the actual objective implies compatibility on overlaps, rather than requiring a separate compatibility assumption.

The theorem derives one positive objective starting level, quantified before every actual infinite `AdmissibleBFGSRun`. Every run starting at or below that level remains in the source neighborhood and has both objective and iterate convergence to the unique minimizer. Compact sublevels are derived from finite convexity and the attained unique minimizer. The radial estimate, correction control, and full-BFGS convergence chain are derived, not premises. There is no assumed identification of a cell, active manifold, limiting matrix, or convergent subsequence of gradients.

## Stronger route used in the proof

The underlying `local_cells_basin` theorem permits arbitrary finitely many closed convex cells, including lower-dimensional cells and overlapping interiors. The source polyhedral/full-dimensional assumptions imply these hypotheses. This is a stronger theorem, not a weakening of the source conclusion.

- Finiteness and closedness produce a neighborhood excluding every cell not containing the minimizer.
- Each remaining convex cell contains the whole segment from any point in it to the minimizer. The local representation neighborhood is shrunk to a ball, so that segment also remains inside the representation domain.
- At an actual differentiable point of the objective, equality of the objective and the smooth extension along this one-sided segment identifies their **radial** derivatives. This is proved with `HasDerivWithinAt` and derivative uniqueness on a genuine interval at zero. It does not assume differentiability of the objective at other points on the segment.
- Local C1,1 regularity on the individual extension domains gives uniform compact Taylor bounds after the finite neighborhood reduction. The lower error bound uses convexity of the full objective. No convexity of a smooth extension away from its cell is assumed; the source explicitly allows nonconvex extensions there.
- Summing the finitely many nonnegative constants and taking a positive common parameter radius gives actual IR. Previously verified IR-to-RS and BFGS radial convergence then apply.

The displayed source proof also states equality of the *full* gradients with each adjacent full-dimensional extension at a differentiable boundary point. This stronger intermediate assertion is not exported by this unit; only the radial equality needed for the conclusion is proved. It remains a separate explanatory statement if every literal proof assertion is to receive its own declaration. No such full-gradient matching assertion is used as a hidden premise.

## Named subclasses

The independent `QuadraticCellRadial` unit builds successfully and its seven-declaration scoped audit (`QuadraticCellRadialAudit.lean`, `quadratic_cell_radial_build.log`, `quadratic_cell_radial_axioms.log`) matches every requested name with only the three standard axioms and no forbidden tokens. It derives regularity from actual quadratic coefficients and exports the piecewise linear-quadratic and smooth-plus-piecewise-linear-quadratic basins. Those additional declarations are not counted in the ten-declaration audit above. A finite maximum of arbitrary convex quadratics is not automatically represented by these polyhedral cells and is not claimed to be covered without a valid representation.
