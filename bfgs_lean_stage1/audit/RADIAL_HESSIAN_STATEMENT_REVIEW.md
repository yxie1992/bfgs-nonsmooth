# Actual radial Hessian interpretation

Source: original `report/chapters/R.tex`, lines 131–139, the smooth-region infinitesimal interpretation. Source unchanged.

`RadialHessian.ray_second_derivative` proves that the actual second scalar derivative of t↦F(x+t*v), at t=0, is the actual second Fréchet derivative applied to (v,v). The only regularity hypothesis is actual `ContDiffAt ℝ 2 F x`; neither a gradient formula nor a Hessian representation is assumed. The proof first derives differentiability of the actual derivative map, then identifies the scalar first derivative on a neighborhood by the chain rule, so the second derivative is not taken of an unverified surrogate.

`matrix F x` has entries obtained by applying the actual second derivative to coordinate unit vectors. `bilinearMatrix_quadratic` proves its quadratic form equals the corresponding bilinear application in arbitrary finite dimension. `ray_second_derivative_matrix` consequently gives the literal source vᵀ Hessian(F)(x) v formula, with v=x−star as its immediate radial specialization. Its dot product is the actual coordinate Euclidean pairing; the underlying Pi topology does not change this formula.

This identifies the radial directional curvature, not a bound on all Hessian eigenvalues. The module does not infer a uniform RS/IR constant from merely pointwise C2 regularity, and does not infer a nonsmooth criterion from an almost-everywhere Hessian bound. A separate explicit singular-curvature counterexample remains a source interpretation obligation. The distinction between fractional radial parameter and unit-distance parameter likewise needs its separately tracked constant comparison if presented as an exported source equivalence.

The main build and complete seven-declaration scoped audit passed (four theorems, three definitions). Actual logs are `radial_hessian_{build,axioms,validation}.log`, with exact hashes and standard axioms only (propext, Classical.choice, Quot.sound). This addition follows seventh whole-project milestone f820c46.
