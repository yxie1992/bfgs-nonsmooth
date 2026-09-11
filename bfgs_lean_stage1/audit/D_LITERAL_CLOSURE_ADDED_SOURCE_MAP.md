# Literal D source spans closed by this supplement

The milestone15 D map retains these four spans as pending literal exports. This separately audited six-file supplement supplies them, without modifying the milestone15 map or proof sources while frozen.

| Original D lines | Literal claim | Exact checked declarations |
| --- | --- | --- |
| 34–35 | Non-strict tests produce the same actual run | `NonStrictLineSearch.Armijo`, `NonStrictLineSearch.Wolfe`, `NonStrictLineSearch.search`, `DLiteralTargets.nonStrictRun` |
| 163–168 | Polynomial equations are exactly beta=1/4 and gamma=1/16 | `DLiteralIdentities.beta_quarter_iff`, `gamma_sixteenth_iff`, `original_box_polynomial_iff`; included in `DLiteralTargets.literalIdentities` |
| 224–230 | Zero excluded from convex hull of the three actual source gradients | `DLiteralIdentities.gradient_support_zero`, `zero_not_mem_gradient_hull`; included in `DLiteralTargets.literalIdentities` |
| 231–236 | Literal convex weights (8/17,8/17,1/17) give the constant lower-bound affine combination -1 | `DLiteralIdentities.coercive_exact_affine_combination`, `coercive_weights_convex`; included in `DLiteralTargets.literalIdentities` |

Every previous principal target and the 33-display numerical, whole-box actual denominator and Euclidean maximum-of-nine supplements remain unchanged. Independent source review remains a separate quality gate from this owner compiler/type/axiom/strict-target PASS.
