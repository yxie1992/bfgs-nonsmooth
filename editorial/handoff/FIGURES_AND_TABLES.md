# Figures and tables: explain the mathematics

These are production specifications, not generated figure data. Use the corrected repository's canonical objects. Create vector figures using reproducible mathematics/code (for example TikZ or scripted plotting), not decorative generative images. Keep black/grayscale distinguishability, readable final-size labels, and exact/schematic status explicit.

## Figure 1: what survives a gradient jump?

**Reader question:** Why can accommodating nonsmoothness coexist with continued descent—or with failure?

Use small gradient-space panels, not a complex surface plot:

- At a nonoptimal point of `u^2+|v|`, show `(2u,1)` and `(2u,-1)`, their vertical difference, and their shared horizontal component.
- At its optimizer, show the balanced normal segment and disappearance of horizontal descent.
- For the canonical certified negative seed, show the three active slopes, their convex hull and affine hull, the origin outside the convex hull, and a genuine common descent direction.

Caption must say that the last panel is the geometry of the **constructed failing cycle**. It must not state that every such triangle causes BFGS failure. If scaled or simplified gradients are used for readability, label the panel as schematic and do not identify those points as the exact seed.

The corrected source's final seed uses `(1,0)`, `(-1,-1/8)`, and an isolated algebraic pair. Confirm this in the current repository. Do not import the earlier `(-2/3,-1/9)` variant or mix their contraction constants.

## Figure 2: the actual deterministic line search

**Reader question:** How can a conventional implementation follow the bad cycle?

Plot one base three-step seed orbit and one contracted copy. Mark rejected trial points separately from accepted iterates. Use exact source formulas/interval-certified coefficients for the mathematical data; rendering may use high precision but is not itself the proof.

Pair with a compact table of trial sequences:

    [1]
    [1, 1/2, 1/4]
    [1, 1/2, 1/4, 1/8, 1/16]

Verify that the chosen seed really has those decisions and the stated parameter range. Explain all rejected points are rejected by the documented test and that accepted tests have strict slack. The main theorem proves the infinite sequence using closure and scaling; the plot illustrates that proof.

Avoid a giant coefficient table in the introduction. Place exact polynomial equations, rational boxes and rigorous inequalities in the proof appendix. State that displayed decimal coordinates are not the definition of the algebraic root.

## Figure 3: from global to local failure

**Reader question:** Why does moving the starting point closer not fix the counterexample?

Show two distinct situations:

- A single wrong vertex separated from the true optimizer: small localization can avoid it.
- A sequence of embedded bad configurations approaching one fixed unique optimizer, with one entire failing query path in each neighborhood.

Use schematic drawings with explicit labels if not plotting the full constructed objective. Never imply multiple local minima: the bad vertices are nonstationary. Emphasize the order `one fixed F; every radius; some bad start`.

Do not portray a decimal approximation of the positive-curvature stable-manifold state as a certified infinite trajectory. Illustrate the embedding architecture schematically instead unless actual rigorous orbit data are available.

## Essential tables

### Negative regularity regimes

Two rows, not a merged theorem:

- Global C^{2,1} convex branches; upper curvature bound; no positive lower bound asserted; deterministic local failure.
- Global C^{1,1} uniformly strongly convex branches; branch second differentiability absent at the accumulation point; deterministic local failure.

Add a distinct remark for the global three-quadratic example and for the literal constant-classical-Hessian variant. Keep initialization transformations and implementation quantifiers in the caption/text.

### Main theorem scope

A small table should compare objective structure, dimension, locality, assumptions, and conclusion. Do not put every lemma into it. The detailed inventory belongs in the companion.

## Reproducibility and layout checks

For each figure, record the script/source, mathematical data source, generation command, whether it is exact-data or schematic, and the final output file. Do not submit a figure without its source. Text must refer to every figure in logical order and explain why it matters.

Render the PDFs and inspect at final size. Check labels, axes, overlap, grayscale distinction, line thickness, captions, and that no rejected trial is confused with an accepted iterate. A beautifully rendered but mathematically misleading figure fails review.

Numerical experiments are optional illustrations, not evidence replacing analytic or formal proof. If existing experiments are used, rely only on actual reproducible current evidence, not withdrawn historical counts. Do not launch a broad benchmark exercise merely to make a theoretical paper look empirical.
