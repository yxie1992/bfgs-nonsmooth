# Exact D/L algebraic seed and source certificate

Source: D.tex equations D:polys, D:rho and lemma D:root; the inherited root in
L.tex. Original research sources are unchanged. The four modules
PolynomialBounds, AlgebraicSeedData, AlgebraicSeedRoot, AlgebraicSeedJacobian
contain 64 scoped declarations. All were built and individually audited with
only propext, Classical.choice, Quot.sound. See algebraic_seed_build.log,
algebraic_seed_axioms.log, algebraic_seed_validation.log and the independent
ALGEBRAIC_SEED_ROOT_PEER_REVIEW.md, including its Jacobian supplement.

The two polynomials, six named algebraic factors, exact terminating rational
center, and closed infinity-norm radius 10^-30 agree with the source.
`exact_closed_box` proves existence and uniqueness over the entire closed box,
with the two original polynomial equations explicitly in the conclusion.
`root` selects that proved root; it does not select the rational center or
assume existence. The whole box satisfies positive U,V,R,K,T,Y,U+129 and the
literal ratio 129*R/(V*(U+129)) lies strictly between 0.060 and 0.061.

`AlgebraicSeedData` contains exact rational coefficients for the translated
Newton map x -> x-M*P(center+x). Ring normalization proves its complete
coordinate polynomial identities for arbitrary real x. No linear terms remain;
all nonconstant monomials have degree at least two. Kernel-checked rational
arithmetic bounds each residual by 10^-50 and each sum of absolute coefficients
weighted by degree by 7000. Elementary product-difference bounds then give a
Lipschitz constant 7000*r on the radius-r box, yielding a self-map and a Banach
contraction on the source box. M's invertibility is proved by an exact matrix
identity, so fixed points are exactly polynomial roots. The proof includes
uniqueness, not just existence or a small residual.

The actual Frechet derivative of the original polynomial vector at center is
proved to be matrixCLM J. M equals the true inverse J^-1. The actual source
residual and the actual supremum of the induced infinity-operator norm
I-M*DP(z) over the full original box satisfy the printed 10^-50 and 10^-26
bounds. A larger radius 4*r/3 gives an open neighborhood at every original box
point, including boundary points, and the single strict common bound
7000*(4*r/3) proves the strict supremum inequality.

`scripts/generate_algebraic_seed.py` reproduces AlgebraicSeedData.lean byte for
byte. It constructs rational candidates using Python's standard Fraction type;
it is not a proof oracle. Every generated identity and inequality is proved by
Lean's ring/norm_num proof terms. There is no native_decide or unchecked
external computation in the proof chain.

This closes the exact root and the source root-certificate details. Actual
BFGS three-update closure, secant/denominator identities in that later update
chain, all deterministic rejected/accepted trial decisions, the infinite
self-similar run, and the D/L embeddings and dynamical claims remain separate
obligations. The source phrase 'all denominators' will be checked expression
by expression as those later formulas are formalized.
