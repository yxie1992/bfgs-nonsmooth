# Independent review: the literal scalar spike in Module U

Scope: the nine frozen scratch modules `NormalSpikeBump`, `NormalSpikeScaled`,
`NormalSpikeSeries`, `NormalSpikeGeometry`, `NormalSpikeBounds`,
`NormalSpikeRegularity`, `NormalSpikeOracle`, `NormalSpikeMassSupport`, and
`NormalSpikeTargets`, against U.18, U.19 and the scalar identities of U.7.1.
The reviewed snapshot is identified by
`audit/scratch/normal_spike/source_hashes.json`. All nine source files were read,
including the strengthened zero-endpoint statement added during review.

Result: no unresolved mathematical or statement defect in this scalar scope.
The refreshed structural check was independently rerun and passed: 151 explicit
declarations, standard transitive axioms only, one exact target, and nine
unchanged source hashes. The compiler, axiom and exact-contract records are
`build.log`, `axioms.log`, `contracts.log`, and `validation.log` in the same
scratch directory. This is a scoped certificate; it is not a replacement for
the next whole-project audit after main-library integration.

## Source correspondence and proof checks

- `scale N = (1/2)^(N+2)` gives exactly the source's indices `j ≥ 2`.
  The piecewise bump agrees with the absolute-value formula at both boundary
  points; actual first derivatives glue with value zero there.
- The cumulative mass and first moment use exactly the source polynomials
  `P` and `Q`. The powers in the scaled density, mass and primitive are
  `a^(-3)`, `a^2` and `a^7`. The computed mass is `(16/15)*a^2`.
  Actual bump supports are pairwise disjoint, and the total density mass is
  proved to equal `4/45` with integrability, rather than assumed finite.
- The literal integral-defined `sourcePrimitive` is proved equal to the
  infinite sum of the exact scaled primitives. Integration of the series is
  justified by summable integral bounds. Uniform summability of the first
  derivatives yields the global actual derivative and continuity; no finite
  truncation, external numerical evaluation, or formal differentiation of an
  unjustified second-derivative series is used.
- Away from zero, smaller-scale terms have constant mass and affine
  primitive. This local decomposition proves the stated third-order
  smoothness. Convexity and nonnegativity are derived from the actual terms.
- The estimates `0 ≤ r'(v) ≤ 6*v^2` and `0 ≤ r(v) ≤ 6*v^3` hold for every
  nonnegative `v`, which includes the source's neighborhood assertion. The
  geometric-tail argument uses the first scale below `2*v` and the exact
  summable mass bound. The zero-endpoint derivative of the mass follows from
  these estimates.
- The oracle uses the complete infinite tail. Its partial-bump mass and
  moment, the smaller-bump mass `(16/45)*a^2` and moment `(16/105)*a^3`, and
  all three exact peak formulas match U.7.1. The actual second derivative at
  the positive peaks tends to positive infinity while the peaks tend to zero.

## Contract correction made during review

The first target snapshot asserted only `deriv (deriv sourcePrimitive) 0 = 0`.
Since Lean's total derivative can take a default value where no derivative
exists, that equality alone did not express the source's existence claim.
The revised target now also contains
`HasDerivAt (deriv sourcePrimitive) 0 0`, proved through the global first
derivative identity and the checked derivative of the mass at zero. It also
explicitly contains failure of continuity of the second derivative at zero,
proved from the incompatible peak limits. The compiler and exact-target audit
were rerun on this strengthened snapshot. No source hypothesis was added.

## Scope boundaries

This review does not certify the higher-dimensional objective in U.20,
its full-BFGS convergence, failure of RS, the variable-jump example U.7.2, or
any recorded numerical BFGS experiments. Those are separate obligations.
The oracle identities are exact real identities; the nine-module target does
not separately formalize the rational-valued-query corollary as a theorem
over `ℚ`. Later evolving `NormalSpikeObjective` and `NormalSpikeGradient`
scratch files are excluded from this review and from the nine recorded hashes.
