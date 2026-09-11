# Exact rational oracle

`NormalSpikeRational.lean` contains computable definitions over the exact rational type. There is no `noncomputable` declaration, floating-point operation, external computation, truncation assumption or supplied oracle correctness premise.

For a positive query, the index is the least natural number for which `2*ratScale N < v`. Its existence is proved from the dyadic limit, and the standard well-founded `Nat.find` implementation performs the rational decidable search. The finite prefix uses the exact piecewise polynomial splines. The entire remaining tail is added using the proved geometric mass and moment constants. A positive query can contain at most one partial bump by the independently proved support separation. Queries at zero or below return zero, including the actual second derivative at zero.

`RationalSpikeOracleTarget` is a universal equality for every rational query: the rational value, first-derivative and second-derivative program outputs, cast to the reals, equal the integral-defined source function and its actual derivatives. It covers bump interiors, endpoints, gaps, zero and the negative half-line. Actual derivative existence at zero and regularity off zero are available from the scalar construction; the oracle does not infer existence merely from Lean's total derivative operator.

The implementation uses a finite sum for the prefix rather than the source's optimized single-partial-bump presentation. Every omitted infinite-tail term is accounted for exactly. The theorem verifies these Lean rational programs and the printed mathematical oracle identities. It does not claim a source-code correspondence proof for a separate experimental Python implementation.

`scale_eq_source` also proves the literal index conversion from `scale N` to the printed `2^{-(N+2)}`. All proof dependencies and the exact target are audited separately by `verify_rational.sh`; no numerical evaluation is used as evidence for a mathematical theorem.

Main integration: the reviewed sources were copied with only import prefixes changed. `audit/verify_normal_spike_examples.sh` rebuilds all nine main modules and rechecks all 98 declarations and five exact targets. Scratch proof evidence is preserved separately.
