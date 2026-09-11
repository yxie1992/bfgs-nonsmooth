# Actual root counts, signature strata, ordered graphs and bands

This is a six-module, 35-declaration, four-contract infrastructure tranche for the remaining Module A geometric decomposition argument. It does not claim a higher-dimensional cell decomposition, a finite path cover, or the final semialgebraic affine-critical value theorem.

## Exact mathematical objects

Every root count is taken from `Polynomial.roots`, the actual real-root multiset of the actual coefficient-specialized polynomial. Distinct counts use its `toFinset.card`; total real multiplicity uses its `card`. There is no assumed root alphabet, continuity premise, generic degree premise or replacement counting function.

The ordered root is armijo's frozen `orderedRealRoot`: the increasing `Finset.orderEmbOfFin` enumeration of the actual distinct roots, with value zero outside the list. `orderedFiberRoot` is exactly this function applied to `fiberPolynomial`; `rootSignatureStratum` is exactly the existing simultaneous degree / distinct count / total multiplicity equality set. The source and dependency manifests freeze these definitions and all other imported scratch proofs.

## Proof chain and statement review

1. `ParameterRootCounts` proves that every simultaneous sign count on the actual distinct roots has finite semialgebraic fibers. Its witness comes from the released exact rational combination of actual Tarski queries. Equality of that expression with the natural-number count is kernel proved. The finite range bound is the symbolic polynomial degree, through the actual specialization degree bound.
2. The empty sign pattern yields the actual distinct-root count. For total multiplicity, a nonzero polynomial's root has multiplicity greater than k exactly when derivatives of orders 0 through k all vanish there. The first nonzero derivative at the actual root multiplicity proves the converse. Summing these exact counts over k below the symbolic degree, then exchanging the finite sums, yields precisely the actual root multiset cardinality. Identically zero fibers are handled separately using their actual empty root multiset. No zero polynomial is incorrectly identified with an empty set of solutions of p(t)=0.
3. `OrderedRootRanks` proves the cardinality of the roots strictly below the ith increasing root is i. The converse uses actual root membership and the surjectivity of the increasing finite enumeration. Its root-equation characterization explicitly includes p ≠ 0; the zero-default total graph has a separate out-of-range branch.
4. `ParameterRootRanks` realizes the strict-below count as a single actual sign count for X−t. Polynomial coefficient renaming embeds the parameter tuple into the tuple with the distinguished t coordinate, and specialization of the renamed polynomial is proved equal to the original specialization.
5. `OrderedRootDefinability` proves the exact existing signature stratum semialgebraic, the valid ordered-root graph semialgebraic, and the entire zero-default graph semialgebraic. Any semialgebraic parameter restriction can be intersected with that exact graph. The results include n=0, repeated roots, degree drops, empty root lists, and identically zero fibers. Smoothness is deliberately not asserted across signature changes or on the whole default graph.
6. `SemialgebraicRootBands` uses the released general polynomial scalar projection theorem, with the actual graph value as existential witness, to derive strict upper and lower graph regions. Its band wrapper permits different actual polynomials for the two bounds and an arbitrary semialgebraic base restriction. It imposes no hidden ordering or validity assumption; when indices are out of range it uses the explicitly defined zero-default function. Applications to root cells may restrict to valid indices on a constant signature stratum.

## Exact contracts

- `actualRootCounts : ActualRootCountsTarget`: finite semialgebraic fibers of both actual counts for every finite dimension and every parameter polynomial.
- `actualRootSignature : ActualRootSignatureTarget`: the existing exact three-equality stratum is semialgebraic for every polynomial and base parameter.
- `actualOrderedRootGraph : ActualOrderedRootGraphTarget`: both the valid graph and entire zero-default graph of the existing actual `orderedFiberRoot` are semialgebraic.
- `actualOrderedRootBands : ActualOrderedRootBandsTarget`: the strict region between two existing actual ordered-root functions, restricted to an arbitrary semialgebraic parameter set, is semialgebraic.

The strict contract driver compares the actual declaration type to the complete independently stated target proposition; it does not merely apply a theorem to a target after supplying extra premises.

## Reproduction and remaining scope

Run `bash audit/scratch/root_definability/verify.sh` from the project. The script uses the pinned environment, builds every main direct import, freshly rebuilds the 17 frozen scratch dependencies into a scope-owned directory, then freshly compiles all six modules. It records actual types, every transitive axiom list, four exact contract checks, and source/dependency hashes. Only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms are allowed.

This supplies the definability side of an ordered-root decomposition. The separately proved analytic continuity and local ambient smooth extension statements still require the actual signature conditions. A dimension-induction cell/path construction and its global finiteness conclusions remain separate work; none is built into `IsSemialgebraic`, whose definition is a genuine finite Boolean polynomial formula.

## Independent-review integration repair

The reviewer found that the first count-core draft used the same global helper name as the already frozen analytic matching module. The helper was renamed to `rootCount_sum_actual_multiplicities`, with its sole internal use updated. Its statement and proof are unchanged. The refreshed manifest and audit driver use the unique name, and validation now explicitly checks that none of the 35 declarations duplicates any declaration from the 17 frozen scratch dependencies. A complete fresh owner gate is required after this repair; the earlier successful gate is retained only as `initial_gate_before_name_repair.log`.
