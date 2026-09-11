# Independent general semialgebraic projection review

PASS. Root read all eight source files and the five complete target definitions.
Fresh PeerAudit.lean reports54 actual types/transitive dependencies (51 explicit
plus three structure reports), ten strict source/wrapper comparisons, and an
independently restated projection theorem for arbitrary finite coordinate types
in separate universes. All eight owned and26 dependency hashes are unchanged.

FiniteSemialgebraicFunction records finite actual range and genuine polynomial
Boolean fibers. The closure lemmas use explicit finite unions/intersections,
including selection by an actually finite-valued function. Degree/sign strata
are constructed by leading-term erasure, with a strict degree drop or zero
polynomial. This retains every vanishing-leading-coefficient branch.

The actual rational-index function has semialgebraic fibers by induction on
symbolic denominator degree. One actual positive pseudo-division identity is
chosen before all parameters. Where its leading coefficient vanishes, erasure
preserves the specialized divisor. Else its even power is positive and the exact
index recurrence applies. Its symbolic remainder has smaller degree, even if
specialization drops degree further. Zero divisors and zero remainders are
explicit branches. Actual Tarski queries follow from the proved weighted
logarithmic-derivative identity, including the zero root-polynomial convention.
No oracle for roots, signs, counts, indices or parameter fibers is a hypothesis.

The parameter-dependent nonzero-factor product is selected from finitely many
literal subsets; it is not mistakenly the specialization of a fixed product
containing identically vanishing factors. Actual finite sign-count formulas,
critical-root sampling and literal coefficient/parity tails give simultaneous
scalar sign projection. Arbitrary Boolean formulas enumerate finite common
sign vectors of all atoms. One scalar witness realizes the WHOLE vector; no
separate existential witnesses are distributed over conjunction or negation.

Finite-coordinate elimination then inducts over empty/option coordinate types,
with checked reindexing through actual polynomial substitutions. No assumption
of local nondegeneracy, root simplicity, fixed degree, nonempty factors, or
quadratic degree restricts the final theorem. The semialgebraic predicate remains
genuine quantifier-free Boolean polynomial syntax; projection is a theorem about
it, not a field built into that predicate.

Only propext, Classical.choice and Quot.sound occur. This closes general
semialgebraic projection. Finite smooth path decomposition and the affine-critical
finite-value application remain separate obligations, not consequences asserted
by this tranche. See peer_axioms_contracts.log and peer_validation.log.
