# Independent polynomial sampling review

PASS — root reviewed all six sources and reran actual types, transitive axioms,
five strict source/wrapper checks, and an independently restated final formula.
See PeerAudit.lean, peer_axioms_contracts.log and peer_validation.log.

The nonzero-factor product is an actual polynomial. Filtering zero factors is
proved to preserve the original family’s boundary and sign behavior, retaining
zero factors as sign zero. A real point in a bounded root-free gap has the same
simultaneous signs as an actual derivative root supplied by Rolle’s theorem.
Root-list membership requires and derives a nonzero derivative in that case;
constants and the empty family instead use the explicit tails. Each tail lies
beyond every actual root, and its sign vector is proved from the actual
leading coefficients and degree parity. Every sign is represented by ONE common
real sample, rather than a different witness for each polynomial.

The final root-count identity uses actual distinct real roots and actual Tarski
queries. A zero derivative polynomial contributes zero, exactly as its empty
root list requires. No root-count or sign-preservation oracle is a premise.
The six source and eleven dependency hashes match the owner’s frozen manifest.
Only propext, Classical.choice and Quot.sound occur in the 29 independent reports.

Scope: this is a fixed-fiber simultaneous sign reduction. Parameter-uniform
semialgebraic Tarski-query fibers, arbitrary Boolean projection and smooth path
decomposition still require subsequent proofs. No such closure is claimed here.
