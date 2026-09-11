# Independent review: actual coercive deterministic seed failure

Reviewed `AlgebraicSeedCoercive.lean` against the literal four-piece objective in D.tex lines231–235 and the previously reviewed exact seed/oracle/deterministic-trace chain. No Lean source was edited in this review.

The actual `MaxAffine.Family 2 4` has gradients g0=(1,0), g1=(−1,−1/8), the certified g2=(c,d), and (0,1), with intercepts 0,0,0,−17. Thus the objective is exactly max{u,−u−v/8,cu+dv,v−17}. The inherited certified parameter proof supplies −c+16d<−1. At the actual point (−1,16), each branch is bounded above by −1 and the first branch attains it. The three explicit coordinate inequalities derive the global lower bound −1 and force this optimizer to be unique. Compactness of every sublevel follows from the already proved finite convex unique-minimum localization theorem; there is no assumed coercivity or bounded orbit premise.

The transfer of the seed oracle is exact. A PointCertificate has a strictly positive old active value and vertical coordinate below17; hence the new fourth branch is strictly below the old active branch. This derives both objective equality and an actual HasFDerivAt statement. Scaling requires 0<t≤1, and the actual orbit scales are proved to satisfy both conditions. All nine listed source trial types inherit those certificates, including rejected trials. The old gradient and direction are not merely postulated for the new objective: actual_coordinateGradient rewrites them using the new derivative theorem.

The three deterministic searches reproduce the literal histories [1], [1,1/2,1/4], and [1,1/2,1/4,1/8,1/16], with the corresponding accepted lengths1,1/4,1/16. Rejections are actual strict-Armijo failures. Acceptance supplies strict Armijo and strict weak Wolfe. The final fromMetric theorem uses the actual current inverse metric and actual coordinate gradient at every index. Five units of search fuel suffice for all histories, so no unexamined future trial is part of the asserted execution.

`coerciveRun` is an actual AdmissibleBFGSRun, including its true inverse-BFGS update, current derivatives, SPD initial matrix, positive lengths and nonzero gradients. The final theorem derives H0=I, iterates→0, strictly decreasing positive objective values→0, while the attained minimum is−1. The limit0 is proved nonstationary by the actual subgradient supporting definition and the actual optimizer value. No iterate or matrix convergence is assumed in the run data.

The parameter range is exactly 0<c1≤1/3 and c1<c2<1. This is a coercive global counterexample and does not assert the later local C2 embedding near the true optimizer. All-trial actual differentiability is an additional exported theorem even though it is not duplicated as a conjunct of the final package. A standalone cocompact-filter notation for coercivity is not exported; the actual compact-sublevel formulation is proved for every level, matching the source argument.

Axiom evidence: independently matched all30 declarations in CoerciveSeedAxiomChecks.lean against the existing actual compiler log coercive_seed_axioms.log. Each transitive dependency list is contained in {propext, Classical.choice, Quot.sound}; no placeholder or unchecked-computation declaration is present. The previously reviewed seed-chain proofs remain the imported mathematical foundation. No statement or source-scope defect found.

Source SHA256: `61e885307502547dc4fed4abe3cad1c1b9092e6d979a8c98beeece11a450c540`.
Audit SHA256: `b0ed917b9e6db101c6ef655d0888e6d30d91ed12f293165a2690d6744c9d91fa`.
Compiler axiom-log SHA256: `bfb452ec909adaa8a0de534f879b2e6e8638ac6c61d1fb5309562a57db20dbd9`.
