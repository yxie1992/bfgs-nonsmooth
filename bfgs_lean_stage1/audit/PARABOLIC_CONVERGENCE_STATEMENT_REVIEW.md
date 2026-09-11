# Q principal theorem: exact statement review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/Q.tex`, lines 25–199.
Original sources are unchanged. The main export is
`AdmissibleBFGSRun.parabolic_convergence`; `parabolicConvergence` inhabits its
separately declared exact target.

`Parabolic.Family m` is the literal arbitrary finite family of real coefficients,
with every quadratic coefficient positive and witnesses for both signs of the
normal slope. The objective is the actual finite maximum. No sorted-envelope,
essential-branch, distinct-slope, nonzero-slope, nonzero-coordinate, uniquely
active branch or bounded-run assumption appears in the final theorem. The
accepted run is the existing unmodified full inverse-BFGS run with actual
Fréchet derivatives and only initial positive definiteness.

The family foundation proves convexity, compactness of every sublevel and the
unique minimum at the origin. Every differentiable accepted gradient is derived
from an actual active branch; differentiable ties are allowed.

The five envelope modules construct a selector-free calibrated scale directly
on the compact normalized lower-envelope cells. Canonical duplicate cells are
counted once, singleton/tie-only cells have zero ramp length, and every original
active index has the same calibrated exponent at a tie. This alternative avoids
assuming the source's ordered pruning. It proves the actual Q.7 interface
identity and Q.16 deficit bound for every original pair of indices. Global
positive finite scale bounds and continuity on F>0 are derived. The explicit
ordered-pruning bookkeeping is not a hypothesis of the completed theorem, and
is still tracked separately as a source proof-description assertion.

`ParabolicTransportAlgebra` proves the exact displacement-parallel identity and
Q.15 cancellation. The old-branch exponent increment is replaced by an exact
rational remainder identity. Thus no Taylor estimate, active-index regularity,
or unchecked symbolic computation is imported.

`ParabolicUniformTransport.exists_uniform_log_transport` chooses every constant
before all eligible pairs in a compact set. The two endpoints satisfy F≥η>0.
The already proved Q.13 yields D≠0 and horizontal control, including zero normal
slopes and vanishing horizontal displacements. Explicit estimates give
(λ−1)²≤S d and a threshold d≤1/[4(S+1)], which proves |λ−1|≤1/2 and λ>0.
The actual logarithm remainder and Q.16 then prove Q.17 with C>0. Convexity of
exp gives the finite linear expansion with L=exp(2C)−1≥0 for d≤1. No numerical
approximation to the exponential is used.

`exists_bandCertificate` constructs the actual matrix field
`outer (calibratedVector x) (calibratedVector x)`, exactly θ²rrᵀ. Visibility,
secant suppression and projected transport hold for every small eligible pair
in the entire band. The field is PSD and continuous on F>0; no extension at the
minimizer is claimed. Neither matrix convergence nor invertibility of the
certificate field is required.

`hasBandCertificates` derives Module T's objective condition. The final
`parabolic_convergence` applies the actual run theorem with derived compact
initial sublevel and unique minimum, yielding both objective values→0 and
iterates→(0,0). It does not assert existence of an acceptable step on every ray,
nor nonlinear coordinate invariance of BFGS.

The 24 new transport/assembly declarations (20 theorems, 4 concrete definitions)
pass the scoped actual transitive-axiom audit in
`ParabolicTransportAxiomChecks.lean` / `parabolic_transport_axioms.log`, using only
the three permitted standard axioms. `parabolic_certificate_build.log` records
the actual pinned build. Independent transport review is in
`PARABOLIC_TRANSPORT_PEER_REVIEW.md`; the envelope has its own full statement,
contract and axiom reviews. The separate three-branch example, printed scale
identities and strict RS separation are not inferred merely from this general
convergence theorem.
