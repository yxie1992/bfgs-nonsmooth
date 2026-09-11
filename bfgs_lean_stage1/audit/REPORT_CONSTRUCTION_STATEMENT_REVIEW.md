# Ninth report milestone: actual scalar constructions and objective examples

The new exact targets are `coerciveSeedFailure`, `dScalarFunction`,
`centeredSpectralConvergence`, `singularCurvatureCounterexample`, and the six
`NormalSpike` targets for scalar properties, actual-objective convergence,
radial separation, objective geometry, Hessian peaks, and the rational oracle.
All target definitions are printed in `Audit.lean`; `scripts/check.py` checks
their inhabitants' exact types and the entire compiled theorem environment.
The report-level register remains distinct from declaration verification.

## D's literal constructions

The actual four-piece coercive max-affine objective retains the exact seed
matrices, accepted lengths, gradients, and recursive deterministic search at
every iterate and every rejected query. Its unique optimizer has value -1,
but the actual run tends to the nonstationary origin with positive values
tending to zero. See `COERCIVE_SEED_STATEMENT_REVIEW.md` and its independent
peer review. This is the source's simple global example.

The scalar construction is now the actual global function with all printed
regions. Its infinite geometric-ramp series is proved equal to the source
interval formula. Actual derivative-series summation proves C2 regularity at
zero and every join. The sharp curvature constants, global Lipschitz second
derivative, coercivity, unique minimum, all node jets, and the full closed
affine plateaus are derived. See `D_SCALAR_SERIES_STATEMENT_REVIEW.md`,
`D_SCALAR_SERIES_PEER_REVIEW.md`, and `D_SCALAR_ASSEMBLY_PEER_REVIEW.md`.
No interpolation or smoothness is an input premise. D's separate actual
two-dimensional C2,1 local embedding and L's persistence theorem remain open.

## U's literal infinite spike and executable exact oracle

The source scalar is the actual interval integral of the actual infinite
scaled-polynomial density. Its regularity, exact mass/support geometry,
zero-endpoint second derivative existence, and unbounded Hessian peaks are
checked. The arbitrary-dimensional printed objective has actual strong
convexity, unique minimum, exact nonsmooth interface, tangential supports,
and Hessian peaks. Every actual admissible full-BFGS run converges, while
the radial-secant condition fails on every neighborhood of the optimizer.
No assumed Hessian, iterate limit, or model oracle occurs in these targets.

The computable rational oracle returns exact values and first/second
derivatives for every rational query. Its terminating finite search and
geometric-tail arithmetic are proved equal to the infinite integral-defined
function in Lean. No Python result verifies a mathematical assertion.
See the scalar, example, and rational `NORMAL_SPIKE_*_PEER_REVIEW.md` files.
The variable-jump nonsplitting example remains a separate obligation.

## C's actual transport and R's interpretations

C now has actual buffered field bounds, tangent-preserving derivatives,
uniform tail transversality, determinant calculus, and logarithmic transport
along actual full-BFGS segments. One coherent cutoff/velocity family works
through smooth and corner points. The source-only actual-run wrapper derives
the value limit and vanishing steps and retains positive uniform visibility.
The one-sided derivative comparison replaces an a.e. integration route and
does not assume finitely many crossings. See
`C_ACTUAL_TRANSPORT_VERIFICATION.md`. The crossing secant correction, full
C contradiction, local/example conclusions, and stronger all-eligible-pair
variant remain separate obligations.

R's arbitrary rectangular centered spectral norm is identified with the
actual Euclidean operator norm and the coordinate pairing with Frobenius
pairing; its actual full-BFGS convergence is verified. The actual singular
curvature example has a bounded a.e. classical radial Hessian on a compact
sublevel but fails RS. Norm-scaled IR is proved equivalent on compact positive
bands. General-dimensional nuclear norm identification remains open.

R's older four-piece numerical attribution is inconsistent with the current
D objective and is not recoverable from preserved source/history. The current
objective's supporting heights and actual secant limit, and its failure of
RS/SP on the initial sublevel, are verified instead. The original source is
preserved and the historical attribution explicitly remains unresolved; see
`COERCIVE_SEED_INTERCEPT_CORRECTION.md` and its independent review.

## Completion boundary

This tranche does not establish that the entire report is verified. The
source register retains D/L embeddings and return-map dynamics, C's remaining
endpoint/main consequences, U's variable-jump example, A's remaining compact
gap/semialgebraic infrastructure, R's nuclear and descriptive identities,
historical attributions, and final synthesis/cross-reference reconciliation.
Scratch work on these obligations is excluded from the frozen release.
