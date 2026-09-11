# Module G retained-claim inventory

Source read in full: `BFGS_MASTER_REPORT_LaTeX/report/chapters/G.tex`.
This is a source/verification scope register, not a claim that all entries are proved.
Original sources are preserved. Eligible pairs are endpoint data; they are not
assumed to occur in one common BFGS history.

| Source claim | Exact scope and qualifications | Current Lean status |
|---|---|---|
| G.1 condition (E), (V), (S), (T) | Finite convex objective, attained minimum, compact positive band, differentiable endpoints, fixed `0<c1<c2<1`; `d>0`, `c1*d≤Δ≤d`, `t≥(1-c2)*d`. Finite-valued PSD field can be singular, discontinuous and unbounded on the band. The pair conditions hold uniformly for every eligible pair with `d≤δ`. | Actual endpoint and band definitions are verified in `TransportedCertificateDefinitions.lean`; the accepted-run bridge is verified in `TransportedCertificateRun.lean`. |
| G.2 exact nonexpansion normalization | The existential transported condition is equivalent to `L=0`, by multiplying the field by `exp((L/c1)*(F-F*))`. Compact value bounds preserve visibility and incoming-jump constants. No domain/pair assumption is added. | Checked in `TransportedNormalization.lean`; `certificateNormalization` is an audited exact target. |
| G.2 ellipsoid/support interpretation | PSD square-root image of the closed unit ball; support function `sqrt(aᵀWa)`. Projected PSD comparison is equivalent to projected ellipsoid inclusion. | Pending. |
| G.2 necessary range inclusion | `range W(z) ⊆ range W(x)+span{s}` from the projected Loewner comparison. Rank-one new direction lies in the plane of the old direction and executed step. | Pending. |
| G.3 exact pointwise visibility/suppression feasibility | `(V),(S)` alone iff `inf_z ν(z)>0`, with normalized incoming jumps defining the polar set. Rank-one selections suffice. Handle `C=0`, empty predecessor sets, unbounded suprema, and no continuity of selections. Does not conclude transport. | Pending. |
| G.3 incoming-jump obstruction | Finitely many eligible common-target incoming jumps with vanishing predicted decreases span the target gradient with `Σ|λ_j|sqrt(t_j)→0`. No PSD field can satisfy uniform `(V),(S)` on that band. No field continuity/boundedness or common trajectory is assumed. | Compiler-checked in `IncomingJumpObstruction.lean`: `incoming_jump_no_visibility_secant` excludes (V),(S) alone; `incoming_jump_no_band_certificate` excludes the full certificate. Actual finite PSD weighted-sum inequality, arbitrary nontrivial limiting filter, and eventual representation are proved. Own axiom audit uses only propext/Classical.choice/Quot.sound; full-project integration and axiom audit passed. |
| G.3 basis-limit corollary | A full basis of limiting incoming jumps, vanishing curvature products, and bounded endpoint gradients force bounded representation coefficients and the incoming-jump obstruction. | Compiler-checked in `IncomingJumpObstruction.lean`: `basis_limit_coefficients`, `basis_limit_no_visibility_secant`, and `basis_limit_no_band_certificate`. Matrix inverses and bounded coefficients are derived; target gradients need not converge. Full-project integration and axiom audit passed. |
| G.3 individual eligible-pair realizability | For `d=-gᵀs>0`, `H=ssᵀ/d+I-ggᵀ/(gᵀg)` is SPD and `Hg=-s`; alpha one realizes each eligible pair separately. Does not join all predecessors into a trajectory. | Compiled in PairRealizability.lean; eligiblePairRealizability has the exact actual SPD/unit-step conclusion, with the original predicted decrease. |
| G.4 tangent/normal geometry | Common tangential projection of limiting active gradients; continuous finite extension of a certificate plus accessible vanishing-curvature pairs forces annihilation of accessible jumps. Zero common tangent gradient iff zero lies in affine hull. Continuity/accessibility are explicit qualifications, not general certificate hypotheses. | Pending. |
| G.6 exact scalar certificate characterization | On compact positive bands, scalar transport vanishes. Certificate existence iff eligible small-decrease derivative-jump quotient is uniformly bounded, equivalently Lipschitz on those eligible pairs. Gradient upper/lower bounds are required for the equivalence; no all-pair Lipschitz conclusion. | Compiler-checked in `ScalarCertificate.lean`: `scalar_certificate_iff_quotient` and `scalar_certificate_iff_eligible_lipschitz`. Actual gradient nonvanishing and compact-band upper/lower bounds are derived; the inverse-gradient-square PSD field is explicit. Own build and axiom audit passed; full-project integration and axiom audit passed. |
| G.6 scalar convergence independent of BFGS updates | Every infinite accepted differentiable-iterate Armijo–weak-Wolfe run using an arbitrary positive scalar metric converges to the attained unique minimizer on a compact initial sublevel. No update/matrix limit assumption. | Compiler-checked in `ScalarConvergence.lean`; `ScalarMetricRun.convergence` proves the update-free result, and `AdmissibleBFGSRun.scalar_convergence` proves its exact dimension-one specialization. Integrated in milestone `0c173ea`; full-project axiom audit passed. |
| G.6 shifted quadratic plus absolute-value example | `f(x)=(x+2)^2/2+|x|`: strong convexity, unique minimizer, scalar global convergence, but no certificate on a positive band around zero. Exact small crossing values/derivatives/eligibility at `(c1,c2)=(1/4,1/2)` and divergent quotient must be checked. | Compiled in ScalarCounterexamples.lean; actual derivatives, strict eligibility, literal quotient divergence, fixed-sublevel certificate nonexistence and all-run convergence. See SCALAR_NONNECESSITY_REVIEW.md. |
| G.7 accumulating-kink example | `h(x)=x²/2+3Σ_{j≥1}4^{-j}(x-4^{-j})_+`: finite/strongly convex/coercive, unique minimizer zero; compact-uniform convergence, exact geometric-sum formulas, knot derivatives `2a,5a`, knot value `13a²/10`. | Compiled in AccumulatingKinks.lean; actual infinite series, compact-uniform convergence, strong convexity, standard coercivity, exact knot values/one-sided derivatives and optimizer regularity. |
| G.7 local certificate nonnecessity | For each fixed knot first, then epsilon tending to zero: eligible crossings have divergent scalar quotient. Every neighborhood of zero contains such a fixed knot, so no local certificate condition holds, while every admissible scalar run converges. Band-dependent constants cannot repair divergence at a fixed knot. | Compiled in AccumulatingKinks.lean; every_neighborhood_no_certificates preserves the fixed-knot-then-epsilon quantifiers. Both scalar metrics and actual BFGS converge. |
| G.9 finite-sample feasibility | Any finite sample of nonstationary differentiable endpoints and eligible pairs admits constant `W=I` with some uniform positive visibility and finite suppression constants; transport is equality. Empty samples require separate harmless constant choices. | Compiled in FiniteSampleCertificates.lean; explicit identity PSD field, finite positive visibility and suppression constants, exact projected transport, empty samples included. |
| G.9 limits of numerical feasibility | Free-constant finite-sample feasibility cannot establish continuum certificate nonexistence or existence; analytic limiting families or fixed a priori constants are required. | Interpretive consequence of the compiled finite-sample theorem; no continuum conclusion is inferred from finite success. |

No theorem about universal line-search existence or all-ray finite oracle
complexity is claimed. Source section-number gaps are preserved; they do not
represent missing pages or omitted retained claims.

Third tranche: individual eligible-pair realization and free-constant finite sample feasibility are compiled in PairRealizability/FiniteSampleCertificates. Both literal scalar nonnecessity examples are compiled in ScalarCounterexamples/AccumulatingKinks, including strong convexity, exact crossing quotients and all-run convergence; the accumulating example fails certificates in every neighborhood. See SCALAR_NONNECESSITY_REVIEW.md and G_PAIR_FINITE_SAMPLE_PEER_REVIEW.md. The ellipsoid/range, pointwise feasibility and tangent/normal claims remain open.

Fourth milestone: literal Euclidean ellipsoid/range geometry, extended-real
pointwise capacity and closed absolutely convex hull polar, and precise
accessible-limit/tangent implications are compiled and fully audited. The G.4
all-active versus accessible-span qualification is documented in
MODULE_G_GEOMETRY_STATEMENT_REVIEW.md. The source's illustrative/partly-smooth
narrative is not silently relabeled as a general theorem. Root
AccessibleCurvatureBridge derives d→0 from t→0, so the actual continuous-field
annihilation wrapper retains only the source curvature-limit premise.

Fifth milestone: the G.4 full-active versus accessible-span distinction now has
an actual objective counterexample in ShiftedAbsAccessibility. For shiftedAbs
and (c1,c2)=(1/8,1/4), all sufficiently small eligible pairs remain on one smooth
side, yielding constant-I certificates on every compact positive band. Actual
limiting gradients 1 and 3 at the nonoptimal kink have zero full-active tangent
projection and positive I energy. Every accessible limiting jump is zero.
This does not contradict the earlier no-certificate result at (1/4,1/2).
See G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md and exact accessibleActiveSeparation.
