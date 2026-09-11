# G source closure with the documented active-span correction

Read all G.tex lines1–283 and every retained-claim inventory row against the
existing audited exports. All retained mathematical conclusions are accounted
for, with one explicit source correction. The unqualified full-active tangent
inference is not asserted as proved. Original source is preserved.

| Source lines | Checked coverage |
|---|---|
| 1–21 | TeX preamble only. |
| 22–54 | Actual EligiblePair/BandCertificate definitions and accepted-run bridge; positive curvature/nonzero step; actual T global/local/solution-set conclusions. |
| 55–75 | certificateNormalization: exact L=0 rescaling equivalence on the same eligible pair domain. |
| 76–98 | ellipsoidCertificateGeometry: actual Euclidean PSD square-root ellipsoid/support and projection/inclusion; projected_matrixRange, range_le_sup_span_of_projected_order, rankOne_direction_mem_plane. |
| 99–128 | pointwiseCertificateCapacity and actual closed absolutely convex hull polar. Extended-real suprema, empty predecessor sets and zero suppression constant are covered; pointwise selections do not assert transport. |
| 129–158 | incomingJumpObstruction, basis-limit coefficient theorem/corollary, eligiblePairRealizability. Common-target endpoint pairs need not be one history; each is individually realized by the actual explicit SPD matrix. |
| 159–183 | Actual common tangential projection and affine-span identity; continuous-field accessible-curvature annihilation; qualified nonzero accessible projection. Full-active projection requires all-difference annihilation. Literal u²+abs(v) geometry is included. |
| 184–205 | scalarCertificateCharacterization with actual positive-band gradient bounds and eligible-pair Lipschitz equivalence, not unrestricted derivative Lipschitzness. |
| 206–227 | scalarMetricConvergence and actual BFGS specialization; literal shifted-absolute-value global nonnecessity at (1/4,1/2). |
| 228–268 | Actual infinite accumulating-kink series, strong convexity/coercivity, exact knot formulas and fixed-knot-then-epsilon crossing argument; scalarLocalCertificateNonnecessity and all-run convergence. |
| 269–283 | finiteSampleFeasibility with the actual constant identity field and free finite constants; no continuum theorem inferred from a finite sample. |

The correction is substantive: the span of accessible limiting gradient jumps
can be smaller than the span of all active-gradient differences. At the actual
shifted-absolute-value nonoptimal kink, parameters (c1,c2)=(1/8,1/4) admit constant
identity certificates on every compact positive band, while all accessible
limiting jumps are zero. The actual active gradients are 1 and3; their full
common tangent space is zero and identity energy is positive. The exact audited
`accessibleActiveSeparation` refutes the unrestricted inference. These parameters
differ from the source's separate (1/4,1/2) no-certificate example, so there is no
conflict. See G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md and
MODULE_G_GEOMETRY_STATEMENT_REVIEW.md.

The correct general theorem concludes tangency to accessible jumps and a nonzero
projection orthogonal to their span. The full-active version retains the
additional spanning/all-difference premise explicitly. The report module status
must therefore say verified with a documented correction, never that the literal
incorrect implication has a Lean proof. The partly smooth interpretation and
bibliographical attribution are background; no theorem for arbitrary active
manifolds is inferred from them.
