# Module R retained-claim inventory

Source `BFGS_MASTER_REPORT_LaTeX/report/chapters/R.tex` has been read in full; its family and boundary examples
remain indexed for formal implementation. This register does not claim full verification.

| Claim | Status and exact remaining work |
|---|---|
| Actual supporting errors, radial numerator and optimizer intercept | Compiled exact definitions/identities in RadialCertificate.lean |
| Positive-band RS sufficient for full-BFGS convergence | Compiled in RadialConvergence.lean; actual correction budget derived; compact/nonunique/Euclidean conclusions in ReportCoreEndToEnd.lean |
| T=D(z,x)+D(x,z), nonnegative errors | Exact identity and convex nonnegativity compiled |
| T≤4GR on bounded K with all subgradients bounded | Compiled: secantCurvature_le_four_mul with derived compact Euclidean radius/gradient bounds |
| R:thm:equiv IR⇔RS | Forward IR→RS compiled, including signed probes and exact scalar optimization. Both-differentiable reverse pair estimate and convex supporting-vector/gradient limit theorem compiled. Joint differentiable approximation and band preservation remain open; inner differentiability may not be added to the final theorem |
| Radial norm-scaled convention equivalence | Open; positive-band lower radius η/G and upper radius R |
| Derivative-free central second-difference equivalence | Open; nested bands and admissible outward dilation scope must remain explicit |
| Optimizer-intercept identity R:eq:intercept | Compiled exactly |
| RS⇔SP with constants 2C+2Tmax | Full pair-quantified equivalence and Tmax bound compiled in RadialEquivalence.lean; constants exactly 2C+2Tmax |
| Homogeneous, u²+abs(v), degree-p intercept examples | Open instantiations; degree-one Euler already available in H |
| Four-piece optimizer/intercept values | Open exact algebra and cross-check with D source; not a replacement for the infinite example |
| R:thm:plq finite polyhedral C1,1 partition theorem | Open: local removal of cells not containing star, derivative agreement at adjacent full-dimensional cells, radial Taylor estimate, RS and basin assembly |
| Finite convex PLQ and smooth-plus-PLQ consequences | Open specializations; do not include arbitrary max-quadratics lacking a polyhedral partition |
| Gauges/mixed powers, polyhedral penalties, Euclidean group residuals | Open detailed family review and exact local hypotheses |
| Finite-max branch test | Open; derivative agreement/active branch and radial estimates |
| Parabolic and spectral boundary examples | Open exact computations and scope review; failure of RS does not assert BFGS failure |

Original source is unchanged. Scalar algebra or a conditional convergence theorem
is never recorded as verifying the still-open objective families or equivalences.
