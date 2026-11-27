# Article to Lean 4 map

This file maps the research article in [`paper/`](./paper/) (the 53-page
`paper/build/master.pdf`, November 2026 edition) to its Lean 4 formalization. It has
two parts: a guide to how the article's basic objects are represented in Lean and
why the representation is faithful, and an index of all 38 numbered statements
with their TeX source, their coverage theorem and the library theorems behind it.

Every claim of the article, not only the numbered statements, is listed in the
coverage registers [`editorial/lean_coverage/register/A_*.json`](./editorial/lean_coverage/register/)
(561 items: 236 `LEAN`, 52 `DEFINITION`, 39 `PART_OF`, 37 `PROOF`, 127 `SAME_AS`,
4 `OPEN`, 66 `NON_CLAIM`, no `DISCREPANCY` and no `TODO`). The method is described in
[`editorial/lean_coverage/README.md`](./editorial/lean_coverage/README.md); the check is

    python3 editorial/lean_coverage/check_coverage.py --strict

The coverage theorems live in
[`bfgs_lean_article/BfgsArticle/Coverage/Article/`](./bfgs_lean_article/BfgsArticle/Coverage/Article/),
one module per TeX file, namespace `BfgsCoverage.Article.<Module>`. Each restates the
claim with its hypotheses, quantifiers and constants written out, and is proved from
the main library `BfgsVerification` ([`bfgs_lean_stage1/`](./bfgs_lean_stage1/)) and the
article package ([`bfgs_lean_article/BfgsArticle/`](./bfgs_lean_article/BfgsArticle/)).
No coverage theorem uses `sorry`, `admit`, an added axiom, `native_decide` or `unsafe`;
the axiom audit of [`bfgs_lean_article/README.md`](./bfgs_lean_article/README.md) checks that
every exported theorem depends at most on `propext`, `Classical.choice` and `Quot.sound`.

## 1. Core definitions and semantic fidelity

The table gives, for each object of the article, its Lean form and the reason the
two agree. Line links point at the definitions.

| Article | Lean | Why they agree |
|:--|:--|:--|
| $\mathbb{R}^n$, $x^Ty$, $\lVert x\rVert^2$ | [`Vec n := Fin n → ℝ`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L21), [`dot`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L24) $=\sum_i x_iy_i$, [`sqNorm`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L26) $=\sum_i x_i^2$ | Inner products and squared norms are the explicit Euclidean sums. Mathlib's norm on `Vec n` is the sup norm; it is used only where the article's statement is topological (limits, open sets, compactness, coercivity, differentiability, local Lipschitz continuity), which do not depend on the choice of norm in finite dimension, and where the article itself uses $\lVert\cdot\rVert_\infty$ (the root box of Lemma 9). Every metric constant stated with the Euclidean norm (Lipschitz constants, balls $B_\rho(x_*)$, query radii, distances to $\arg\min F$) is stated with [`euclideanVector`](bfgs_lean_stage1/BfgsVerification/CompactConvergence.lean#L91) (the isometric copy in `EuclideanSpace ℝ (Fin n)`) or with `sqNorm`. |
| $F$ differentiable at $x$ with $\nabla F(x)=g$ | `HasFDerivAt F (gradientFunctional g) x`, [`gradientFunctional g`](bfgs_lean_stage1/BfgsVerification/ObjectiveDefinitions.lean#L21) $=\sum_i g_i\,\mathrm{proj}_i$, so `gradientFunctional g v = dot g v` | This is Fréchet differentiability with derivative $v\mapsto g^Tv$, which is the article's $\nabla F(x)=g$ (the Fréchet derivative does not depend on the norm). Where a gradient is computed from $F$, [`coordinateGradient F x`](bfgs_lean_stage1/BfgsVerification/ConvexDifferentiability.lean#L28) is the vector of partial derivatives of `fderiv ℝ F x`, and `hasFDerivAt_coordinateGradient` returns the first form at differentiable points. |
| $\partial F(x)$ for finite convex $F$ | [`ConvexSubdifferential.subdifferential F x`](bfgs_lean_stage1/BfgsVerification/ConvexSubdifferential.lean#L16) $=\{g:\forall z,\ g^T(z-x)\le F(z)-F(x)\}$ | The global convex subdifferential. For a finite convex function on $\mathbb{R}^n$ it equals the Clarke subdifferential and the limiting subdifferential, so no choice is hidden. $0\in\partial F(x)$ is minimality of $x$. |
| Admissible run (Definition 1) | [`AdmissibleBFGSRun n F`](bfgs_lean_stage1/BfgsVerification/ObjectiveDefinitions.lean#L30) | Fields: `ConvexOn ℝ univ F` (finite convex $F$); $H_0\succ0$; $\alpha_k>0$; $g_k\ne0$ and `HasFDerivAt F (gradientFunctional (g k)) (x k)` (differentiable iterates with actual gradients); $x_{k+1}=x_k+s_k$ with [`bfgsStep H g α`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L33) $=-\alpha Hg$; $H_{k+1}=$ [`inverseBFGS H s y`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L36), literally the update display of Definition 1 with $t=y^Ts$; Armijo $F(x_{k+1})\le F(x_k)+c_1g_k^Ts_k$ and weak Wolfe $g_{k+1}^Ts_k\ge c_2g_k^Ts_k$, both non-strict as in the article; $0<c_1<c_2<1$. The run is infinite (indexed by `ℕ`), and the update is never reset or rescaled. `inverseBFGS` would return a junk value if $t=0$, but $t_k>0$ is proved from weak Wolfe and $g_k\ne0$ (`curvature_pos`). The primal update $B_{k+1}=B_k-g_kg_k^T/q_k+y_ky_k^T/t_k$ of the article is the theorem [`AdmissibleBFGSRun.hessian_update`](bfgs_lean_stage1/BfgsVerification/ObjectiveEnergy.lean#L29) for $B_k=H_k^{-1}$. [`FullBFGSRun`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L59) is the same update without an objective, used for the matrix identities. The coverage theorem `Energy.admissible_iff` unfolds the structure to the displayed definition. |
| Unit-first Armijo and weak-Wolfe bracketing search (Section 5.1, Lewis and Overton, Algorithm 4.6) | [`NonStrictLineSearch.fromMetric F x H c₁ c₂ N`](bfgs_lean_stage1/BfgsVerification/NonStrictLineSearch.lean#L33), via [`search`](bfgs_lean_stage1/BfgsVerification/NonStrictLineSearch.lean#L18) | Direction $p=-Hg$ with $g=\nabla F(x)$; $\alpha_{\rm lo}=0$, $\alpha_{\rm hi}=+\infty$, first trial $\alpha=1$; Armijo is tested first, then weak Wolfe, both non-strict; an Armijo failure sets $\alpha_{\rm hi}=\alpha$, a Wolfe failure sets $\alpha_{\rm lo}=\alpha$; the next trial is $(\alpha_{\rm lo}+\alpha_{\rm hi})/2$ if $\alpha_{\rm hi}<\infty$ and $2\alpha_{\rm lo}$ otherwise. The result is the accepted length and the complete list of trials, so every theorem states the whole decision tree. The search is fuel-bounded; the theorems hold for every budget $N\ge5$ (`fromMetric_fuel_mono`). At a nondifferentiable trial point the Wolfe test would read a zero gradient; the failure theorems prove that every queried point is differentiable and lies in the open interior of one piece, with strict margins, so the search coincides there with the strict and the non-strict versions of Algorithm 4.6, as the article states. |
| Eligible pair, $\Pi_s$ | [`TransportedCertificate.EligiblePair`](bfgs_lean_stage1/BfgsVerification/TransportedCertificateDefinitions.lean#L20), [`stepProjector s`](bfgs_lean_stage1/BfgsVerification/TransportedCertificateDefinitions.lean#L31) $=I-ss^T/\lVert s\rVert^2$ | Actual gradients at both points, $d>0$, $c_1d\le\Delta\le d$, $t\ge(1-c_2)d$: the display of Section 2.3 with $\omega=1-c_2$. The projector is the Euclidean one. |
| Band certificate (Definition 2) | [`TransportedCertificate.BandCertificate`](bfgs_lean_stage1/BfgsVerification/TransportedCertificateDefinitions.lean#L38), [`HasBandCertificates`](bfgs_lean_stage1/BfgsVerification/TransportedCertificateDefinitions.lean#L64) | A field $W$ that is positive semidefinite (Mathlib's `PosSemidef`, which includes symmetry) at differentiable points of the band $K_\eta=\{x\in K:F(x)\ge F_*+\eta\}$, and constants $m>0$, $L\ge0$, $\delta>0$ with visibility $g^TWg\ge m$, secant control $y^TW(z)y\le Ct$ and transport $\Pi_sW(z)\Pi_s\preceq(1+Ld)\Pi_sW(x)\Pi_s$ on eligible pairs with $d\le\delta$. The library structure omits $C\ge0$; the coverage theorem `Energy.bandCertificate_iff` adds it, so the Lean notion is exactly the article's. Empty bands need no certificate, as in the article ("each nonempty band"). |
| Radial secant condition (14) and inward model condition (15) | [`RadialCertificate.HasRadialSecantBounds`](bfgs_lean_stage1/BfgsVerification/RadialCertificate.lean#L34), [`RadialCertificate.HasInwardTaylorBounds`](bfgs_lean_stage1/BfgsVerification/InwardRadial.lean#L16) | For every band $\eta>0$ a constant bounds $((h-g)^T(z-x_*))^2\le C_\eta\,t$, respectively $0\le F(x-\tau r_x)-F(x)+\tau\nabla F(x)^Tr_x\le\frac{M_\eta}{2}\tau^2$ for $0\le\tau\le\theta_\eta\le1/2$, at differentiable points only; the inward point need not be differentiable. |
| $C^{1,1}_{\rm loc}(V)$, $C^{2,1}$, classical Hessian, $\mu$-strong convexity | [`CenteredSmoothSublinear.LocallyC11On V f`](bfgs_lean_stage1/BfgsVerification/CenteredSmoothCalculus.lean#L13) (differentiable on $V$ with locally Lipschitz derivative); `ContDiff ℝ 2` with a Hessian that is Lipschitz in the Euclidean operator norm; [`RadialHessian.matrix`](bfgs_lean_stage1/BfgsVerification/RadialHessian.lean#L59) (matrix of `fderiv ℝ (fderiv ℝ F) x`); [`FixedNormal.EuclideanStrongConvexOn U μ F`](bfgs_lean_stage1/BfgsVerification/FixedNormalStrongConvex.lean#L16) ($F-\frac\mu2\lVert\cdot\rVert^2$ convex) | Local Lipschitz continuity is norm-independent; the quantitative $C^{2,1}$ and strong convexity constants are Euclidean. A "twice-differentiable point" is one where $F$ is differentiable on a neighborhood and its derivative map is differentiable, the convention of the caption of Table 3. |
| Affine criticality $0\in\mathrm{aff}\,\partial F(p)$ and planar two-branch regularity | [`AffineCriticalObjective.IsAffineCritical F p`](bfgs_lean_stage1/BfgsVerification/AffineCriticalObjective.lean#L16), `PlanarCornerCharts.ConvexTwoBranchRegularAt` ([`PlanarConvexCorner.lean`](bfgs_lean_stage1/BfgsVerification/PlanarConvexCorner.lean#L12)) | `IsAffineCritical` is membership of $0$ in the affine span of the Euclidean copy of $\partial F(p)$, which is $0\in\mathrm{aff}\,\partial F(p)$ (the copy is a linear isometric equivalence). Two-branch regularity: on an open $U\ni x$, $F=\max\{f_1,f_2\}$ with convex $C^2$ branches, both active at $x$, with linearly independent gradients (nonzero $2\times2$ determinant), as in Theorem 8. |
| Finite closed full-dimensional polyhedral partition (Theorem 7) | cells $P_i=\{x: a_{ij}^Tx\le b_{ij}\ \forall j\}$ ([`ConvexCellRadial.polyhedron`](bfgs_lean_stage1/BfgsVerification/ConvexCellRadial.lean#L159)) indexed by a `Fintype`, with nonempty interiors, covering $U$, and $F=f_i$ on $U\cap P_i$ with $f_i\in C^{1,1}_{\rm loc}(V_i)$ | Exactly the hypotheses of Theorem 7; $\varepsilon$ is chosen before the run, so it does not depend on $H_0$, $c_1$, $c_2$. The library theorem does not need full dimensionality, which the coverage theorem carries as an unused hypothesis. |
| Scalar splines $\varphi_b$ (Lemma 6) and $\psi_b$ (Appendix D.3) | [`DScalar.phi`](bfgs_lean_stage1/BfgsVerification/DScalarAssembly.lean#L55), [`LScalar.phi`](bfgs_lean_stage1/BfgsVerification/LScalarAssembly.lean#L47) | The coverage modules prove that the library functions are given by the article's formulas (nodes, slopes, plateaus, cubic ramps and primitives) and have the stated regularity: $C^{2,1}$ for $\varphi_b$, $C^{1,1}$ and not twice differentiable at $0$ for $\psi_b$. |
| Root isolation polynomial $P(c,d)$ and the rational certificate (Appendix C) | [`AlgebraicSeed.P`](bfgs_lean_stage1/BfgsVerification/AlgebraicSeedData.lean#L14) with factors `U, V, R, K, T, Y`; interval rules [`IntervalBounds`](bfgs_lean_stage1/BfgsVerification/IntervalBounds.lean) | $P$ is the article's two cleared polynomial equations. The root box is the sup-norm box of radius $10^{-30}$ about the rational center, as printed. Interval arithmetic is proved sound in the kernel (`SeedCertificate.interval_rules`); the nine queries of Table 2 are certified by interval bounds with rational endpoints checked in the Lean kernel (`norm_num`), not by floating point. |
| Five-dimensional return map $\mathcal{T}_\mu$ and its stable manifold (Appendix D.2) | [`LNormalizedReturn.returnMap μ`](bfgs_lean_stage1/BfgsVerification/LNormalizedReturn.lean#L39) on [`State := Vec 5`](bfgs_lean_stage1/BfgsVerification/LNormalizedReturn.lean#L13) | Three inverse-BFGS substeps with lengths $1,1/4,1/16$ at fixed scale $\tau$, then normalization by $\hat{\rho} = M_{3,11}$, matching the display defining $\mathcal{T}_\mu$. The stable-manifold statement (`LowerCurvature.stable_manifold_positive_scale`) is proved in Lean by constructing the stable orbits; the classical theorem cited in the article is not imported. |
| $\mathrm{dist}(x,\arg\min F)$ | [`euclideanSolutionDistance F x`](bfgs_lean_stage1/BfgsVerification/CompactConvergence.lean#L96) | Euclidean distance to the minimizer set. |
| Open problems 1 to 4 (Section 6) | `Verification.C2StronglyConvexLocalFailure`, `Verification.NondegenerateSmoothMaxLocalConvergenceHigherDim`, `Verification.ConvexPositiveMeasureFailure`, `Verification.MixedBenchmarkRLinear` | Each question is a Lean `Prop` stated without proof (status `OPEN`). |

### Why there are no specification gaps

- Hypotheses are never strengthened silently: each coverage theorem states the article's
  hypotheses as written (unused ones carry a leading `_`). Where a module states results
  under standing assumptions (for instance the displays inside proofs), an `example` at its end
  shows that these assumptions can hold at once, so no statement is vacuous; the other
  statements are about explicit objectives, runs and certificates.
- Quantifier order follows the article: constants chosen "before the run" (the basin
  $\varepsilon$ of Theorems 7 and 9, the certificate data of Definition 2) are existentially
  quantified before the run, and the failure theorems quantify the objective, the starts and
  $H_0=I$ before the pair $(c_1,c_2)$.
- The tests are the article's: Armijo with $\le$ and weak Wolfe with $\ge$; the failure runs
  are shown to have strict margins, so strict tests give the same runs.
- The places where a junk value of a total Lean function could matter are excluded:
  runs carry actual derivatives (`HasFDerivAt`), the specified search is applied only along
  runs whose queries are proved differentiable, and `inverseBFGS` is applied with $t>0$.
- Norm-dependent constants are Euclidean. The sup norm of `Vec n` appears in statements that
  do not depend on the norm, in the article's own $\lVert\cdot\rVert_\infty$ boxes, and in
  "for every $\varepsilon>0$ there is a start within $\varepsilon$" statements, where it makes no
  difference.

## 2. The 38 numbered statements

Numbering as in `paper/build/master.pdf`: Definitions 1 to 2, Lemmas 1 to 11,
Propositions 1 to 5, Theorems 1 to 12 and Corollaries 1 to 8, in order of appearance.
Sections 1 (Introduction) and 6 (Synthesis and open problems) contain no numbered
statements; their claims are covered by prose items of `A_introduction.json` and
`A_verification.json`. The coverage declarations are in the namespace
`BfgsCoverage.Article`, which the table omits. Each line range is that of the statement's
environment in the TeX source; the register item has the id
`A/<file stem>/<kind>/<label>`.

### Section 2. Analytical framework: principal minors and comparison energies

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Definition 1** (Admissible runs) | `art:admissible`<br>[`paper/sections/energy.tex:26-45`](paper/sections/energy.tex#L26-L45) | [`Energy.admissible_iff`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L228), [`Energy.update_formula`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L308) | [`BfgsVerification.AdmissibleBFGSRun`](bfgs_lean_stage1/BfgsVerification/ObjectiveDefinitions.lean#L30), [`BfgsVerification.inverseBFGS`](bfgs_lean_stage1/BfgsVerification/Definitions.lean#L36) |
| **Lemma 1** (Primal–dual invariants) | `art:run-invariants`<br>[`paper/sections/energy.tex:61-74`](paper/sections/energy.tex#L61-L74) | [`Energy.primal_dual_invariants`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L1726) | [`BfgsVerification.AdmissibleBFGSRun.positive_invariants`](bfgs_lean_stage1/BfgsVerification/ObjectiveRun.lean#L18), [`BfgsVerification.AdmissibleBFGSRun.predicted_decrease_bounds`](bfgs_lean_stage1/BfgsVerification/ObjectiveRun.lean#L117) |
| **Lemma 2** (Reference energy identity) | `art:reference-energy`<br>[`paper/sections/energy.tex:99-115`](paper/sections/energy.tex#L99-L115) | [`Energy.reference_energy`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L409) | [`BfgsVerification.AdmissibleBFGSRun.fixed_reference_energy`](bfgs_lean_stage1/BfgsVerification/ObjectiveEnergy.lean#L60), [`BfgsVerification.AdmissibleBFGSRun.fixed_reference_energy_bound`](bfgs_lean_stage1/BfgsVerification/ObjectiveEnergy.lean#L89) |
| **Theorem 1** (Principal-minor hierarchy) | `art:minor-hierarchy`<br>[`paper/sections/energy.tex:156-168`](paper/sections/energy.tex#L156-L168) | [`Energy.minor_hierarchy`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L653) | [`BfgsVerification.principalMinorHierarchy`](bfgs_lean_stage1/BfgsVerification/PrincipalHierarchy.lean#L53), [`BfgsVerification.inverseBFGS_step_det_beta`](bfgs_lean_stage1/BfgsVerification/HessianUpdate.lean#L177) |
| **Theorem 2** (Universal reciprocal growth) | `art:reciprocal-growth`<br>[`paper/sections/energy.tex:203-209`](paper/sections/energy.tex#L203-L209) | [`Energy.reciprocal_growth`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L780) | [`BfgsVerification.objectiveReciprocalGrowth`](bfgs_lean_stage1/BfgsVerification/ObjectiveEndToEnd.lean#L21), [`BfgsVerification.reciprocalGrowth`](bfgs_lean_stage1/BfgsVerification/EndToEnd.lean#L28) |
| **Definition 2** (Band certificate) | `art:band-certificate`<br>[`paper/sections/energy.tex:275-290`](paper/sections/energy.tex#L275-L290) | [`Energy.bandCertificate_iff`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L1159), [`Energy.hasBandCertificates_iff`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L1196) | [`BfgsVerification.TransportedCertificate.BandCertificate`](bfgs_lean_stage1/BfgsVerification/TransportedCertificateDefinitions.lean#L38), [`BfgsVerification.TransportedCertificate.HasBandCertificates`](bfgs_lean_stage1/BfgsVerification/TransportedCertificateDefinitions.lean#L64) |
| **Theorem 3** (Convergence from band certificates) | `art:certificate`<br>[`paper/sections/energy.tex:298-307`](paper/sections/energy.tex#L298-L307) | [`Energy.certificate`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L1347) | [`BfgsVerification.transportedCertificateConvergence`](bfgs_lean_stage1/BfgsVerification/ReportCoreEndToEnd.lean#L9) |
| **Lemma 3** (Tail vector comparison) | `art:tail-comparison`<br>[`paper/sections/energy.tex:347-360`](paper/sections/energy.tex#L347-L360) | [`Energy.tail_vector_comparison`](bfgs_lean_article/BfgsArticle/Coverage/Article/Energy.lean#L1696) | [`BfgsVerification.AdmissibleBFGSRun.scalar_frame_tail_incompatible`](bfgs_lean_stage1/BfgsVerification/ScalarTransportEnergy.lean#L153) |

### Section 3. Global convergence: mixed benchmarks, inward models, and homogeneous geometry

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Corollary 1** (Whole-sequence convergence on $u^2+\lvert v\rvert$) | `art:mixed-benchmark`<br>[`paper/sections/global.tex:18-24`](paper/sections/global.tex#L18-L24) | [`Global.mixed_benchmark`](bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean#L1277) | [`ArticlePositive.mixed_benchmark_global`](editorial/narrative_rebuild/positive_formal/MixedBenchmark.lean#L45) |
| **Theorem 4** (Inward models control radial secants) | `art:radial-equivalence`<br>[`paper/sections/global.tex:97-101`](paper/sections/global.tex#L97-L101) | [`Global.radial_equivalence`](bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean#L628) | [`BfgsVerification.RadialCertificate.radial_of_inward_on_compact`](bfgs_lean_stage1/BfgsVerification/InwardRadial.lean#L93) |
| **Corollary 2** (Radial convergence) | `art:radial-convergence`<br>[`paper/sections/global.tex:143-148`](paper/sections/global.tex#L143-L148) | [`Global.radial_convergence`](bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean#L706) | [`BfgsVerification.AdmissibleBFGSRun.radial_certificate_convergence_on_sublevel`](bfgs_lean_stage1/BfgsVerification/RadialConvergence.lean#L75), [`BfgsVerification.inwardCertificateConvergence`](bfgs_lean_stage1/BfgsVerification/ReportGeometryEndToEnd.lean#L22) |
| **Theorem 5** (Centered smooth-plus-homogeneous objectives) | `art:centered`<br>[`paper/sections/global.tex:176-187`](paper/sections/global.tex#L176-L187) | [`Global.centered`](bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean#L1138) | [`BfgsVerification.AdmissibleBFGSRun.centered_values`](bfgs_lean_stage1/BfgsVerification/CenteredSmoothSublinear.lean#L87), [`BfgsVerification.AdmissibleBFGSRun.centered_iterates`](bfgs_lean_stage1/BfgsVerification/CenteredSmoothSublinear.lean#L107) |
| **Theorem 6** (Coercive positively homogeneous objectives) | `art:homogeneous`<br>[`paper/sections/global.tex:225-233`](paper/sections/global.tex#L225-L233) | [`Global.homogeneous`](bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean#L1557) | [`BfgsVerification.AdmissibleBFGSRun.homogeneous_coercive_iterates_zero`](bfgs_lean_stage1/BfgsVerification/HomogeneousConsequences.lean#L101) |
| **Corollary 3** (Norms, gauges, and coercive linear maxima) | `art:homogeneous-examples`<br>[`paper/sections/global.tex:247-257`](paper/sections/global.tex#L247-L257) | [`Global.homogeneous_examples_norm`](bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean#L1636) | [`BfgsVerification.AdmissibleBFGSRun.norm_conclusion`](bfgs_lean_article/BfgsArticle/HomogeneousModels.lean#L42), [`BfgsVerification.AdmissibleBFGSRun.gauge_conclusion`](bfgs_lean_article/BfgsArticle/HomogeneousModels.lean#L58) |

### Section 4. Local convergence: polyhedral partitions and curved planar interfaces

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Lemma 4** (Matrix-independent sublevel basin) | `art:localization`<br>[`paper/sections/local.tex:22-29`](paper/sections/local.tex#L22-L29) | [`Local.localization_coercive`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L189) | [`BfgsVerification.Localization.sublevel_compact`](bfgs_lean_stage1/BfgsVerification/Localization.lean#L135), [`BfgsVerification.Localization.neighborhood_basin`](bfgs_lean_stage1/BfgsVerification/Localization.lean#L164) |
| **Theorem 7** (Local convergence on finite polyhedral partitions) | `art:polyhedral`<br>[`paper/statements/positive_partition.tex:1-16`](paper/statements/positive_partition.tex#L1-L16) | [`PositivePartition.polyhedral`](bfgs_lean_article/BfgsArticle/Coverage/Article/PositivePartition.lean#L58) | [`BfgsVerification.ConvexCellRadial.finite_polyhedral_basin`](bfgs_lean_stage1/BfgsVerification/ConvexCellRadial.lean#L192), [`BfgsVerification.ConvexCellRadial.local_cells_basin`](bfgs_lean_stage1/BfgsVerification/ConvexCellRadial.lean#L131) |
| **Corollary 4** (Piecewise linear-quadratic and composite objectives) | `art:plq`<br>[`paper/sections/local.tex:82-88`](paper/sections/local.tex#L82-L88) | [`Local.plq`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L598) | [`BfgsVerification.ConvexCellRadial.piecewise_quadratic_basin`](bfgs_lean_stage1/BfgsVerification/QuadraticCellRadial.lean#L61), [`BfgsVerification.ConvexCellRadial.smooth_plus_piecewise_quadratic_basin`](bfgs_lean_stage1/BfgsVerification/QuadraticCellRadial.lean#L76) |
| **Corollary 5** (Local smooth-plus-homogeneous basin) | `art:local-centered`<br>[`paper/sections/local.tex:101-108`](paper/sections/local.tex#L101-L108) | [`Local.local_centered`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L941) | [`BfgsVerification.CenteredSmoothSublinear.local_centered_basin`](bfgs_lean_stage1/BfgsVerification/CenteredSmoothSublinear.lean#L123) |
| **Theorem 8** (Affine-critical cluster points in the plane) | `art:planar-cluster`<br>[`paper/sections/local.tex:202-215`](paper/sections/local.tex#L202-L215) | [`Local.planar_cluster`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L1669) | [`BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster_on_sublevel`](bfgs_lean_stage1/BfgsVerification/PlanarConvergence.lean#L14), [`BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster`](bfgs_lean_stage1/BfgsVerification/PlanarSecantRun.lean#L83) |
| **Corollary 6** (Planar convergence when affine criticality implies optimality) | `art:planar-convergence`<br>[`paper/sections/local.tex:247-252`](paper/sections/local.tex#L247-L252) | [`Local.planar_convergence`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L1872) | [`BfgsVerification.AdmissibleBFGSRun.planar_convergence_on_sublevel`](bfgs_lean_stage1/BfgsVerification/PlanarConvergence.lean#L34) |
| **Corollary 7** (Nondegenerate planar smooth maxima) | `art:planar-max`<br>[`paper/sections/local.tex:268-283`](paper/sections/local.tex#L268-L283) | [`Local.planar_max`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L1956) | [`BfgsVerification.PlanarMaxRegular.finite_max_local_basin`](bfgs_lean_stage1/BfgsVerification/PlanarFiniteMaxBasin.lean#L12), [`BfgsVerification.PlanarMaxRegular.finite_max_hessian_local_basin`](bfgs_lean_stage1/BfgsVerification/PlanarMaxHessianBasin.lean#L62) |
| **Theorem 9** (Explicit convergence basin with curved, nonradial switching) | `art:nonradial-example`<br>[`paper/sections/local.tex:323-337`](paper/sections/local.tex#L323-L337) | [`Local.nonradial_example`](bfgs_lean_article/BfgsArticle/Coverage/Article/Local.lean#L2505) | [`BfgsVerification.PlanarQuadraticExample.fullBFGS_explicit_basin`](bfgs_lean_stage1/BfgsVerification/PlanarQuadraticConvergence.lean#L63), [`BfgsVerification.PlanarQuadraticExample.eligible_radial_unbounded_on_neighborhood`](bfgs_lean_stage1/BfgsVerification/PlanarQuadraticSeparation.lean#L52) |

### Section 5. Deterministic failure: self-similar cycles and local embeddings

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Lemma 5** (Exact cycle closure and strict trial margins) | `art:seed_cycle`<br>[`paper/sections/failure.tex:111-132`](paper/sections/failure.tex#L111-L132) | [`Failure.seed_cycle`](bfgs_lean_article/BfgsArticle/Coverage/Article/Failure.lean#L690) | [`BfgsVerification.SeedCycle.source_cycle`](bfgs_lean_stage1/BfgsVerification/AlgebraicSeedCycle.lean#L202), [`BfgsVerification.SeedOrbit.source_metric_posDef`](bfgs_lean_stage1/BfgsVerification/AlgebraicSeedOrbitGeometry.lean#L40) |
| **Theorem 10** (Global failure on a coercive polyhedral function) | `art:failure_polyhedral`<br>[`paper/sections/failure.tex:193-204`](paper/sections/failure.tex#L193-L204) | [`Failure.failure_polyhedral`](bfgs_lean_article/BfgsArticle/Coverage/Article/Failure.lean#L1307) | [`BfgsVerification.SeedOrbit.actual_coercive_deterministic_failure`](bfgs_lean_stage1/BfgsVerification/AlgebraicSeedCoercive.lean#L301), [`BfgsVerification.DNonStrictObjectives.coercive_fromMetric`](bfgs_lean_stage1/BfgsVerification/DNonStrictObjectives.lean#L39) |
| **Lemma 6** ($C^{2,1}$ scalar plateau spline) | `art:upper_scalar_lemma`<br>[`paper/sections/failure.tex:281-292`](paper/sections/failure.tex#L281-L292) | [`Failure.upper_scalar_lemma_exists`](bfgs_lean_article/BfgsArticle/Coverage/Article/Failure.lean#L1890) | [`BfgsVerification.DScalar.scalar_function_contract`](bfgs_lean_stage1/BfgsVerification/DScalarTarget.lean#L11), [`BfgsVerification.DScalar.phi_second_derivative_lipschitz`](bfgs_lean_stage1/BfgsVerification/DScalarAssembly.lean#L111) |
| **Theorem 11** (Local failure with globally smooth convex branches) | `art:local-failure`<br>[`paper/statements/negative_upper.tex:1-25`](paper/statements/negative_upper.tex#L1-L25) | [`NegativeUpper.local_failure`](bfgs_lean_article/BfgsArticle/Coverage/Article/NegativeUpper.lean#L194) | [`BfgsVerification.DEmbedding.deterministic_embedding_failure`](bfgs_lean_stage1/BfgsVerification/DEmbeddingTarget.lean#L12), [`BfgsVerification.DEmbedding.objective_function_contract`](bfgs_lean_stage1/BfgsVerification/DEmbeddingObjective.lean#L468) |
| **Theorem 12** (Local failure under uniform strong convexity) | `art:local-failure-lower`<br>[`paper/statements/negative_lower.tex:1-26`](paper/statements/negative_lower.tex#L1-L26) | [`NegativeLower.local_failure_lower`](bfgs_lean_article/BfgsArticle/Coverage/Article/NegativeLower.lean#L156) | [`BfgsVerification.LUniform.uniformSmoothLocalFailure`](bfgs_lean_article/BfgsArticle/LUniformLocal.lean#L572), [`BfgsVerification.LUniform.uniform_identity_failure`](bfgs_lean_article/BfgsArticle/LUniformLocal.lean#L539) |

### Appendix A. Gram compression for the inverse-BFGS update

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Lemma 7** (Subspace Gram compression) | `art:gram-compression`<br>[`paper/appendices/matrix_algebra.tex:6-15`](paper/appendices/matrix_algebra.tex#L6-L15) | [`MatrixAlgebra.gram_compression`](bfgs_lean_article/BfgsArticle/Coverage/Article/MatrixAlgebra.lean#L523) | [`BfgsVerification.BFGSCompression.compressed_inverseBFGS_bound`](bfgs_lean_stage1/BfgsVerification/BFGSCompression.lean#L120), [`BfgsVerification.inverseBFGS_step_det_beta`](bfgs_lean_stage1/BfgsVerification/HessianUpdate.lean#L177) |

### Appendix B. Constructing the planar contour comparison field

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Lemma 8** (Planar contour comparison field) | `art:planar-field`<br>[`paper/appendices/planar_geometry.tex:7-33`](paper/appendices/planar_geometry.tex#L7-L33) | [`PlanarGeometry.planar_field`](bfgs_lean_article/BfgsArticle/Coverage/Article/PlanarGeometry.lean#L738) | [`BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates`](bfgs_lean_stage1/BfgsVerification/PlanarAllEndpoints.lean#L14), [`BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates`](bfgs_lean_stage1/BfgsVerification/PlanarAllEndpointTargets.lean#L35) |

### Appendix C. The algebraic seed and its finite rational certificate

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Lemma 9** (Rational root certificate) | `art:root_certificate`<br>[`paper/appendices/seed_certificate.tex:32-36`](paper/appendices/seed_certificate.tex#L32-L36) | [`SeedCertificate.root_certificate`](bfgs_lean_article/BfgsArticle/Coverage/Article/SeedCertificate.lean#L157) | [`BfgsVerification.AlgebraicSeed.exact_closed_box`](bfgs_lean_stage1/BfgsVerification/AlgebraicSeedRoot.lean#L101), [`BfgsVerification.AlgebraicSeed.box_denominators_and_ratio`](bfgs_lean_stage1/BfgsVerification/AlgebraicSeedRoot.lean#L162) |

### Appendix D. Scalar spline interpolations and the strongly convex local embedding

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Proposition 1** (Perturbed failing trajectory under strong convexity) | `art:quadratic_failure`<br>[`paper/appendices/lower_curvature.tex:99-107`](paper/appendices/lower_curvature.tex#L99-L107) | [`LowerCurvature.quadratic_failure_initial_point`](bfgs_lean_article/BfgsArticle/Coverage/Article/LowerCurvature.lean#L434) | [`BfgsVerification.LUniform.uniform_global_failure`](bfgs_lean_article/BfgsArticle/LUniformGlobal.lean#L227), [`BfgsVerification.LGlobalFailure.nonstrict_actual_global_failure`](bfgs_lean_article/BfgsArticle/LNonStrictGlobal.lean#L142) |
| **Lemma 10** (Exact search realization and hyperbolicity) | `art:lower_hyperbolic`<br>[`paper/appendices/lower_curvature.tex:136-148`](paper/appendices/lower_curvature.tex#L136-L148) | [`LowerCurvature.lower_hyperbolic`](bfgs_lean_article/BfgsArticle/Coverage/Article/LowerCurvature.lean#L593) | [`BfgsVerification.LReturnSpectrum.actual_spectral_contract`](bfgs_lean_stage1/BfgsVerification/LReturnSpectrum.lean#L12), [`BfgsVerification.LReturnSpectrum.actual_scale_eigenvector`](bfgs_lean_stage1/BfgsVerification/LReturnSpectrum.lean#L43) |

### Appendix E. Worked certificates and existence of admissible runs

| Statement | Label and source | Coverage declaration | Core library |
|:--|:--|:--|:--|
| **Proposition 2** (Degenerating trajectory and band certificate on $u^2+\lvert v\rvert$) | `art:examples-mixed`<br>[`paper/appendices/hypothesis_examples.tex:11-27`](paper/appendices/hypothesis_examples.tex#L11-L27) | [`HypothesisExamples.mixed_certificates`](bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean#L59) | [`BfgsVerification.HypothesisExamples.Mixed.certificate_parameters`](bfgs_lean_article/BfgsArticle/HypothesisExamples.lean#L434), [`BfgsVerification.HypothesisExamples.Mixed.joint_witness`](bfgs_lean_article/BfgsArticle/HypothesisExamples.lean#L526) |
| **Proposition 3** (Full-rank band certificate in $\mathbb{R}^n$) | `art:examples-full-rank`<br>[`paper/appendices/hypothesis_examples.tex:41-52`](paper/appendices/hypothesis_examples.tex#L41-L52) | [`HypothesisExamples.quadratic_certificates`](bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean#L276) | [`BfgsVerification.HypothesisExamples.Quadratic.objective_euclidean`](bfgs_lean_article/BfgsArticle/HypothesisExamples.lean#L39), [`BfgsVerification.HypothesisExamples.Quadratic.certificate_parameters`](bfgs_lean_article/BfgsArticle/HypothesisExamples.lean#L102) |
| **Lemma 11** (Existence of differentiable Armijo–weak-Wolfe steps and runs) | `art:examples-run-existence`<br>[`paper/appendices/hypothesis_examples.tex:62-75`](paper/appendices/hypothesis_examples.tex#L62-L75) | [`HypothesisExamples.strict_wolfe_step`](bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean#L335) | [`BfgsVerification.AdmissibleRunExistence.exists_wolfe_step`](bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean#L85), [`BfgsVerification.AdmissibleRunExistence.exists_admissible_run`](bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean#L199) |
| **Proposition 4** (Curved two-quadratic family with global convergence and run existence) | `art:examples-two-quadratics`<br>[`paper/appendices/hypothesis_examples.tex:89-100`](paper/appendices/hypothesis_examples.tex#L89-L100) | [`HypothesisExamples.two_quadratic_joint`](bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean#L517) | [`BfgsVerification.TwoQuadraticExample.paper_planar_hypotheses`](bfgs_lean_article/BfgsArticle/TwoQuadraticExample.lean#L526), [`BfgsVerification.TwoQuadraticExample.joint_witness`](bfgs_lean_article/BfgsArticle/TwoQuadraticExample.lean#L760) |
| **Corollary 8** (Run existence on the three-quadratic nonradial example) | `art:examples-nonradial-runs`<br>[`paper/appendices/hypothesis_examples.tex:118-123`](paper/appendices/hypothesis_examples.tex#L118-L123) | [`HypothesisExamples.nonradial_runs`](bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean#L556) | [`BfgsVerification.PlanarQuadraticExample.objective_exists_admissible_run`](bfgs_lean_article/BfgsArticle/AdmissibleRunExistence.lean#L431), [`BfgsVerification.PlanarQuadraticExample.fullBFGS_explicit_basin`](bfgs_lean_stage1/BfgsVerification/PlanarQuadraticConvergence.lean#L63) |
| **Proposition 5** (A coercive homogeneous objective with no differentiable first step) | `art:examples-no-step`<br>[`paper/appendices/hypothesis_examples.tex:145-152`](paper/appendices/hypothesis_examples.tex#L145-L152) | [`HypothesisExamples.gauge_no_step`](bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean#L601) | [`BfgsVerification.HypothesisExamples.Gauge.joint_obstruction`](bfgs_lean_article/BfgsArticle/HypothesisExamples.lean#L754) |

## 3. Registers and checks

| Register | TeX file | Items |
|:--|:--|:--|
| [`A_master.json`](editorial/lean_coverage/register/A_master.json) | [`paper/master.tex`](paper/master.tex) | 13 |
| [`A_introduction.json`](editorial/lean_coverage/register/A_introduction.json) | [`paper/sections/introduction.tex`](paper/sections/introduction.tex) | 82 |
| [`A_energy.json`](editorial/lean_coverage/register/A_energy.json) | [`paper/sections/energy.tex`](paper/sections/energy.tex) | 71 |
| [`A_global.json`](editorial/lean_coverage/register/A_global.json) | [`paper/sections/global.tex`](paper/sections/global.tex) | 58 |
| [`A_local.json`](editorial/lean_coverage/register/A_local.json) | [`paper/sections/local.tex`](paper/sections/local.tex) | 62 |
| [`A_failure.json`](editorial/lean_coverage/register/A_failure.json) | [`paper/sections/failure.tex`](paper/sections/failure.tex) | 93 |
| [`A_verification.json`](editorial/lean_coverage/register/A_verification.json) | [`paper/sections/verification.tex`](paper/sections/verification.tex) | 35 |
| [`A_positive_partition.json`](editorial/lean_coverage/register/A_positive_partition.json) | [`paper/statements/positive_partition.tex`](paper/statements/positive_partition.tex) | 3 |
| [`A_negative_upper.json`](editorial/lean_coverage/register/A_negative_upper.json) | [`paper/statements/negative_upper.tex`](paper/statements/negative_upper.tex) | 4 |
| [`A_negative_lower.json`](editorial/lean_coverage/register/A_negative_lower.json) | [`paper/statements/negative_lower.tex`](paper/statements/negative_lower.tex) | 3 |
| [`A_matrix_algebra.json`](editorial/lean_coverage/register/A_matrix_algebra.json) | [`paper/appendices/matrix_algebra.tex`](paper/appendices/matrix_algebra.tex) | 10 |
| [`A_planar_geometry.json`](editorial/lean_coverage/register/A_planar_geometry.json) | [`paper/appendices/planar_geometry.tex`](paper/appendices/planar_geometry.tex) | 15 |
| [`A_seed_certificate.json`](editorial/lean_coverage/register/A_seed_certificate.json) | [`paper/appendices/seed_certificate.tex`](paper/appendices/seed_certificate.tex) | 29 |
| [`A_lower_curvature.json`](editorial/lean_coverage/register/A_lower_curvature.json) | [`paper/appendices/lower_curvature.tex`](paper/appendices/lower_curvature.tex) | 63 |
| [`A_hypothesis_examples.json`](editorial/lean_coverage/register/A_hypothesis_examples.json) | [`paper/appendices/hypothesis_examples.tex`](paper/appendices/hypothesis_examples.tex) | 20 |

`register/A_geometry.json` was retired with the rewrite of November 2026, when
`paper/sections/geometry.tex` was dissolved into Sections 1.1, 1.2 and 4.4; its ids are
listed as `retired` in `A_introduction.json` with their successors, and
`BfgsArticle/Coverage/Article/Geometry.lean` is kept unchanged because companion modules
import it (its statements are restated in `Introduction.lean`).

Checks: `check_coverage.py --strict` (every item has a final status, every `LEAN` item's
first name is declared in the module of its register, every docstring item reference
`Item `A/...` (`file:a-b`)` matches the register, every anchor occurs in its lines);
each coverage module compiles without errors or warnings
(`LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Article/<Module>.lean` in
`bfgs_lean_article/`); `#print axioms` gives at most `[propext, Classical.choice, Quot.sound]`.
