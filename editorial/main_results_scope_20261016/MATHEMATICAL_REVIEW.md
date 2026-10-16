# Independent mathematical review of the main-results scope draft

**Date:** 16 October 2026.

**Repository HEAD checked:** `a6f46d13bb31e27e92b27890470c8c0754fb9c80`.

**Draft reviewed:** `editorial/main_results_scope_20261016/REVIEW.md`, the 442-line version read at the start of this review. Locations below refer to that version.

**Reviewer:** independent GPT-6 Astra subagent in OpenCode.

## Verdict

**The requested new calculations and examples are mathematically sound.** In particular, the explicit band certificate, actual BFGS history, centered support-function family, positive-spanning test, numerical Lasso basin, parameterized two-quadratic family, arbitrary-data run-existence application, radial obstruction, and max-linear first-step obstruction all check out.

**Revise three scope formulations before accepting the report:** one definite reversed implication (R1), and two overbroad/underspecified statements (R2–R3). None invalidates the new examples or the report's central answer. The report fairly answers the author's question and usefully distinguishes objective hypotheses, existence of an infinite run, and success of a specified implementation.

This review used analytic derivations and the stated manuscript contracts. I read the general `AdmissibleRunExistence` theorem for its exact hypotheses; I did not undertake the separate comprehensive formal-witness search or run Lean/lake. The proofs below are ordinary mathematical proofs, not claims of new registered Lean coverage. No computational algebra or numerical sampling is being used as a substitute for proof.

## Required corrections

### R1 — Reverse the comparison between affine criticality and stationarity

- [ ] **Location:** Section 4.4, lines 278–282, especially line 280.
- **Exact text:** “affine-criticality is stronger than stationarity.”
- **Problem:** This implication is backwards. The manuscript defines
  \(\mathcal C_{\rm aff}=\{p:0\in\operatorname{aff}\partial F(p)\}\)
  in `paper/sections/local.tex:157-168`. Since
  \(\partial F(p)\subseteq\operatorname{aff}\partial F(p)\), ordinary convex stationarity implies affine criticality; the converse can fail.
- **Corrected explanation/proof:** For example,
  \[
  J(u,v)=u^2+v^2+\max\{u,2u\}
  \]
  is finite, coercive and strongly convex. At zero,
  \(\partial J(0)=[1,2]\times\{0\}\), whose affine hull contains zero but which itself does not. Thus zero is affine critical but not stationary. What is stronger than ordinary descent is *equal-rate descent*, equivalently non-affine-criticality; and the hypothesis that every affine-critical point is optimal is stronger than ordinary convex stationarity/optimality.
- **Suggested replacement:** “In particular, higher-dimensional curved switching is not covered by the planar construction. Affine criticality is weaker than stationarity, so requiring every affine-critical point in the relevant sublevel to be optimal is a substantive extra hypothesis.”
- **Theorem reference:** `paper/sections/local.tex:276-291` has exactly this extra hypothesis and correctly describes equal-rate descent as stronger than ordinary descent.

### R2 — Qualify the blanket exclusion based on affine intercepts

- [ ] **Location:** Section 4.2, lines 203–206; compare the table at line 52.
- **Exact text:** “Affine intercepts, such as the cap in the article's coercive polyhedral failure example, destroy the homogeneous structure; they are not covered by this global theorem.”
- **Problem:** As a categorical statement about representations, this is false. Homogeneity is a property of the resulting function, not the absence of an intercept in every formula used to represent it. For example,
  \[
  \max\{x,-x,-1\}=|x|
  \]
  has a nonzero affine intercept in a redundant branch and is covered by `art:homogeneous`. Also, a common additive objective constant does not change any BFGS or line-search comparison and can be removed before applying the homogeneous result.
- **Correct conclusion:** The theorem does not guarantee convergence for *general* finite affine maxima. The particular coercive cap in the article is genuinely nonhomogeneous and excluded from this route. Neither the positive-spanning calculation nor that exclusion requires a blanket necessity claim about all representations with intercepts.
- **Suggested replacement:** “General affine offsets need not preserve homogeneity, so this global theorem gives no guarantee for arbitrary finite affine maxima. The cap in the article's coercive polyhedral failure example is a concrete nonhomogeneous case.”
- **Table wording:** “Does not cover general affine maxima” would express the intended scope more accurately than treating intercepts themselves as a disqualifying feature.

### R3 — Keep the open C²/strong-convexity question explicitly local

- [ ] **Location:** Section 6.3, lines 396–401.
- **Exact text:** “They do not refute the conjunction ‘finite uniformly strongly convex C² branches’ in general” and “leaves the more general C²/strong-convexity question … open.”
- **Problem:** The preceding paragraph discusses local failure, but these sentences drop the essential local qualifier. The article already proves a *global* failure with finitely many uniformly strongly convex C∞ branches. Thus the unrestricted convergence question for that conjunction is not open here.
- **Source/proof of the distinction:** In `paper/appendices/lower_curvature.tex:26-52`,
  \[
  Q_\mu(x)=\tfrac\mu2\|x\|^2+\max_i g_i^Tx
          =\max_i\{\tfrac\mu2\|x\|^2+g_i^Tx\},\qquad\mu>0,
  \]
  has three quadratic branches, each with Hessian \(\mu I\). Proposition `art:quadratic_failure` supplies a genuine deterministic admissible run converging to the nonoptimal origin; its optimum is \(-1/(514\mu)<0\). This is a global failure with the stated conjunction. What remains open is an every-start **local neighborhood** guarantee near the optimizer for one fixed objective, outside the nondegenerate planar theorem; see `paper/sections/verification.tex:53-59`.
- **Suggested replacement:** “These two local embeddings do not settle the every-start local-neighborhood convergence question for finitely many uniformly strongly convex C² branches, outside the nondegenerate planar case. Global convergence for this class already fails for the quadratic-perturbed seed in Proposition `art:quadratic_failure`.” Keep “local” when mentioning the open question later in the paragraph.

## Suggested clarifications

1. **State the loss regularity explicitly.** Section 4.3, lines 210–214, says “smooth convex losses.” The exact contract in `paper/sections/local.tex:79-95` is convex and locally C¹,¹. Writing that regularity avoids reading “smooth” as merely C¹; the latter alone does not discharge the cell-extension hypothesis.
2. **Use “every positive sublevel” in Section 5.** Lines 294–295 and 312 should preferably say \(K_B=\{F\le B\}\), \(B>0\), to match `art:planar-cluster`'s strict upper-level assumption \(b>F_*\). The global conclusion is correct. Also, the family has curved switching when \(a\ne c\); \(a=c\) is its valid straight-switching special case.
3. **Clarify the table's provenance heading.** The heading at line 47, “Concrete witness / class already presented,” can be read as “already in the article,” whereas the report also supplies new worked examples. “Illustrative witness / class (sources below)” would preserve the distinction the prose carefully makes later. The distinction matters to the author's question about whether the examples have actually been presented.

## Verification of the new calculations

### 1. Section 3: the complete band certificate is valid

For \(F(u,v)=u^2+|v|\), the minimum is zero, its minimizer is unique, and \(K=\{F\le b\}\), \(b>0\), is compact. On differentiability points \(v\ne0\),
\[
g=(2u,\operatorname{sgn}v),\qquad g^Tx=2u^2+|v|\ge F(x).
\]
Consequently \(W_\eta(x)=xx^T\) is finite-valued, symmetric and PSD, with visibility constant \(m_\eta=\eta^2\) on every nonempty positive band.

For distinct endpoints \(z=x+s\), \(\Pi_s z=\Pi_s x\), so their projected rank-one matrices agree exactly. Thus \(L_\eta=0\). Eligible pairs have \(d>0\), hence \(s\ne0\), so the projection is well-defined.

Write \(x=(u,v)\), \(z=(a,w)\), with \(v,w\ne0\), and let \(A=a-u\).

- If the signs agree, \(y=(2A,0)\), \(t=2A^2\), and
  \[
  (y^Tz)^2=4A^2a^2=2a^2t\le2F(z)t\le2bt.
  \]
  This also holds when \(A=0\).
- If the signs differ, set \(S=|v|+|w|>0\). Then
  \[
  t=2A^2+2S,\qquad y^Tz=2Aa+2|w|.
  \]
  Cauchy–Schwarz applied to
  \((\sqrt2 A,\sqrt{2S})\) and
  \((\sqrt2 a,\sqrt2|w|/\sqrt S)\) gives
  \[
  (y^Tz)^2\le t\left(2a^2+\frac{2|w|^2}{S}\right)
       \le2(a^2+|w|)t\le2bt.
  \]

This proves secant control for every pair of differentiability points in \(K\), a stronger assertion than the eligible-small-pair requirement. Therefore \(C_\eta=2b\), \(\delta_\eta=1\), and all other constants in lines 101–104 are correct. The proof checks both orientations of the sign change.

### 2. Section 3: the stated history is an actual infinite full-BFGS run

Put \(h_k=2^{-k}\) and \(\sigma_k=(-1)^k\). The proposed data give
\[
x_k=(0,\tfrac23\sigma_kh_k),\quad
g_k=(0,\sigma_k),\quad
s_k=(0,-\sigma_kh_k),\quad
y_k=(0,-2\sigma_k).
\]
Thus \(s_k=-H_kg_k\) and \(x_{k+1}=x_k+s_k\), with \(\alpha_k=1\). Moreover,
\[
I-s_ky_k^T/t_k=\operatorname{diag}(1,0),\qquad
\frac{s_ks_k^T}{t_k}=\operatorname{diag}(0,h_k/2),
\]
so the full inverse-BFGS formula gives exactly \(H_{k+1}=\operatorname{diag}(1,h_k/2)\).

The printed scalars are correct:
\[
d_k=h_k,\qquad \Delta_k=h_k/3,\qquad t_k=2h_k.
\]
Armijo holds because \(h_k/3\ge h_k/4\). Weak Wolfe holds because
\(g_{k+1}^Ts_k=h_k\ge-h_k/2=c_2g_k^Ts_k\).
Every iterate is differentiable, every gradient is nonzero, and every finite-index matrix is SPD. The singular matrix limit is immaterial.

The scalar quadratic witness at lines 152–155 is also correct: \(y_k=s_k\), hence the scalar inverse update stays equal to one; \(\Delta_k=3\cdot4^{-k}/8\), \(d_k=4^{-k}/2\), and weak Wolfe holds at equality for \(c_2=1/2\).

### 3. Section 4.1: centering test and support-function family

Under the centered theorem's convexity and smoothness assumptions, the subgradient sum rule at \(x_*\) gives
\[
\partial F(x_*)=\nabla\psi(x_*)+\partial\gamma(0).
\]
Consequently the printed test is necessary and sufficient for optimality. A representation on a neighborhood suffices: local optimality is global for the finite convex \(F\).

For nonempty compact convex \(C\), \(\partial\sigma_C(0)=C\). In the proposed family \(\nabla\psi(x_*)=-a\), so \(a\in C\) checks the test. The bound
\[
F(x_*+r)\ge c+\tfrac12r^TQr
          \ge c+\tfrac12\lambda_{\min}(Q)\|r\|^2
\]
proves uniqueness, attainment and compact sublevels. Neither symmetry nor polyhedrality nor \(0\in C\) is needed. This is a valid arbitrary-dimensional global specialization of `art:centered`.

### 4. Section 4.2: positive spanning is the correct equivalence

Let \(P=\operatorname{conv}\{a_i\}\). If \(0\in\operatorname{int}P\), some \(\mu\overline B\subseteq P\); comparing support functions gives \(F(x)\ge\mu\|x\|\).
Conversely, if zero is not in the full-dimensional interior of \(P\), separation supplies a nonzero \(v\) with \(a_i^Tv\le0\) for every \(i\). Its positive ray prevents coercivity. Equivalently, coercivity and homogeneity force a strictly positive minimum on the unit sphere.

The stability assertion is correct: if \(\max_i\|\widetilde a_i-a_i\|<\varepsilon<\mu\), then
\(\max_i\widetilde a_i^Tx\ge(\mu-\varepsilon)\|x\|\).
Only the intercept wording needs R2.

### 5. Section 4.3: the Lasso basin is correct and nonempty

The objective is strongly convex. Direct scalar minimization gives \(x_*=(1,0)\), \(F_*=3/2\). On \(x_1>0\),
\[
\psi(x)=\tfrac32+\tfrac12(x_1-1)^2+\tfrac12x_2^2,
\qquad\gamma(x-x_*)=|x_2|,
\]
which is precisely the required centered representation.

For \(x_1\le0\),
\[
F(x)=2+\tfrac12x_1^2-3x_1+\tfrac12x_2^2+|x_2|\ge2.
\]
Thus any initial sublevel with upper value below two is compact and wholly in the open convex set \(U=\{x_1>0\}\). `art:centered` gives convergence for every admissible run from it, for arbitrary initial SPD matrix and fixed valid constants. For example, \((1,1/4)\) is a differentiable point in this basin. The draft correctly makes a conditional convergence assertion here rather than asserting a particular search succeeds.

### 6. Section 5: all parameters a,b,c>0 give the asserted global planar example

Write \(f_+=au^2+bv^2+v\) and \(f_-=cu^2+bv^2-v\). Each Hessian is bounded below by \(2\min(a,b,c)I\), and their maximum inherits that strong convexity. The average bound
\[
F\ge(f_++f_-)/2=\tfrac{a+c}{2}u^2+bv^2
\]
proves unique minimization at zero and compactness of every sublevel. Strong convexity implies that a segment joining distinct positive-level boundary points has its interior strictly below that level, proving the strict-contour hypothesis.

The switching equation is \(v=(c-a)u^2/2\). With gradients
\(p=(2au,2bv+1)\), \(q=(2cu,2bv-1)\),
\[
\det(p,q)=4b(a-c)uv-2(a+c)u
          =-2u\bigl[a+c+b(c-a)^2u^2\bigr]
\]
on the switching curve. It is nonzero except at zero. At every other switching point the two gradients are linearly independent, so zero is not in their affine line. At a smooth point, affine criticality would mean a zero gradient and thus global optimality, impossible because the unique minimizer is nonsmooth. At zero the gradients are \((0,1)\), \((0,-1)\), whose affine hull contains zero. Hence \(\mathcal C_{\rm aff}=\{0\}\) exactly.

All hypotheses of `art:planar-cluster` and `art:planar-convergence` therefore hold on \(\{F\le B\}\) for every \(B>0\). Each admissible initial point has such a positive value, proving the claimed global conclusion. The two gradients at zero are affinely independent and have strictly positive weights \((1/2,1/2)\), also checking `art:planar-max`.

**Run existence has the claimed arbitrary-data quantifiers.** The gradient difference across a tie is \((2(a-c)u,2)\ne0\), so differentiability is equivalent to not being on the switching curve. On any line \(x+tp\) through a differentiability point, the polynomial \(f_+(x+tp)-f_-(x+tp)\) has degree at most two and is nonzero at \(t=0\). It therefore has at most two roots. This gives the finite-exception, hence countable-exception, hypothesis of `AdmissibleRunExistence.exists_admissible_run` (`BfgsArticle/AdmissibleRunExistence.lean:192-207`) for both \(a\ne c\) and \(a=c\).

The unique minimizer zero is nondifferentiable, so no differentiability point has zero gradient. Convexity and boundedness below were already checked. The general theorem thus supplies an infinite admissible run from **every differentiable start, every SPD initial matrix, and every fixed valid pair \(0<c_1<c_2<1\)**. This is existence of a choice of accepted steps, exactly as stated; it is not a guarantee about an arbitrary implementation.

### 7. Section 5: radial-obstruction identities and eligibility are exact

For \(a=b=1,c=2\), let \(v_0=r^2/2\), \(x=(r,v_0+e)\), \(z=(r,v_0-e/2)\), with \(r,e>0\). The branch gaps are \(f_+(x)-f_-(x)=2e>0\) and \(f_+(z)-f_-(z)=-e<0\), so both endpoints are differentiable with the asserted branch choices. In particular,
\[
g=(2r,1+r^2+2e),\quad h=(4r,r^2-e-1),\quad
s=(0,-3e/2),\quad y=(2r,-2-3e).
\]
These give exactly all four formulas at lines 329–332, including
\(y^Tz=r^2+(1-3r^2/2)e+3e^2/2\). Direct subtraction gives exactly
\[
\Delta-d/4=e(1+9r^2)/8,\quad
d-\Delta=e+9e^2/4,\quad
t-d/2=3e(3-r^2)/4+3e^2.
\]
Thus for \(0<r^2<3\), every \(e>0\) gives an eligible pair for \((c_1,c_2)=(1/4,1/2)\). For the band argument, only sufficiently small \(e\) is needed.

Fix \(r>0\). The common limiting value is
\(\ell=3r^2/2+r^4/4>0\). For sufficiently small \(e\), both endpoints lie in the single positive band
\(\{\ell/2\le F\le2\ell\}\). Meanwhile \(d\to0\), \(t\sim3e\to0\), and \(y^Tz\to r^2\ne0\), so \((y^Tz)^2/t\to+\infty\). This defeats every finite radial secant constant even with any imposed positive small-step threshold. Since \(F\ge u^2+v^2\) and \(\ell\to0\) as \(r\to0\), these entire small sublevel bands can be placed in any prescribed neighborhood of zero. The draft correctly avoids interpreting the varying endpoint pairs as one BFGS history.

### 8. Section 6.1: the max-linear obstruction is valid

For \(G=\max\{u,-u+v,-u-v\}=\max\{u,-u+|v|\}\),
\[
G\ge|u|,\qquad G\ge|v|/2,
\]
so \(\|(u,v)\|\le\sqrt5\,G(u,v)\). Hence it is coercive, nonnegative, and uniquely minimized at zero; it satisfies `art:homogeneous`.

At \((1,0)\), only the first branch is active, the gradient is \((1,0)\), and with \(H_0=I\) the proposed next point is \((1-\alpha,0)\). For \(0<\alpha<1\), both gradients equal \((1,0)\), and weak Wolfe requires \(-\alpha\ge-c_2\alpha\), impossible for \(c_2<1\). At \(\alpha=1\), all branches are active with distinct gradients. For \(\alpha>1\), the second and third branches are active with distinct gradients. These points are nondifferentiable in the ambient plane, even though the restriction to the open negative horizontal ray is smooth.

There is therefore no admissible first step, independently of Armijo and for every valid constant pair. Replacing one by \(\varepsilon>0\) changes the threshold to \(\alpha=\varepsilon\) and preserves the obstruction. The same line through a differentiability point contains a whole nondifferentiable ray, so the general existence theorem's countability hypothesis genuinely fails. The draft correctly limits this to the specified initial data and does not call it a stagnating infinite run or a generic failure result.

## Overall scope and readability assessment

The opening three-way distinction is essential and well executed. The compactness/localization consequences, objective-independent-of-metric basin quantifiers, conditional nature of the positive theorems, and restriction of the moving-geometry construction to the plane match the manuscript. The examples demonstrate joint satisfiability, not merely isolated hypotheses or unrealizable update sequences. Section 5 adds a valid global family beyond the printed local three-branch example and carefully marks its analytic, not newly formalized, status.

After R1–R3, the report's generality assessment is fair: substantial sufficient classes, explicit existence evidence, genuine limits on initialization/nonbreakdown, and no genericity, positive-measure-failure or necessity theorem being inferred. The report does not identify a defect in a main manuscript theorem; the required corrections are in the new review's scope exposition.
