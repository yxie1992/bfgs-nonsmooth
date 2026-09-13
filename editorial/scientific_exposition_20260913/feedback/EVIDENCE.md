# Evidence excerpts

These are verbatim excerpts from the uploaded source snapshot, not replacement text. Line numbers are one-based physical lines in the source. PDF pages refer to the local build, whose expected 46/107 page counts match the archive manifest. Internal paths in the source refer to the full author repository and may be absent from this intentionally compact typesetting bundle.

## E1. New introduction: historical benchmark and comparison

`paper/sections/introduction.tex:3–52`; article pp. 1–2.

```text

0003 BFGS builds its search directions from changes in gradients, yet it often
0004 works well when those gradients jump. Classical convex convergence theory
0005 uses smoothness together with the evolving quasi-Newton matrices
0006 \cite{FND_P76,FND_BN89,FND_N92}. Lewis--Overton's experiments and analyses
0007 \cite{LO} exposed the difficulty of extending that theory: nonsmooth BFGS can
0008 approach a minimizer while its inverse-Hessian approximations become highly
0009 singular. What global or local convergence can ordinary full BFGS guarantee
0010 on convex nonsmooth functions, and how can one prove it without assuming
0011 the asymptotic behavior of its iterates or matrices?
0012 
0013 We give three answers: deterministic counterexamples to every-start local
0014 convergence; global and local convergence theorems for structured convex
0015 families, including the mixed benchmark below; and a principal-minor and
0016 comparison-energy argument that remains effective as the BFGS matrices
0017 degenerate.
0018 
0019 Lewis--Overton's Challenge~7.1~\cite{LO} gives this question a broader,
0020 probabilistic setting. For locally Lipschitz semialgebraic objectives with
0021 bounded sublevels and absolutely continuously distributed initial data, it
0022 asks about nonbreakdown, stationary cluster points, R-linear convergence of
0023 all function trial values, and identification of spectral subspaces under
0024 partly smooth convergence. We study deterministic guarantees for convex
0025 objectives. Successful termination is allowed; infinite runs are analyzed
0026 under the differentiable-iterate convention made precise below.
0027 
0028 Substantial positive theory precedes this work. Guo--Lewis extends Powell's
0029 argument through smooth convex replacements on regions relevant to a BFGS
0030 sequence~\cite[Theorems~3.2, 4.1 and~4.3]{GL18}. The resulting theory proves
0031 Euclidean-norm convergence in arbitrary finite dimension
0032 \cite[Corollary~4.2]{GL18}; for the mixed model
0033 \[
0034                     F(u,v)=u^2+|v|
0035 \]
0036 Corollary~4.4 gives only a subsequence approaching a point of $v=0$.
0037 The following paragraph explicitly leaves convergence of every BFGS sequence
0038 to $(0,0)$ open~\cite[Corollary~4.4 and following discussion]{GL18}.
0039 Approaching the nonsmooth line does not force the smooth coordinate $u$ to
0040 vanish. Corollary~\ref{art:mixed-benchmark} answers this whole-sequence question
0041 for every admissible full-BFGS run, as a consequence of an arbitrary-dimensional
0042 family theorem rather than a special planar recurrence.
0043 
0044 Two other advances clarify the remaining task. Xie--W\"achter's two-piece
0045 unbounded affine model leads to an unbounded descent direction after finitely
0046 many iterations~\preprintcite[Theorem IV.1]{XW}; a value-convergence theorem
0047 for a broader homogeneous family does not replace that finite escape result.
0048 Gebken's published 2026 introduction still identifies $u^2+|v|$ as unresolved.
0049 His local criticality theorem for continuous smooth selections assumes an
0050 iterate limit, repeated activity, and specified spectral and gradient-jump
0051 behavior~\cite[Theorem~3.1 and (B1)]{BG}. Our positive results instead derive
0052 convergence from the objective hypotheses for the families stated here.

```

## E2. Three contribution paragraphs

`paper/sections/introduction.tex:61–112`; article pp. 2–3.

```text

0061 \paragraph{Deterministic limits.}
0062 We construct convex objectives for which a fixed unit-first
0063 Armijo--weak-Wolfe doubling/bisection search generates full-BFGS iterates
0064 converging to a nonstationary point. For each local construction, one fixed
0065 objective has failing starts arbitrarily close to its unique minimizer, all
0066 with $H_0=I$, and every accepted or rejected query approaches that minimizer
0067 across the family of runs. One construction is a maximum of four convex
0068 $C^{2,1}$ branches with bounded Hessians; another is a maximum of four
0069 uniformly strongly convex $C^{1,1}$ branches, three of which are not twice
0070 differentiable at the minimizer (Theorems~\ref{art:local-failure}
0071 and~\ref{art:local-failure-lower}). These refute every-start neighborhood
0072 guarantees under either regularity regime. They establish no positive-measure
0073 failure set and do not refute the almost-sure semialgebraic challenge.
0074 
0075 \paragraph{Global and local convergence.}
0076 We prove global value convergence for centered smooth-plus-sublinear
0077 objectives with compact initial sublevels contained in the region where the
0078 representation holds, and whole-iterate convergence when
0079 the minimizer is unique (Theorem~\ref{art:centered}). This settles the mixed
0080 benchmark above. For coercive finite convex degree-one homogeneous functions,
0081 including coercive maxima of finitely many linear functions, every admissible
0082 run converges to zero (Theorem~\ref{art:homogeneous}). Local results
0083 cover smooth convex plus finite polyhedral terms and finite polyhedral
0084 partitions with smooth extensions (Theorem~\ref{art:polyhedral}). Moving
0085 comparison geometry also yields local convergence for planar smooth maxima
0086 under strict-contour and active-gradient nondegeneracy assumptions
0087 (Corollary~\ref{art:planar-max}). The explicit three-quadratic example in
0088 Theorem~\ref{art:nonradial-example} has curved switching sets and fails the radial
0089 condition, so this extension has a concrete payoff beyond inward radial
0090 modeling.
0091 
0092 \paragraph{Analysis with degenerating matrices.}
0093 We prove a hierarchy linking adjacent degrees of the actual principal
0094 minors of full-BFGS matrices. Extending the classical trace/determinant
0095 potential approach, it forces the arithmetic mean of the reciprocals
0096 $1/(g_k^TH_kg_k)$ to diverge when gradients are bounded and predicted
0097 decreases tend to zero. Comparison energies turn this restriction into convergence:
0098 a field must retain information about the objective gap, control the gradient
0099 changes it sees, and move with a controlled energy cost. The field is an
0100 analytical device, not part of the algorithm. Neither a bounded condition
0101 number nor a prescribed spectral limit is needed
0102 (Theorems~\ref{art:minor-hierarchy}--\ref{art:certificate}).
0103 
0104 Our conditions are sufficient; they do not classify every successful run.
0105 Sections~\ref{art:geometry}
0106 and~\ref{art:energy} explain and establish the mechanism;
0107 Sections~\ref{art:global} and~\ref{art:local} prove its global and local
0108 consequences, and Section~\ref{art:failure} gives the deterministic
0109 counterexamples. The article includes the essential proofs of these claims.
0110 An independent complete companion preserves the wider noncompact and
0111 quantitative theory, with Lean proofs, exact correspondence and reproducible
0112 audit evidence.

```

## E3. Negative predecessors deferred to the failure section

`paper/sections/failure.tex:46–64`; article p. 23.

```text

0046 For this routine, even identity initialization does not give a neighborhood
0047 in which every differentiable start succeeds under the following regularity
0048 assumptions.
0049 \input{statements/negative_upper}
0050 
0051 The objective and all starts are chosen before the displayed line-search
0052 parameters. The failure set supplied by the theorem is a sequence of starts;
0053 it is not a positive-measure basin. There is no uniform positive lower
0054 curvature requirement on these branches. Earlier prescribed-orbit
0055 constructions for smooth nonconvex objectives~\cite{NEG_M04,NEG_M07}
0056 suggest the value of designing the dynamics first. Other failures concern
0057 nonconvex objectives~\cite{NEG_LZ15}; see also \preprintcite{NEG_DIAO26}
0058 for a recent smooth nonconvex planar construction. These results do not
0059 supply the convex local claim above. Lewis--Overton's earlier examples use exact search or subgradient choices
0060 \preprintcite{NEG_LO08}; the scaled memoryless failures
0061 of Asl--Overton~\cite{NEG_AO21} concern a different matrix update. Here
0062 the essential combination is convex branch regularity, full BFGS with the
0063 specified search, a common identity initialization, and every query close
0064 to the true minimizer.

```

## E4. Energy motivation and principal-minor explanation

`paper/sections/energy.tex:74–142`; article pp. 7–8.

```text

0074 \begin{lemma}[Reference energy]\label{art:reference-energy}
0075 For any fixed $x_*$, put $r_k=x_k-x_*$ and
0076 \[
0077  E_k=r_k^TB_kr_k,\qquad a_k=g_k^Tr_k,\qquad
0078  R_k=\frac{(y_k^Tr_{k+1})^2}{t_k}.
0079 \]
0080 Then
0081 \begin{equation}\label{art:energy-identity}
0082  E_{k+1}=E_k-\frac{a_k^2}{q_k}+R_k.
0083 \end{equation}
0084 If $x_*$ minimizes $F$, with $F_*=F(x_*)$, then
0085 \begin{equation}\label{art:energy-budget}
0086  (F(x_N)-F_*)^2\sum_{k<N}q_k^{-1}
0087        \le E_0+\sum_{k<N}R_k.
0088 \end{equation}
0089 \end{lemma}
0090 \begin{proof}
0091 Since $r_{k+1}=r_k+s_k$ and $M_ks_k=0$, the Hessian update gives
0092 \[
0093  r_{k+1}^TB_{k+1}r_{k+1}
0094  =r_k^TM_kr_k+\frac{(y_k^Tr_{k+1})^2}{t_k},
0095 \]
0096 which is \eqref{art:energy-identity}. At a minimizer, convexity gives
0097 $a_k\ge F(x_k)-F_*$; the values decrease. Summation and $E_N\ge0$ yield
0098 \eqref{art:energy-budget}.
0099 \end{proof}
0100 
0101 The identity makes the intended contradiction visible. If a gap of at least
0102 $\eta>0$ persists and the secant correction satisfies $R_k\le C$, then
0103 \eqref{art:energy-budget} gives
0104 \[
0105  \eta^2\sum_{k<N}q_k^{-1}\le E_0+CN.
0106 \]
0107 Thus an objective-level bound on one component of a gradient jump would
0108 force the reciprocal sum to grow at most linearly. The next theorem proves
0109 that the full update requires faster growth. Neither step requires a bound
0110 on $\norm{B_k}$ or a limit for $H_k$: the initial energy is finite, and the
0111 later energies need only remain nonnegative.
0112 
0113 \subsection{Actual principal minors and reciprocal growth}
0114 
0115 For a symmetric $n\times n$ matrix $H$, define
0116 \[
0117  e_j(H)=\sum_{\substack{I\subset\{1,\ldots,n\}\\|I|=j}}\det H_{I,I},
0118  \qquad e_{n+1}(H)=0.
0119 \]
0120 These are actual principal determinants. Multilinearity of the determinant
0121 identifies them with the coefficients of $\det(I+zH)$; hence they are invariant
0122 under orthogonal changes of coordinates and equal the elementary symmetric
0123 polynomials of the eigenvalues. In particular $e_1=\tr$ and $e_n=\det$.
0124 Trace and determinant potentials are central to classical BFGS analysis
0125 \cite{FND_N92,FND_BN89}. The determinant records volume, while the intermediate
0126 principal-minor sums retain information about different-dimensional
0127 compressions. The inequality below couples each degree to the next one.
0128 After normalization, this coupling supplies a positive weighted potential
0129 even when the matrices become poorly conditioned.
0130 
0131 \begin{theorem}[Principal-minor hierarchy]\label{art:minor-hierarchy}
0132 Let $H\succ0$, $s=-\alpha Hg$, $\alpha>0$, and suppose
0133 \[
0134  q=g^THg>0,\qquad \beta=-\frac{y^THg}{q}>0.
0135 \]
0136 For the inverse-BFGS update $H_+$ in \eqref{art:update},
0137 \begin{equation}\label{art:hierarchy}
0138  e_j(H_+)\le\frac{\norm{y}^2}{\beta^2q}e_{j+1}(H)
0139                    +\frac\alpha\beta e_j(H),\qquad 1\le j\le n.
0140 \end{equation}
0141 At $j=n$ the exact identity is $\det H_+=(\alpha/\beta)\det H$.
0142 \end{theorem}

```

## E5. Unhelpful qualification of secant constant

`paper/sections/energy.tex:250–271`; article p. 10.

```text

0250 \begin{definition}[Band certificate]\label{art:band-certificate}
0251 Let $K=\{F\le b\}$ be compact, with $b>F_*=\min F$.
0252 For each nonempty $K_\eta=\{x\in K:F(x)\ge F_*+\eta\}$, $\eta>0$,
0253 a band certificate consists of a finite-valued symmetric PSD field
0254 $W_\eta(x)$ on its differentiable points and constants
0255 $m_\eta>0$, $C_\eta\ge0$, $L_\eta\ge0$, $\delta_\eta>0$ such that
0256 \begin{align}
0257  g^TW_\eta(x)g&\ge m_\eta,\label{art:visibility}\\
0258  y^TW_\eta(z)y&\le C_\eta t,\label{art:secant-control}\\
0259  \Pi_sW_\eta(z)\Pi_s&\preceq
0260  (1+L_\eta d)\Pi_sW_\eta(x)\Pi_s.\label{art:transport}
0261 \end{align}
0262 The first inequality holds at every differentiable point of $K_\eta$;
0263 the last two hold for all eligible pairs in $K_\eta$ with $d\le\delta_\eta$.
0264 \end{definition}
0265 Neither continuity, uniform boundedness nor positive definiteness of $W_\eta$
0266 is required. The constants and field may depend on the positive band.
0267 Allowing an arbitrary real secant constant gives the same condition, since
0268 it can always be replaced by its maximum with zero.
0269 The positive-band restriction permits these constants to deteriorate near the
0270 solution set: the proof only needs to rule out a limiting gap bounded away
0271 from zero. In particular, the condition allows nonsmoothness at an optimizer.

```

## E6. Global homogeneous family and its attribution

`paper/sections/global.tex:200–260`; article pp. 14–15.

```text

0200 \subsection{Coercive homogeneous objectives, linear maxima, and gauges}
0201 
0202 Pure homogeneous geometry is the limiting case with no smooth remainder.
0203 Coercivity here has a clear purpose: it prevents escape along a direction of
0204 zero or negative homogeneous value and converts convergence in value into
0205 convergence to the origin. It imposes no smoothness or finite-piece condition.
0206 
0207 \begin{theorem}[Coercive homogeneous objectives]\label{art:homogeneous}
0208 Let $F:\R^n\to\R$, $n\ge1$, be finite, convex, positively homogeneous of
0209 degree one, and coercive. Then zero is its unique minimizer and every
0210 infinite admissible full-BFGS run satisfies
0211 \[
0212  F(x_k)\longrightarrow0,\qquad x_k\longrightarrow0.
0213 \]
0214 The initial point, initial SPD matrix and fixed valid line-search constants
0215 are arbitrary within admissibility.
0216 \end{theorem}
0217 \begin{proof}
0218 Homogeneity gives $F(0)=0$. If $F(x)\le0$ for some $x\ne0$, then
0219 $F(tx)=tF(x)\le0$ as $t\to\infty$, contradicting coercivity. Thus
0220 $F(x)>0$ off zero. Continuity on the unit sphere gives
0221 \[
0222  \mu=\min_{\norm{x}=1}F(x)>0,
0223  \qquad F(x)\ge\mu\norm{x}.
0224 \]
0225 All sublevels are compact. Theorem~\ref{art:centered}, with $\psi=0$ and
0226 $\gamma=F$, gives convergence in value, and the displayed lower bound gives
0227 convergence of the iterates. Equivalently, the inward remainder is identically
0228 zero, so the radial convergence corollary applies directly.
0229 \end{proof}
0230 
0231 \begin{corollary}[Compact homogeneous models]\label{art:homogeneous-examples}
0232 The conclusion of Theorem~\ref{art:homogeneous} holds for every norm, every
0233 finite convex degree-one gauge with bounded unit sublevel, and every finite
0234 linear maximum
0235 \[
0236  F(x)=\max_{1\le i\le m}a_i^Tx
0237 \]
0238 whose zero sublevel is bounded. These are whole-iterate conclusions from every
0239 admissible start. The linear maximum has no affine intercepts.
0240 \end{corollary}
0241 \begin{proof}
0242 For a norm, continuity and positivity give a positive minimum on the Euclidean
0243 unit sphere. For either of the other models, boundedness of the stated
0244 sublevel rules out a nonzero $x$ with $F(x)\le0$, since its full positive ray
0245 would lie in that sublevel. The same sphere argument gives
0246 $F(x)\ge\mu\norm{x}$, hence coercivity. Finite maxima of linear forms are
0247 finite, convex and degree-one homogeneous, so the theorem applies.
0248 \end{proof}
0249 
0250 No symmetry is needed for the gauge or max-linear cases. The familiar
0251 Euclidean norm is an already established consequence of Guo--Lewis's
0252 smooth-extension analysis \cite[Corollary~4.2]{GL18}; the scalar absolute-value
0253 model was analyzed by Lewis--Overton under their stated search conventions
0254 \cite[Section~5.1]{LO}. The result here treats the stated arbitrary-dimensional
0255 homogeneous family. Coercivity is used for this compact, whole-iterate route,
0256 not asserted necessary for value convergence. The complete companion,
0257 Chapter~7, separately proves the noncompact homogeneous value dichotomy
0258 $F(x_k)\to0$ or $F(x_k)\to-\infty$, together with its bounded-below and
0259 additional iterate consequences. Those noncompact conclusions are not needed
0260 for, or independently reproved by, the compact global theorems of this article.

```

## E7. Common local models and application descriptions

`paper/sections/local.tex:78–128`; article p. 17.

```text

0078 \begin{corollary}[Smooth losses with polyhedral or quadratic pieces]\label{art:plq}
0079 A finite convex piecewise linear-quadratic objective with a unique minimizer
0080 has the local convergence property of Theorem~\ref{art:polyhedral}.
0081 The same holds for a convex locally $C^{1,1}$ loss plus a finite convex
0082 piecewise linear-quadratic regularizer, provided the sum has a unique minimizer.
0083 \end{corollary}
0084 \begin{proof}
0085 By piecewise linear-quadratic we mean a representation by quadratic polynomials
0086 on a finite cover by closed full-dimensional polyhedral cells. Each polynomial is a smooth
0087 extension of its cell formula; adding the smooth loss preserves the required
0088 local $C^{1,1}$ extensions. Theorem~\ref{art:polyhedral} applies.
0089 \end{proof}
0090 
0091 In particular, a finite convex polyhedral penalty, such as a finite sum of
0092 absolute-value or hinge terms, is piecewise affine on a finite polyhedral
0093 partition. It therefore falls under this corollary when added to a locally
0094 $C^{1,1}$ convex loss,
0095 under the stated uniqueness assumption. Different cells may have different
0096 quadratic Hessians. A finite maximum of arbitrary quadratic formulas need not
0097 admit such a polyhedral partition and is not automatically covered.
0098 There is also no claim that iterates identify a cell or that rejected trials
0099 remain in the local structural neighborhood.
0100 
0101 
0102 The finiteness and cell geometry are substantive. Finitely many curved
0103 switching interfaces need not preserve inward segments, and the negative
0104 examples later in the paper show that regularity of smooth branches alone
0105 cannot replace the stated geometric hypothesis. The theorem gives a
0106 sufficient local basin, without claiming necessity or a uniform rate.
0107 
0108 \begin{corollary}[A local centered-composite basin]\label{art:local-centered}
0109 If the representation and smoothness assumptions of
0110 Theorem~\ref{art:centered} hold on a neighborhood of a unique minimizer $x_*$,
0111 then some $\varepsilon>0$, chosen from the objective alone, has the following
0112 property: every admissible run starting with
0113 $F(x_0)\le F(x_*)+\varepsilon$ stays in that neighborhood and converges to
0114 $x_*$ in value and iterates.
0115 \end{corollary}
0116 \begin{proof}
0117 Shrink to an open convex neighborhood where the representation holds.
0118 Lemma~\ref{art:localization} gives a compact sublevel contained there.
0119 Armijo traps the accepted points, and Theorem~\ref{art:centered} applies.
0120 \end{proof}
0121 
0122 For example, a locally $C^{1,1}$ convex loss plus finitely many Euclidean
0123 residual norms $\norm{A_jx-b_j}$ has this local form. A residual nonzero at
0124 $x_*$ remains nonzero nearby, so its Euclidean norm is smooth there; a zero
0125 residual gives the centered sublinear function $\norm{A_j(x-x_*)}$.
0126 Summing these decompositions proves the representation. Under uniqueness,
0127 the corollary applies. This example allows nonpolyhedral penalties while
0128 retaining the same radial mechanism.

```

## E8. Main-text planar motivation and deferred construction

`paper/sections/local.tex:130–222`; article pp. 18–19.

```text

0130 \subsection{A moving direction for curved planar switching}
0131 
0132 The radial direction can fail for a different reason: a curved interface may
0133 carry a gradient jump with a nonzero radial component. The secant correction
0134 then blows up as endpoints approach opposite sides of the interface.
0135 The transported framework allows the comparison direction to follow the
0136 interface instead. It must first remain visible to every local supporting
0137 model, then cancel the leading jump, and finally move at a cost controlled
0138 by the actual objective decrease. The field is constructed from the
0139 objective; BFGS never evaluates it.
0140 
0141 For $F:\R^2\to\R$, write
0142 \[
0143  \mathcal C_{\rm aff}=
0144  \{p:0\in\aff\partial F(p)\}.
0145 \]
0146 At a point outside this set, let $a$ be the least-norm point of
0147 $\aff\partial F(p)$. Orthogonality to its direction space gives
0148 $g^Ta=\norm{a}^2$ for every $g\in\partial F(p)$. Thus
0149 $-a/\norm{a}^2$ decreases all supporting models at the same unit rate.
0150 Affine criticality concerns failure of this common-rate direction;
0151 ordinary stationarity concerns failure of every strict common descent
0152 direction. They need not coincide.
0153 
0154 The two planar hypotheses have separate roles. Strictly convex positive
0155 sublevels prohibit long accepted chords with vanishing value decrease.
0156 Regular two-branch switching makes each positive-level corner move smoothly
0157 with the level and supplies a direction paired equally with both gradients.
0158 Neither condition imposes a matrix limit or a lower bound on all eigenvalues
0159 of a Hessian. A common positive lower Hessian bound is one sufficient way
0160 to obtain strict contours, but is not required.
0161 
0162 \begin{theorem}[An affine-critical cluster point in the plane]\label{art:planar-cluster}
0163 Let $F:\R^2\to\R$ be finite and convex, attain its minimum $F_*$, and have
0164 a compact sublevel $K=\{F\le b\}$ with $b>F_*$. Assume the following
0165 objective geometry:
0166 
0167 \begin{enumerate}
0168 \item For every $F_*<t\le b$, the boundary of $\{F\le t\}$ contains no
0169 nontrivial line segment.
0170 \item At every $p\in K\setminus\mathcal C_{\rm aff}$, either $F$ is $C^2$
0171 in a neighborhood of $p$, or it equals $\max\{f_1,f_2\}$ there, where
0172 $f_1,f_2$ are convex $C^2$ functions, both active at $p$, and
0173 $\nabla f_1(p),\nabla f_2(p)$ are linearly independent.
0174 \end{enumerate}
0175 Every infinite admissible full-BFGS run starting in $K$ has an affine-critical
0176 cluster point. No local representation is required at affine-critical points.
0177 \end{theorem}
0178 \begin{proof}
0179 The values decrease to $\ell\ge F_*$, the gradients are bounded on $K$, and
0180 $\sum d_k<\infty$. Let $\Gamma$ be the nonempty compact cluster set.
0181 Every point of $\Gamma$ has value $\ell$. If $\ell=F_*$, its points are
0182 minimizers and hence affine critical. Suppose, for a contradiction, that
0183 $\Gamma$ contains no affine-critical point. Then $\ell>F_*$.
0184 
0185 The steps tend to zero. Otherwise compactness gives a subsequence with
0186 $x_k\to x$, $x_{k+1}\to z\ne x$. For $0\le\theta\le1$, the supporting
0187 inequality and convexity give
0188 \[
0189  F(x_k)-\theta d_k
0190  \le F((1-\theta)x_k+\theta x_{k+1})
0191  \le(1-\theta)F(x_k)+\theta F(x_{k+1}).
0192 \]
0193 Passing to the limit shows $F=\ell$ on $[x,z]$. Such level points lie on
0194 the boundary of $\{F\le\ell\}$: if one were interior, extending the line
0195 from a minimizer slightly beyond that point and applying convexity would
0196 give value strictly less than $\ell$. The resulting boundary segment
0197 contradicts the first hypothesis.
0198 
0199 Lemma~\ref{art:planar-field}, proved in Appendix~\ref{art:planar-appendix},
0200 constructs a continuous comparison field $w$ on a neighborhood of the whole
0201 set $\Gamma$. For each sufficiently close eligible pair in that neighborhood,
0202 it gives uniform constants $m>0,C,L\ge0$ and scalars $\lambda>0,\beta$ with
0203 \[
0204  \begin{gathered}
0205  (g^Tw(x))^2\ge m,\qquad (y^Tw(z))^2/t\le C,\\
0206  w(z)=\lambda w(x)+\beta s,\qquad \lambda^2\le1+Ld.
0207  \end{gathered}
0208 \]
0209 Compactness implies $\operatorname{dist}(x_k,\Gamma)\to0$, so these estimates
0210 apply to the entire tail, not just a selected subsequence.
0211 With $E_k=w(x_k)^TB_kw(x_k)$, the Hessian update and $M_ks_k=0$ yield
0212 \[
0213  E_{k+1}=
0214  \lambda_k^2\left(E_k-\frac{(g_k^Tw(x_k))^2}{q_k}\right)
0215        +\frac{(y_k^Tw(x_{k+1}))^2}{t_k}
0216  \le(1+Ld_k)(E_k-m/q_k)+C.
0217 \]
0218 The parenthesized quadratic form is nonnegative. Dividing by
0219 $\prod_{j=J}^{k}(1+Ld_j)$ and summing, exactly as in the proof of
0220 Theorem~\ref{art:certificate}, bounds $\sum_{k=J}^{N-1}q_k^{-1}$ by a constant
0221 times $N-J+1$. This contradicts Theorem~\ref{art:reciprocal-growth}.
0222 \end{proof}

```

## E9. The geometric construction in the appendix

`paper/appendices/planar_geometry.tex:40–123`; article pp. 34–35.

```text

0040 \emph{Corner motion.}
0041 At a nonsmooth point of $C$, the local branch-value map
0042 $x\mapsto(f_1(x),f_2(x))$ has nonsingular derivative. The inverse function
0043 theorem gives a $C^2$ curve $p_j(t)$ characterized by
0044 $f_1(p_j(t))=f_2(p_j(t))=t$ for $t$ near $\ell$. Its $C^1$ velocity
0045 $v_j(t)=p_j'(t)$ satisfies
0046 \begin{equation}\label{art:corner-velocity}
0047  \nabla f_1(p_j(t))^Tv_j(t)=
0048  \nabla f_2(p_j(t))^Tv_j(t)=1.
0049 \end{equation}
0050 In particular, this chart has only one nonsmooth point at level $\ell$.
0051 A smooth point has a neighborhood with no nonsmooth points. A finite cover
0052 of $C$ by smaller buffered charts therefore contains only finitely many
0053 level-$\ell$ corners. After shrinking their charts, the neighborhood of
0054 $C$, and the interval of levels, every nearby nonsmooth point lies on one
0055 of these finitely many curves. This is a compactness consequence of the
0056 charts, rather than an assumed finite bound on future branch changes.
0057 
0058 \emph{Joining their directions.}
0059 At a corner, the two active gradients generate its cone of supporting
0060 normals. Its unit directions form a compact arc of width less than $\pi$;
0061 by \eqref{art:corner-velocity}, every such unit normal $n$ has
0062 $n^Tv_j(t)>0$. Normal arcs at distinct level-$\ell$ corners are disjoint:
0063 a shared supporting normal would expose both points and their full segment
0064 in the boundary of $\{F\le\ell\}$. The strict-contour hypothesis excludes
0065 this. The finitely many arcs have positive angular separation.
0066 
0067 Choose fixed smooth angular cutoffs $0\le\chi_j\le1$ with disjoint supports,
0068 equal to one on slightly enlarged normal arcs. Shrink the level interval so
0069 that these plateaus contain the whole moving arcs and each support still
0070 satisfies $n^Tv_j(t)>0$ uniformly. With
0071 $n(\theta)=(\cos\theta,\sin\theta)$ and
0072 $T(\theta)=(-\sin\theta,\cos\theta)$, define
0073 \begin{equation}\label{art:planar-height}
0074  h(t,\theta)=1+\sum_j\chi_j(\theta)
0075                    \bigl(n(\theta)^Tv_j(t)-1\bigr).
0076 \end{equation}
0077 Because at most one cutoff is nonzero, this is a convex combination of
0078 positive quantities. Thus $h$ is bounded and bounded away from zero on the
0079 chosen compact level interval. It is $C^1$ in $t$, smooth in $\theta$, and
0080 its derivatives used below are bounded. No convex-support-function property
0081 of $h$ is needed.
0082 
0083 At a smooth point, put
0084 $n(\theta(x))=\nabla F(x)/\norm{\nabla F(x)}$ and define
0085 \begin{equation}\label{art:planar-field-formula}
0086  w(x)=h(F(x),\theta(x))n(\theta(x))
0087        +h_\theta(F(x),\theta(x))T(\theta(x)).
0088 \end{equation}
0089 All expressions are periodic, so no global choice of angle is required.
0090 Near the $j$th switching curve the relevant cutoff equals one and all others
0091 vanish. Consequently $h=n^Tv_j$, $h_\theta=T^Tv_j$, and
0092 \begin{equation}\label{art:planar-corner-field}
0093  w(x)=v_j(F(x)).
0094 \end{equation}
0095 This holds on both smooth sides in a whole neighborhood of the curve.
0096 Use the same formula on the curve itself. It provides a continuous, locally
0097 Lipschitz extension across the gradient jump, while the field is $C^1$
0098 elsewhere. Smaller compact buffers give uniform field and derivative bounds.
0099 At a smooth point,
0100 \[
0101  \nabla F(x)^Tw(x)=\norm{\nabla F(x)}h(F(x),\theta(x))>0;
0102 \]
0103 at a corner every subgradient pairs to one by
0104 \eqref{art:corner-velocity}. On sufficiently small buffers of $C$, these
0105 pairings have a uniform positive lower bound. One way to see the needed
0106 uniform gradient bound away from zero is the supporting inequality
0107 $\norm{g}\norm{x-x_*}\ge F(x)-F_*$ on the compact buffer, where $x_*$ is
0108 any minimizer and the value gap stays positive. This proves the visibility
0109 and common-pairing assertions.
0110 
0111 The specific angular formula has a crucial derivative cancellation:
0112 \begin{equation}\label{art:planar-tangent-cancellation}
0113  \partial_\theta(hn+h_\theta T)=(h+h_{\theta\theta})T.
0114 \end{equation}
0115 Thus at a smooth point the derivative of $w$ maps the tangent line of a
0116 level curve into that same line. In the orthonormal basis $(T,n)$,
0117 \[
0118  Dw=\begin{pmatrix}a&b\\0&e\end{pmatrix}
0119 \]
0120 with bounded coefficients. The formula $hn+h_\theta T$ is classical in
0121 normal-angle geometry \cite{geom_Bogosel2023}; Bogosel gives its explicit
0122 form \preprintcite[Section~2, equation~(4)]{Bog22}. Here its derivative cancellation
0123 is used for a comparison field, without a convexity requirement on $h$.

```

## E10. Main-text nondegeneracy assumptions and interpretation

`paper/sections/local.tex:245–318`; article pp. 19–21.

```text

0245 \subsection{Nondegenerate smooth maxima and an explicit nonradial basin}
0246 
0247 The extra affine-correctness condition can be verified from the active
0248 models at the minimizer. Positive optimal multipliers ensure that an affine
0249 balance cannot lose a branch nearby without losing stationarity; affine
0250 independence makes that balance unique and continuous. In the plane these
0251 same assumptions leave at most two active branches at a noncritical point,
0252 which supplies the required regular switching.
0253 
0254 \begin{corollary}[Nondegenerate planar smooth maxima]\label{art:planar-max}
0255 Let $F:\R^2\to\R$ be finite and convex with a unique minimizer $x_*$. Near
0256 $x_*$ suppose $F=\max_{1\le i\le m}f_i$, where the branches are convex and
0257 $C^2$. Suppose sufficiently low positive sublevels are strictly convex in
0258 the boundary-segment sense of Theorem~\ref{art:planar-cluster}. For the
0259 active set $I_*$ at $x_*$, suppose the gradients are affinely independent
0260 and admit weights
0261 \[
0262  \lambda_i^*>0,\qquad \sum_{i\in I_*}\lambda_i^*=1,
0263  \qquad \sum_{i\in I_*}\lambda_i^*\nabla f_i(x_*)=0.
0264 \]
0265 Then some $\varepsilon>0$, chosen independently of $H_0$ and the valid
0266 line-search constants, satisfies
0267 \[
0268  F(x_0)<F_*+\varepsilon
0269  \quad\Longrightarrow\quad F(x_k)\to F_*,\qquad x_k\to x_*
0270 \]
0271 for every infinite admissible full-BFGS run. A common positive lower Hessian
0272 bound on the locally relevant branches suffices for the contour hypothesis.
0273 \end{corollary}
0274 \begin{proof}
0275 Discard the branches inactive at $x_*$ by their strict value gaps. Let $A(x)$
0276 have columns $(\nabla f_i(x),1)$ for $i\in I_*$. Affine independence makes
0277 $A(x_*)$ full column rank, and this persists nearby. If
0278 $A(p)\lambda=(0,0,1)^T$ is solvable, its unique solution is
0279 \[
0280  \lambda(p)=(A(p)^TA(p))^{-1}A(p)^T(0,0,1)^T.
0281 \]
0282 This expression is continuous and equals $\lambda^*$ at $x_*$. Shrink the
0283 neighborhood until all its coordinates are positive. The subdifferential
0284 of a finite smooth maximum is the convex hull of its active gradients.
0285 Indeed, differentiating the finite maximum in a direction gives the maximum
0286 of the active gradient pairings. Every convex combination of those gradients
0287 supports the objective locally; convexity extends the supporting inequality
0288 globally by taking a short initial segment toward any proposed violating
0289 point. Conversely, a subgradient outside their convex
0290 hull could be strictly separated from that hull by a direction, contradicting
0291 the directional-derivative inequality for a subgradient.
0292 An affine representation of zero using gradients active at $p$, extended by
0293 zero on inactive indices, must equal $\lambda(p)$. It therefore uses every
0294 index and is a convex representation of zero. Thus every nearby
0295 affine-critical point is a minimizer.
0296 
0297 At most three planar gradients are affinely independent. Away from affine
0298 criticality, three cannot be active, since their affine hull would be all of
0299 $\R^2$. One active branch gives a smooth chart. For two active branches their
0300 gradients are distinct; if they were linearly dependent, their affine line
0301 would contain zero. Thus the gradients are independent, and the other
0302 branches have strict gaps. This gives the required convex two-branch chart.
0303 
0304 Lemma~\ref{art:localization} now puts a sufficiently low compact sublevel
0305 inside the chosen neighborhood, with its upper level also below the threshold
0306 for strict contours. Apply Corollary~\ref{art:planar-convergence}.
0307 If all relevant branch Hessians have a common positive lower bound on a
0308 convex neighborhood, subtracting the corresponding positive quadratic
0309 makes every branch convex. Their maximum is therefore strongly convex
0310 there. A sufficiently low sublevel lies in that neighborhood and cannot have
0311 a nontrivial boundary segment, proving the last assertion.
0312 \end{proof}
0313 
0314 The multiplier geometry is related to the nondegeneracy used in local bundle
0315 Newton analysis \preprintcite[Propositions~5.5--5.6]{LW} and in Gebken's
0316 criticality results \cite{BG}.
0317 Here the full-BFGS conclusion is derived without assumed iterate or matrix
0318 asymptotics. The contour and planar restrictions remain explicit.

```

## E11. Scaling explanation and transition to raw spline data

`paper/sections/failure.tex:225–268`; article pp. 26–27.

```text

0225 \subsection{Matching the spatial scale, objective scale and initial matrix}
0226 A change of scale also changes which inverse matrix represents the same
0227 search direction. This simple covariance explains both local constructions.
0228 Suppose, near the current and queried points under consideration, that
0229 \begin{equation}\label{art:matched-local-model}
0230  F(p+\lambda z)=C+\sigma\mathcal G(z),\qquad \lambda,\sigma>0.
0231 \end{equation}
0232 Differentiation gives $g_F=(\sigma/\lambda)g_{\mathcal G}$. Consequently,
0233 for the same candidate length, the corresponding inverse matrix and step are
0234 \begin{equation}\label{art:matched-scaling}
0235  H_F=\frac{\lambda^2}{\sigma}H_{\mathcal G},\qquad
0236  p_F=\lambda p_{\mathcal G},\qquad s_F=\lambda s_{\mathcal G}.
0237 \end{equation}
0238 At an accepted pair $y_F=(\sigma/\lambda)y_{\mathcal G}$. Thus
0239 $y_F^Ts_F=\sigma y_{\mathcal G}^Ts_{\mathcal G}$; the two projection
0240 factors in the inverse update are identical, and its rank-one term is
0241 multiplied by $\lambda^2/\sigma$. This proves the matrix relation in
0242 \eqref{art:matched-scaling} again after the update. Function differences
0243 and all gradient--step products are multiplied by $\sigma>0$, so the
0244 Armijo and weak-Wolfe comparisons, including their strict signs, agree.
0245 
0246 This is a covariance calculation, not an existence theorem for a local
0247 trajectory. To transfer a particular run, the local model must cover the
0248 current point and every candidate the search actually visits. Under that
0249 containment, induction on the bracket decisions transfers the full trial
0250 tree, and induction on accepted steps transfers the matrices. We verify
0251 that containment separately in each construction below.
0252 
0253 The choice $\sigma=\lambda^2$ is decisive: it leaves the initial matrix
0254 unchanged. In the first embedding, the corner's objective height is $a_n^3$
0255 and its affine slopes are $a_n^2g_i$. Taking spatial scale
0256 $\lambda=a_n^2$ gives $\sigma=a_n^4=\lambda^2$, so every copy starts
0257 with $I$. Its affine neighborhood has width proportional to $a_n$, much
0258 larger than the entire copied trial tree, whose width is proportional to
0259 $a_n^2$. This separation of scales makes all-query containment possible.
0260 
0261 \subsection{Convex interpolation that leaves room for every query}
0262 We now construct the scalar functions that implement this design. Their node
0263 values are $a_n^3$ and their node slopes are $a_n^2$. A monotone derivative
0264 connects neighboring nodes and is constant on a neighborhood of each node.
0265 The constant regions create the local affine corner; the cubic transition
0266 makes the second derivative continuous and globally Lipschitz even as the
0267 nodes accumulate at zero. The following formulas fix the construction
0268 completely.

```

## E12. Explicit gradients at the true minimizer

`paper/sections/failure.tex:355–382`; article pp. 28–29.

```text

0355 \subsection{One objective and a uniform induction over all queries}
0356 Define
0357 \begin{equation}\label{art:upper_objective}
0358  F(u,v)=\max\{\varphi_2(u),\varphi_2(-u-v/8),
0359                     \varphi_{b_*}(cu+dv),v\}.
0360 \end{equation}
0361 The Hessian of each of the first three branches is a nonnegative scalar
0362 multiple of $g_ig_i^T$. Equation~\eqref{art:scalar_curvature} gives the
0363 upper bounds $51$, $51(65/64)<52$, and $12$, respectively, on their
0364 operator norms; the last branch has zero Hessian. Their Hessians are
0365 globally Lipschitz because $\varphi_b''$ is Lipschitz and the arguments
0366 are linear. The first two scalar arguments are independent, so their
0367 coercivity makes every sublevel of $F$ compact. Nonnegativity and their
0368 unique scalar zeros show $F(x)=0$ exactly at $x=0$. At zero the first
0369 three gradients vanish and the last is $(0,1)^T$, giving
0370 $F'(0;h)=\max\{0,h_2\}$; thus the minimizer is nonsmooth.
0371 
0372 Let $p_n=a_n(2,-32)^T$. The first two scalar arguments at $p_n$ equal
0373 $2a_n$, and the third equals $b_*a_n$. Consequently
0374 \begin{equation}\label{art:upper_local_model}
0375  F(p_n+h)=a_n^3+a_n^2G(h)
0376  \quad\hbox{if } |g_i^Th|\le a_n/2 (i=0,1,2).
0377 \end{equation}
0378 Indeed, the first three branches are on their affine regions and each
0379 has value at least $a_n^3/2$. The first two slab inequalities imply
0380 $|h_1|\le a_n/2$ and $|h_2|\le8a_n$, so the fourth branch is negative.
0381 In particular $F(p_n)=a_n^3$ and
0382 $F'(p_n;(-1,16)^T)=-a_n^2<0$.

```

## E13. Counterexample interpretation and limits

`paper/sections/failure.tex:464–490`; article pp. 30–31.

```text

0464 The proof in Appendix~\ref{art:lower_curvature} has the same sequence of
0465 tasks as the first construction. It starts from the explicit strongly convex
0466 objective $Q_\mu(z)=\mu\|z\|^2/2+G(z)$, whose true minimizer is away from
0467 the wrong corner. A normalized three-step return map has the original seed
0468 as a hyperbolic boundary fixed point. Its stable manifold contains positive
0469 scale states, yielding an actual perturbed bad orbit. The seed's strict
0470 finite margins ensure that the same accepted and rejected trial lists
0471 persist along that orbit. No rounded initial state is asserted to lie on
0472 the stable manifold.
0473 
0474 For the local embedding the scalar node values are now $a_n^2$ and the
0475 node slopes $a_n$. The resulting model is
0476 $F(p_n+a_nz)=a_n^2(C_*+Q_\mu(z))$, so
0477 $\lambda=a_n$, $\sigma=a_n^2$ and again
0478 $\lambda^2/\sigma=1$. We choose one entire perturbed orbit small enough
0479 for every query to fit the affine scalar regions. Its one initial SPD
0480 matrix is then used in every copy; one fixed affine change makes it $I$.
0481 The faster variation of the scalar derivative retains global $C^{1,1}$
0482 regularity but prevents second differentiability at the accumulation point.
0483 This is why the theorem does not supply a finite strongly convex $C^2$
0484 local counterexample.
0485 
0486 The two constructions separate upper branch regularity from positive lower
0487 curvature. Their common mechanism is a local copy of an actual bad query
0488 tree; the different scalar scales determine which regularity survives at
0489 the accumulation point. The remaining convergence questions are discussed
0490 next.

```

## E14. Table/figure currently carrying the cycle illustration

`paper/sections/failure.tex:110–181`; article pp. 24–25.

```text

0110 \begin{lemma}[Exact cycle and strict trial decisions]\label{art:seed_cycle}
0111 The matrices in \eqref{art:seed_matrices} are positive definite, and
0112 \[
0113  \mathcal B(I,g_0,g_1,1)=M_1,\qquad
0114  \mathcal B(M_2,g_2,g_0,1/16)=\rho I,\qquad z_3=\rho z_0.
0115 \]
0116 At $z_j$, $j=0,1,2$, the unique active gradient is $g_j$.
0117 With $p_j=-M_jg_j$, the entire line-search query list is
0118 Table~\ref{art:trial_table}. At every rejection the objective strictly
0119 exceeds its current value. At every acceptance,
0120 \begin{equation}\label{art:seed_margins}
0121  G(z_j)+\tfrac13g_j^Ts_j-G(z_{j+1})>0,\qquad
0122  g_{j+1}^Ts_j>0>g_j^Ts_j,
0123 \end{equation}
0124 where $g_3=g_0$. All listed queries and the three starting points have a
0125 unique active branch and satisfy
0126 \begin{equation}\label{art:seed_query_bounds}
0127  |g_i^Tz|<3 (i=0,1,2),\qquad z_2<2,\qquad G(z)>0.
0128 \end{equation}
0129 Here $z_2$ in the middle inequality denotes the second coordinate.
0130 \end{lemma}
0131 
0132 \begin{table}[t]
0133 \centering
0134 \begin{tabular}{ccccc}
0135 \hline
0136 Phase $j$ & Trial $\alpha$ & Active branch & $10^4G(z_j+\alpha p_j)$ & Decision\\
0137 \hline
0138 0&1&1&$(1218,1219)$&accept\\
0139 1&1&0&$(3845,3846)$&reject\\
0140 1&$1/2$&0&$(1364,1365)$&reject\\
0141 1&$1/4$&2&$(723,724)$&accept\\
0142 2&1&0&$(6687,6691)$&reject\\
0143 2&$1/2$&0&$(3406,3408)$&reject\\
0144 2&$1/4$&0&$(1765,1767)$&reject\\
0145 2&$1/8$&0&$(944,946)$&reject\\
0146 2&$1/16$&0&$(534,536)$&accept\\
0147 \hline
0148 \end{tabular}
0149 \caption{Rational enclosures and the deterministic trial tree for the
0150 algebraic seed. Every rejection is an Armijo rejection. The intervals are
0151 enclosures, not rounded approximations asserted to be exact values.}
0152 \label{art:trial_table}
0153 \end{table}
0154 
0155 The proof of the lemma, including the root isolation, matrix closure and
0156 rational certificate, is in Appendix~\ref{art:seed_certificate}. The logic
0157 of the search can already be read from its margins. Every rejected candidate
0158 has a value larger than the current value, so it fails Armijo for every
0159 $c_1>0$. At each accepted candidate the decrease exceeds one third of the
0160 predicted decrease, while the new directional derivative is positive and
0161 the old one is negative. Hence Armijo holds for $c_1\le1/3$ and weak Wolfe
0162 holds for every $c_2>0$. Thus the displayed lengths are outputs of the
0163 specified search for the entire parameter range in
0164 Theorem~\ref{art:local-failure}; no accepted-length sequence is assumed.
0165 The routine never needs a Wolfe rejection on this example.
0166 
0167 Figure~\ref{art:cycle-figure} displays this unit-first geometry: phase zero
0168 accepts its first query, while the next two phases bisect past the rejected
0169 candidates before reaching their accepted points. The right panel includes
0170 all those rejected candidates.
0171 
0172 \begin{figure}[t]
0173 \centering
0174 \includegraphics[width=\textwidth]{figures/cycle_trials.pdf}
0175 \caption{The accepted three-step seed cycle (left), with closure
0176 $z_3=\rho z_0$, and every rejected candidate point (right). The rendering
0177 uses the rational center of the certified root box. It illustrates the
0178 certified trial geometry; it is not a proof of exact equality or of
0179 membership in the stable manifold used for the perturbed construction.}
0180 \label{art:cycle-figure}
0181 \end{figure}

```

## E15. Ending and audit/disclosure voice

`paper/sections/verification.tex:1–58`; article pp. 31–32.

```text

0001 \section{Synthesis, verification and the remaining questions}\label{art:verification}
0002 
0003 The mixed benchmark $u^2+|v|$ now has a whole-sequence convergence answer.
0004 The centered-family argument places it within a broader global theory;
0005 locally, finite polyhedral geometry controls the inward model error, while
0006 a moving comparison field handles the three-quadratic example's curved
0007 switches even when its radial secant condition fails. The common mechanism
0008 uses the principal-minor hierarchy and comparison energies to detect the
0009 remaining objective gap without a full spectral description of the BFGS
0010 matrices. The geometric conditions are sufficient, not necessary.
0011 
0012 The implemented counterexamples show why finite smooth formulas alone do
0013 not ensure local convergence. One regime has four convex $C^{2,1}$ branches
0014 with bounded Hessians; the other has four uniformly strongly convex
0015 $C^{1,1}$ branches. Each has one fixed objective with bad starts arbitrarily
0016 near its own minimizer, under the respective search parameters in
0017 Theorems~\ref{art:local-failure} and~\ref{art:local-failure-lower}.
0018 The local embeddings provide this conclusion; the simpler polyhedral and
0019 quadratic-plus-maximum wrong-corner examples establish global failure.
0020 The argument follows the actual update and every rejected query, so these
0021 are implemented trajectories, not merely prescribed accepted sequences.
0022 
0023 The two local negatives do not give a counterexample with finitely many
0024 uniformly strongly convex $C^2$ branches through the minimizer. The planar
0025 positive theorem settles a nondegenerate subclass, leaving that broader
0026 local question open. The constructions concern the specified weak-Wolfe
0027 implementation; they do not establish failure for every search routine or
0028 for strong Wolfe. Exceptional deterministic starts also do not establish
0029 failure with positive probability, and the accumulating local constructions
0030 have no finite semialgebraic description. Lewis--Overton's almost-sure
0031 stationarity, all-trial-value rate and spectral-identification challenge
0032 \cite[Challenge~7.1]{LO} therefore remains outside these conclusions.
0033 Convergence of an infinite admissible run is distinct from indefinite
0034 differentiable execution; a zero gradient is successful termination.
0035 
0036 \paragraph{Formal verification and reproducibility.}
0037 The companion records Lean~4.19.0 proofs with pinned mathlib, exact
0038 statement-to-source correspondence, and compiler and transitive-axiom audit
0039 logs. The permitted foundational dependencies are propositional
0040 extensionality (\texttt{propext}), classical choice
0041 (\texttt{Classical.choice}) and quotient soundness (\texttt{Quot.sound}).
0042 The audits reject \texttt{sorryAx}, custom mathematical axioms and reachable
0043 unsafe or partial proof artifacts. The principal-minor theorem concerns
0044 actual matrices and determinants, and the negative proofs include the search
0045 decisions and all-query induction. The article's proofs and rational
0046 certificate can also be read independently of Lean. The kernel and execution
0047 environment remain trusted. Formal checking does not establish foundational
0048 consistency, publication priority, fidelity of every prose paraphrase or
0049 floating-point robustness; author-side correspondence review is separate
0050 from independent human peer review.
0051 
0052 \paragraph{AI assistance and author review.}
0053 Large language models assisted theorem development, proof reconstruction,
0054 formalization, literature searches, software and writing. This assistance
0055 was substantive, beyond grammar editing. Human authors must review the
0056 claims, citations, novelty assessment and disclosure before submission;
0057 this author-review edition asserts neither author consent nor completed
0058 independent human review.

```

## E16. Updated companion narrative

`companion/research_story.tex:1–67`; companion PDF pp. 2–3.

```text

0001 The question is what convergence ordinary full BFGS can guarantee when a
0002 convex objective has gradient jumps. Its practical success invites a
0003 theory, but the smooth argument cannot simply treat every secant as a
0004 bounded Hessian acting on a short step. Lewis--Overton's experiments and
0005 Challenge~7.1 place this problem in a broader almost-sure semialgebraic
0006 setting~\cite{LO}. The present work gives deterministic positive and negative
0007 answers for specified convex classes. It does not claim to settle every
0008 part of that challenge.
0009 
0010 The mixed objective $F(u,v)=u^2+|v|$ gives a concrete measure of progress.
0011 Guo--Lewis developed extensions of Powell's smooth-convex argument and
0012 proved convergence on the Euclidean norm~\cite[Theorems~3.2, 4.1, 4.3 and
0013 Corollary~4.2]{GL18}. Their Corollary~4.4 proves only that a subsequence for
0014 the mixed objective approaches a point on $v=0$, leaving whole-sequence
0015 convergence to zero open. The horizontal error $u^2$ can remain positive on
0016 that line. Gebken's published 2026 introduction still identifies this
0017 benchmark as unresolved, while its criticality theorem assumes iterate
0018 and matrix behavior~\cite[Theorem~3.1 and (B1)]{BG}.
0019 
0020 The centered smooth--sublinear result here proves that every infinite
0021 admissible full-BFGS run on $u^2+|v|$ converges to zero, for arbitrary
0022 positive-definite initialization and fixed valid Armijo--weak-Wolfe
0023 parameters. It is a consequence of a family argument in arbitrary dimension.
0024 The sublinear part is modeled exactly toward its center; adding a locally
0025 $C^{1,1}$ convex term leaves only a quadratic inward remainder. Compact
0026 initial sublevels inside the structural region give value convergence,
0027 and uniqueness gives convergence of the whole sequence. The same route
0028 covers coercive degree-one homogeneous functions, including coercive finite
0029 maxima of linear functions. The Euclidean norm is an attributed known case.
0030 The full noncompact homogeneous value alternatives are retained separately:
0031 value convergence does not imply bounded iterates, and it does not subsume
0032 Xie--W\"achter's finite detection of unbounded descent in the two-piece
0033 affine model~\cite[Theorem~IV.1]{XW}.
0034 
0035 Local convergence extends this positive picture. Finitely many polyhedral
0036 cells with smooth extensions supply a uniform inward model after a low
0037 sublevel traps the iterates near the minimizer. The algorithm need not
0038 identify a cell. Curved switching sets can defeat that radial condition;
0039 the planar theorem constructs a comparison field along positive contours
0040 instead. Its nondegenerate smooth-max corollary and explicit three-quadratic
0041 example show a convergence conclusion beyond the radial class. The
0042 fixed-normal theorem in arbitrary dimension and the flat-contour parabolic
0043 family use different hypotheses and remain independent parts of the theory.
0044 
0045 The negative results establish a complementary limitation. A fixed unit-first
0046 implementation can generate a shrinking cycle around a nonstationary corner.
0047 The construction certifies every rejected and accepted query, and then embeds
0048 copies so that one fixed objective has failing starts arbitrarily close to
0049 its unique minimizer, all with identity initialization. One embedding has
0050 four globally convex $C^{2,1}$ branches with bounded Hessians and no uniform
0051 positive lower-curvature assumption. A different embedding preserves uniform
0052 strong convexity with $C^{1,1}$ branches that lose second differentiability at
0053 the accumulation point. These are two distinct exclusions of deterministic
0054 neighborhood guarantees. They neither establish positive-probability failure
0055 nor produce a finite uniformly strongly convex $C^2$ local counterexample.
0056 
0057 The common analytical tool is an adjacent-degree hierarchy for actual
0058 principal determinants of full-BFGS matrices. Building on the classical
0059 trace/determinant approach~\cite{FND_P76,FND_BN89,FND_N92}, it forces the
0060 arithmetic mean of reciprocal metric-gradient values to diverge under the
0061 stated bounded-gradient and vanishing-decrease hypotheses. A comparison
0062 energy turns this matrix restriction into convergence when objective
0063 geometry preserves visibility of nonoptimality, controls the secant
0064 correction and permits transport at a summable cost. Matrix degeneration
0065 is allowed throughout. The radial and moving-field arguments demonstrate
0066 ways this mechanism succeeds; the scalar nonnecessity results prevent it
0067 from being read as a complete characterization.

```

## E17. Companion archive/reference scope

`companion/correspondence.tex:1–67`; companion Appendix B.

```text

0001 The machine-readable correspondence is part of this report's source release.
0002 It is designed to expose whole theorem contracts and all dependencies, rather
0003 than offer a sample export as a substitute for a proof.
0004 
0005 The frozen corrected mathematical source is Git commit
0006 \path{00362c0249262d182866f14bac756a7c4edac95c}, with paths and hashes in
0007 \path{editorial/BASELINE.json}. The narrative revision starts from the initial
0008 author-review release at \texttt{7f53b4c}; its source manifest, original
0009 contract reviews and unchanged earlier PDFs are preserved under
0010 \path{editorial/narrative_rebuild/} and \path{release/history/20260912_initial/}.
0011 All 172 corrected source spans remain present with their complete exports.
0012 The new opening changes their scientific presentation and reading order,
0013 not their mathematical assertions.
0014 
0015 The revised article independently proves global centered and coercive
0016 homogeneous convergence, local finite-partition and planar results, the
0017 actual-matrix framework and both finite-branch local counterexamples. The
0018 noncompact homogeneous alternatives, fixed-normal geometry, flat-contour
0019 parabolic family, lifting, rates and scalar baseline remain separate
0020 companion results. The infinite constant-Hessian family in
0021 Chapter~\ref{comp:L} also remains here after its removal from the article's
0022 main theorem selection. None of these incomparable results is treated as
0023 superseded merely because the article selects a smaller statement set.
0024 
0025 \begin{longtable}{p{.32\textwidth}p{.6\textwidth}}
0026 \toprule Record & Purpose\\\midrule\endhead
0027 \path{SOURCE_CORRESPONDENCE.json} & Every corrected source span, classification,
0028 new chapter and line location, and its full formal-export list.\\
0029 \path{editorial/CLAIM_LEDGER.json} & Article statements, equations and substantive
0030 deductions, their proof locations and precise source/contract correspondences.\\
0031 \path{editorial/SUPERSESSION_LEDGER.json} & Disposition of every source span;
0032 incomparable positive and negative results are retained.\\
0033 \path{bfgs_lean_stage1/master_report/DECLARATION_INDEX.json} & Exact Lean
0034 signatures, proof excerpts and type/value/structural dependencies of the source
0035 declarations.\\
0036 \path{bfgs_lean_stage1/master_report/PROOF_INDEX.html} & Human-readable original
0037 claim index, full exports, exact types and direct proof dependencies.\\
0038 \path{editorial/formal_audit/} & Preserved runner, actual fresh compiler and
0039 transitive audit evidence.\\
0040 \path{editorial/LITERATURE_LEDGER.json} & Source versions, access levels,
0041 point-of-use comparisons and unresolved attribution.\\
0042 \bottomrule
0043 \end{longtable}
0044 
0045 The formal source project remains in \path{bfgs_lean_stage1/}. Its pinned
0046 \path{lean-toolchain}, \path{lakefile.toml} and \path{lake-manifest.json}
0047 are authoritative. On a new supported system, run
0048 \texttt{bash scripts/bootstrap.sh} there, then the fresh audit command in
0049 Chapter~\ref{comp:E}. Network access is needed to obtain the pinned toolchain
0050 and dependencies when they are absent. The release archive omits those large
0051 caches and preserves the source tree's relative paths.
0052 
0053 To rebuild the documents from the repository root, run
0054 \texttt{bash editorial/build.sh}. The normal journal class used for the article
0055 is supplied under \path{editorial/vendor/svjour3/} with the original notices
0056 and download provenance. PDF figures are generated from stated mathematical
0057 data; their code is in \path{paper/figures/}. The figure computations are
0058 renderings, not additional formal proof premises. Build logs, page-level
0059 rendering evidence and editorial review findings are kept under
0060 \path{editorial/logs/} and \path{editorial/reviews/}.
0061 
0062 Source transformations preserve the corrected mathematical assertions.
0063 Exact Lean contracts can contain definitions that abbreviate substantial
0064 hypotheses; the declaration index exposes their definitions and dependency
0065 closure. Reading one exported name without expanding those contracts would
0066 not validate the prose. Correspondence review is a separate logical bridge
0067 from kernel checking, and author approval remains necessary before submission.

```

## E18. Compact archive scope

`SOURCE_ARCHIVE_README.md:1–52`; archive README.

```text

0001 # BFGS article and companion: compact LaTeX sources
0002 
0003 Snapshot from Git commit `91d30dadcfd0980472c3896be0c9fd83fc7d4db1`. All existing source files retain their
0004 repository-relative paths beneath the outer `BFGS-non-smooth/` directory.
0005 The article and companion mathematical text is unchanged.
0006 
0007 ## Build
0008 
0009 Extract the ZIP, enter `BFGS-non-smooth/`, and run:
0010 
0011 ```bash
0012 bash build_sources.sh
0013 ```
0014 
0015 Outputs: `paper/build/master.pdf` (46 pages) and
0016 `companion/build/master.pdf` (107 pages) in the tested TeX Live 2025 environment.
0017 The entry points are `paper/master.tex` and `companion/master.tex`.
0018 The script sets the included Springer class search path and fixed document
0019 metadata date. It compiles the already-generated companion sources directly.
0020 It does not require the original report generator or the Lean project.
0021 
0022 Use a LaTeX installation with latexmk, pdfLaTeX, Latin Modern, AMS packages,
0023 TikZ, microtype and the standard packages listed in the two preambles.
0024 Bibliographies are native `bibliography.tex` files; no BibTeX/Biber step is needed.
0025 Exact PDF bytes may vary with installed TeX/font/package versions.
0026 
0027 The required vector figure PDF is included as a source asset. Its reproducible
0028 Python/TikZ sources and exact seed data are also included. To regenerate it:
0029 
0030 ```bash
0031 bash build_sources.sh --regenerate-figures
0032 ```
0033 
0034 This optional step needs Python 3 (standard library only) and the LaTeX
0035 `standalone` package. It is drawing code, not a mathematical proof input.
0036 
0037 ## Scope
0038 
0039 This is a compact typesetting/source bundle. It excludes finished article and
0040 companion PDFs, build intermediates/logs, Git history, Lean/toolchain caches and
0041 the full formal audit/correspondence database. Paths mentioned in the manuscript
0042 for those research records refer to the full repository/research archive.
0043 No new formal verification is claimed by this typesetting package.
0044 
0045 The unmodified Springer class, option file, template, notices and provenance are
0046 retained under `editorial/vendor/svjour3/`. Their original rights notices apply;
0047 this bundle does not assert an additional licence for them or the research text.
0048 Human author metadata, approval and submission decisions remain reserved.
0049 
0050 `SOURCE_MANIFEST.json` gives SHA-256 hashes for every other archive member and
0051 expected hashes of the current reference PDFs. Fresh extraction-build evidence
0052 is recorded next to the ZIP in `BFGS_article_companion_LaTeX_sources.json`.

```
