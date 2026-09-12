# Article–companion notation map

The article uses one global notation convention for its common argument. The companion preserves the corrected source conventions chapter by chapter. Equal symbols in separate constructions need not denote equal objects. This map records notation changes only; exact hypotheses, dimensions and exported Lean types remain in `CLAIM_LEDGER.json`, `companion/SOURCE_CORRESPONDENCE.json` and the canonical declaration index.

## Shared BFGS notation

| Symbol | Meaning in the article | Companion location and cautions |
|---|---|---|
| $F$; occasionally $f$ | Finite real-valued convex objective on Euclidean space | Chapter 7 uses lower-case $f$ for homogeneous objectives; the same algorithm applies. |
| $n$ | Ambient dimension in the positive theory | Also a scale index in the negative construction; that construction has ambient dimension two. |
| $x_k$, $g_k=\nabla F(x_k)$ | Accepted iterate and its ordinary gradient | Chapters 2–13 retain this convention. Accepted gradients are nonzero on an infinite admissible run. |
| $H_k\succ0$, $B_k=H_k^{-1}$ | Stored inverse-Hessian approximation and its inverse | $B_k$ is an algebraic inverse, not the actual objective Hessian. No matrix limit is assumed. |
| $p_k=-H_kg_k$, $\alpha_k>0$ | Search direction and accepted length | A trial length is also denoted $\alpha$; a trial is not assumed accepted. |
| $s_k=x_{k+1}-x_k=\alpha_kp_k$ | Executed step | Pair statements use $s=z-x$. |
| $y_k=g_{k+1}-g_k$ | Gradient difference | Pair statements use $y=h-g$, $g=\nabla F(x)$ and $h=\nabla F(z)$. |
| $c_1,c_2$, $c=1-c_2$ | Fixed Armijo and weak-Wolfe constants, $0<c_1<c_2<1$ | The seed's algebraic coordinate $c$ is a different, local symbol. |
| $q_k=g_k^TH_kg_k$ | Positive metric quadratic form | In the lower-curvature construction, $q_i=g_i-\mu c_*$ is instead a vector of shifted slopes. |
| $d_k=-g_k^Ts_k=\alpha_kq_k$ | Predicted decrease | The seed coordinate $d\approx-1.02523$ is unrelated and has no iteration subscript. |
| $\Delta_k=F(x_k)-F(x_{k+1})$ | Actual objective decrease | $c_1d_k\le\Delta_k\le d_k$. |
| $t_k=y_k^Ts_k$ | Secant curvature | $t_k\ge(1-c_2)d_k>0$. Scalar ramp coordinates called $t$ are unrelated. |
| $M_k=B_k-g_kg_k^T/q_k$ | PSD remainder annihilating $s_k$ | The seed phase matrices $M_0,M_1,M_2$ are inverse-BFGS matrices, not these PSD remainders. |
| $e_j(H)$ | Sum of actual order-$j$ principal determinants | Chapter 2 also identifies these with elementary symmetric eigenvalue polynomials; $e_{n+1}=0$. |
| $\beta_k=t_k/d_k$ | Positive normalized secant curvature in the hierarchy | Appendix seed identities use $\beta,\gamma$ for algebraic lengths that specialize to $1/4,1/16$. |
| $S_N=\sum_{k<N}q_k^{-1}$ | Reciprocal sum | This shorthand is most prominent in companion Chapter 6; it is not a smooth subspace $S$. |

An admissible-run theorem assumes an infinite sequence of successful accepted steps. The deterministic negative implementation starts each search at one, then doubles or bisects its bracket. Its proof accounts separately for all accepted and rejected queries. No notation turns arbitrary eligible pairs into an actual BFGS trajectory.

## Comparison energy and geometric conditions

| Symbol | Meaning | Scope distinctions |
|---|---|---|
| $x_*$, $F_*$ | A minimizer and minimum value | A fixed reference point in an energy identity need not be a minimizer until a gap inequality explicitly uses that assumption. |
| $r_x=x-x_*$, $r_k=x_k-x_*$ | Radial reference displacement | The lower-curvature scale ratio $r=1/128$ and a return-map normalization factor also named $r$ are different local scalars. |
| $E_k=r_k^TB_kr_k$ | Fixed-reference energy | In the PSD-field proof, $E_k=\operatorname{tr}(B_kW(x_k))$ is the corresponding generalized energy. |
| $a_k=g_k^Tr_k$ | Scalar supporting-gradient pairing | In a moving frame, $a_k=V_k^Tg_k$ is a vector; in both scalar embeddings $a_n$ is a geometric scale. |
| $R_k=(y_k^Tr_{k+1})^2/t_k$ | Radial correction | $R$ may also denote a radius bound, while seed polynomial $R=c-8d$ is local to its certificate. |
| $K=\{F\le b\}$, $K_\eta$ | Compact sublevel and its positive-gap band | The level $b$ is not a scalar-interpolation parameter $b$ or normalized matrix-shape coordinate $b$. |
| $\Pi_s=I-ss^T/(s^Ts)$ | Euclidean projection perpendicular to a nonzero executed/pair step | Its denominator is valid on eligible pairs because $d>0$ implies $s\ne0$. |
| $W_\eta(x)\succeq0$ | Finite-valued comparison field on a band | It need not be SPD, bounded or continuous. It is objective data, not a stored BFGS matrix. |
| (V), (S), (T) | Visibility, secant control, projected transport | Companion Chapters 3 and 5 use these lettered names. The article uses named inequalities with the same roles. |
| $V_k$, $T_k$, $b_k$ | Moving frame, frame transport and step-parallel coefficients | $V_{k+1}=V_kT_k+s_kb_k^T$. Neither $T_k$ nor its cumulative product is a BFGS matrix. |
| $T$, $N$ in radial pairs | $T=(h-g)^T(z-x)$ and $N=(h-g)^T(z-x_*)$ | Radial $T$ is the same scalar as pair curvature $t$; it is unrelated to frame $T_k$ or seed polynomial $T=c^2-c+d^2$. |
| $D_F(z,x)$ | $F(z)-F(x)-\nabla F(x)^T(z-x)$ | Supporting-plane error; the gradient belongs to the second endpoint. This orientation is preserved in the radial proof. |
| (RS), (IR) | Radial-secant bound and inward modeling bound | The article denotes them by labeled formulas. Their quantifiers cover positive objective bands, with constants allowed to depend on the band. |
| $\tau$ | Inward fraction in the radial theorem | In the lower-curvature appendix $\tau>0$ is the physical normalization scale of the return map, not a radial fraction. |
| $\gamma$ | Finite convex degree-one function in centered objectives | Companion Chapter 8 also uses $\gamma(p)=\operatorname{dist}(0,\operatorname{aff}\partial F(p))$. These are separate contexts. |
| $\partial F$, $\operatorname{aff}\partial F$ | Convex subdifferential and its affine hull | Stationarity is $0\in\partial F$; affine criticality is $0\in\operatorname{aff}\partial F$. They are not interchangeable. |
| $V(p)$, $U(p)$, $a(p)$ | Jump span, its orthogonal complement, and nearest point to zero in the affine subgradient hull | Companion Chapter 8; $V(p)$ is a subspace, not the moving-frame matrix $V_k$. |
| $a$, $S=a^\perp$, $P_S$ | Fixed normal, tangential subspace and projection | Companion Chapter 11; its $A(x)$ is the common tangential gradient projection. |

## Exact seed shared by both negative constructions

The article's $G(z)=\max(g_0^Tz,g_1^Tz,g_2^Tz)$ and companion Chapters 12–13 use the same algebraically isolated $(c,d)$, gradients $g_0=(1,0)^T$, $g_1=(-1,-1/8)^T$, $g_2=(c,d)^T$, contraction factor $\rho$, phase matrices $M_j$, displacements $s_j$ and phase points $z_j$. The seed variables $U,V,R,K,T,Y$ are polynomial abbreviations local to the algebraic certificate. They are not the geometric subspaces, sublevel set, frame or curvature quantities of earlier chapters.

Here $j=0,1,2$ is the phase, $m\ge0$ counts full three-step cycles, and $n$ counts shrinking embedded copies. Thus $x_{3m+j}$ is a run iterate, while $x_0^{(n)}$ identifies the start of the $n$th separate run. The point $p_n$ is that run's nonstationary limit; it is distinct from the search direction $p_k$. The objective and initial matrix are fixed across those starts within each theorem.

## Upper-curvature scalar construction: article and Chapter 12

| Article | Companion Chapter 12 | Value or role |
|---|---|---|
| $\theta$ | $\vartheta$ | Scale ratio $1/16$. |
| $a_n=\theta^n$ | $a_n=\vartheta^n$ | Node scale. |
| $\varepsilon$ | $\epsilon_0$ | Ramp half-width $1/128$. |
| $t_b$ | $c_b$ | Ramp center $[1-(1+\theta+\theta^2)/b]/(1-\theta^2)$. |
| Ramp variable $v$ | Ramp variable $t$ | $(\xi-t_b+\varepsilon)/(2\varepsilon)$. |
| $P_b$, $J_b$ | $P_b$, $J_b$ | Cubic ramp and its integral; the parameter substitutions above identify them. |
| $\varphi_b$ | $\varphi_b$ | Convex $C^{2,1}$ scalar with node value $a_n^3$ and node derivative $a_n^2$. |
| $b\in\{2,b_*\}$ | Same | $b_*=2c-32d\in(33,34)$. |

The embedded starts are $p_n+a_n^2z_0$. Gradients and steps have scale $a_n^2$, while objective differences have scale $a_n^4$. The negative scalar side is cubic near zero; this is part of its $C^{2,1}$ regularity.

## Lower-curvature scalar construction: article and Chapter 13

| Article appendix | Companion Chapter 13 | Value or role |
|---|---|---|
| $\mu$ | $\mu$ | Fixed common quadratic coefficient $1/4096$ during the local embedding. |
| $c_*$, $q_i$, $b_i$ | Same | $c_*=(2,-32)^T$, $q_i=g_i-\mu c_*$, $b_i=q_i^Tc_*$. |
| $r$ | $r$ | Scalar scale ratio $1/128$, distinct from the upper construction's $1/16$. |
| $a_n=r^n$ | Same | Node scale in this second construction. |
| $\varepsilon$ | $\epsilon$ | Ramp half-width $1/1024$. |
| $t_b$ | $\vartheta_b$ | Ramp center $[1-(1+r)/b]/(1-r)$. It is neither the scale ratio nor the upper ramp center. |
| Ramp variable $v$ via the reused cubic-ramp formula | Ramp variable $t$ | $(\xi-t_b+\varepsilon)/(2\varepsilon)$. |
| $\psi_b$ | $\varphi_b$ | Convex $C^{1,1}$ scalar with node value $a_n^2$ and derivative $a_n$. The article deliberately renames it to distinguish the two constructions. |
| $P_b$, $J_b$ | Same symbols | Reinstantiated with this construction's center and half-width; they are not numerically the upper-curvature ramps. |
| $Q_\mu=\mu\|x\|^2/2+G(x)$ | Same formula | Strongly convex seed objective, whose bad orbit is supplied by the stable-manifold theorem. |
| $\mathcal T_\mu$ | $\mathcal T_\mu$ | Five-dimensional normalized return map in $(z,b,e,\tau)$; here $b,e$ are matrix-shape coordinates. |
| $A=\bar H_0^{1/2}$ | Same fixed whitening change | $\widetilde F(z)=F(Az)$ converts the one common SPD initialization to identity. This $A$ is not a tangential gradient field. |

The local copy uses $p_n+a_n y$ and scales objective differences by $a_n^2$. The scalar's negative side is $x^2/2$, and its derivative is not differentiable at zero on the accumulating positive side. These functions therefore do not acquire the upper construction's $C^{2,1}$ regularity by a notation change. The separate constant-classical-Hessian alternative replaces the ramp by a step, the integral by a hinge, and the negative scalar side by $-x$; it has a countably piecewise-affine remainder, not the finite smooth-branch claim.

## Source navigation and formal representations

Companion Chapters 1–14 correspond to source IDs `I`, `M`, `T`, `R`, `G`, `F`, `H`, `A`, `C`, `Q`, `U`, `D`, `L`, `E`, respectively. Article labels use `art:`; retained source labels and formal namespaces keep their historical identifiers. Manually headed theorems in Chapters 7 and 11 are indexed as named statements even though their TeX does not use theorem environments.

Lean uses several concrete representations for vectors, matrices, linear maps and Euclidean quantities. This notation table does not identify distinct Lean types or equate a default function-space norm with a Euclidean norm. The expanded exact declarations and their definitions govern those representation bridges. Bibliographic notes and editorial scope sentences remain separately classified from mathematical theorem exports.
