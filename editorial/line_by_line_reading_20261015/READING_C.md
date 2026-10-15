# Line-by-line reading, reader C: `paper/sections/global.tex` (Section 4)

- **Files read (snapshot `$S/step2/snapshot/paper/`, = commit c8db802):** `sections/global.tex` (reported on, all 258
  lines); for definitions, hypotheses and cross-references also `master.tex`, `sections/introduction.tex`,
  `sections/geometry.tex`, `sections/energy.tex`, `sections/local.tex`, `sections/verification.tex`,
  `bibliography.tex`, `preprint_references.tex`, the register `editorial/lean_coverage/register/A_global.json`
  (plus the `A_local.json` ids quoted below), the companion chapters `companion/chapters/04_R.tex` and `07_H.tex`
  (for the two chapter pointers), and the Lean module
  `bfgs_lean_article/BfgsArticle/Coverage/Article/Global.lean` (statements and proofs of every declaration
  named in the register; read only, no Lean or lake process).
- **Literature checked at the point of use:** [GL18] (author PDF, Cornell): Corollary 4.2 = "Any BFGS sequence for
  the Euclidean norm on R^n converges to zero", Corollary 4.4 = subsequence converging to a point of v = 0, followed
  by "That conjecture remains open": matches global.tex:189-191 and 250-252. [LO] (author-hosted published PDF
  `nsoquasi.pdf`, journal pages 135-163): Section 5.1 is "The absolute value" (secant method on |x| with c_1 = 0 and a
  modified Wolfe test): matches "under their stated search conventions" (global.tex:252-254). [BB]: Bregman
  divergence, as used. Companion Chapter 4 ("Radial modeling and finite partitions", Theorem R:thm:equiv, both
  directions) and Chapter 7 ("Homogeneous objectives without compactness", the value dichotomy): match
  global.tex:93-94 and 255-258.
- **PDF pages:** 11-16 of `$S/baseline/paper.pdf` (Section 4 occupies pp. 11-15; p. 16 starts Section 5), rendered
  at 110 dpi, with zooms at 170-200 dpi of pp. 12-15.
- **Time spent:** about 25 minutes (03:10-03:35).
- **Scratch:** `checks.py` (exact checks with `fractions`, all pass), `count_olds.py` (occurrence counts of every
  old string below), page renders `page11.png`-`page16.png`, `p12_mid.png`, `p13_a.png`, `p14_top.png`,
  `p15_a.png`, `p15_b.png`.

## Summary

| Severity | Count | Findings |
|---|---|---|
| major | 0 | |
| minor | 2 | R-C-1 (gap: Corollary 1's proof covers only one of its two conditions), R-C-2 (reference to a theorem for a fact proved inside its proof) |
| cosmetic | 9 | R-C-3 to R-C-11 |

Every inference of the six proofs was recomputed (see "Checks performed" at the end); every statement holds as
printed, every Section 3 result is applied within its hypotheses, every constant is right, and the statements
agree with their register readings. The findings concern a missing invocation, a reference, unstated one-line
steps, notation and wording. No overfull line or broken display on pp. 11-16; the one typesetting point (no
end-of-proof marks) is article-wide.

## Findings

### R-C-1 — Corollary 1's proof treats only the radial condition (minor; gap / reference)

- **Where:** `sections/global.tex:98-109` (statement 98-102, proof 103-109).
- **Text:** statement "Under either condition, every admissible run starting in $K$ converges …"; proof
  "Equation~\eqref{art:radial-condition} gives secant control on eligible pairs."
- **Explanation:** the statement covers both \eqref{art:radial-condition} (14) and \eqref{art:inward-condition} (15),
  but the proof only uses (14); under (15) it needs Theorem~\ref{art:radial-equivalence} (Theorem 4) first, and the
  proof never invokes it. The printed proof therefore shows less than its statement (the repair is the theorem just
  above, and lines 94-95 announce that the article uses it, so a reader can fill it in). Also left implicit: an
  eligible pair in $K_\eta$ satisfies the hypotheses of (14), namely $F_*+\eta\le F(z)$, $F(z)\le F(x)-c_1d<F(x)$ and
  $T=t\ge\omega d>0$ (energy.tex:240-242), and in the notation of Section 4 $y^TW_\eta(z)y=(y^Tr_z)^2=N^2$, $t=T$.
- **Fix** (old string occurs once in global.tex):
  - old: `Equation~\eqref{art:radial-condition} gives secant control on eligible pairs.`
  - new: `By Theorem~\ref{art:radial-equivalence} we may assume \eqref{art:radial-condition};`
    `it gives secant control on eligible pairs in $K_\eta$, since these have`
    `$F(z)<F(x)$ and $T=t>0$.` (three source lines)
- **Register items:** A/global/proof/002 (and A/global/corollary/art:radial-convergence, whose Lean proof
  `radial_convergence` already does exactly this: `hcond.elim id (radial_equivalence …)`).

### R-C-2 — "The subgradient bound was proved in Theorem 3" (minor; reference)

- **Where:** `sections/global.tex:60`.
- **Text:** "The subgradient bound was proved in Theorem~\ref{art:certificate}; supporting"
- **Explanation:** the statement of Theorem 3 (energy.tex:270-278) contains no subgradient bound; the bound is a step
  of its proof (energy.tex:282-285: bound $F$ on $K+\epsilon\overline B$ and evaluate the supporting inequality at
  $x+\epsilon u$). A reader who looks up Theorem 3 does not find the claim. (The register note of
  A/global/proof/001 records the same reading as a "wording point".)
- **Fix** (old string occurs once; compatible with R-C-3):
  - old: `The subgradient bound was proved in Theorem~\ref{art:certificate}; supporting`
  - new: `The subgradient bound was proved in the proof of Theorem~\ref{art:certificate}; supporting`
- **Register items:** A/global/proof/001.

### R-C-3 — An unused Lipschitz claim in the proof of Theorem 4 (cosmetic; language)

- **Where:** `sections/global.tex:60-61`.
- **Text:** "supporting inequalities then give $|F(x)-F(z)|\le\Lambda\norm{x-z}$ on $K$."
- **Explanation:** true, but never used: the proof needs only $|N|\le2\Lambda R$ and $T-N\le2\Lambda R$
  (Cauchy-Schwarz with the subgradient and radius bounds) and $D_F\ge0$. The sentence is a leftover of the converse
  direction, where the companion does use it (companion 04_R.tex:127-129, "the Lipschitz bound on $K$ gives
  $F(z)\ge F(x)-GtR$"). A reader looks for its use in vain. (Lean: `lipschitz_on_K`, "not used later".)
- **Fix** (old string occurs once; apply after R-C-2, or on its own):
  - old: `; supporting` + newline + `inequalities then give $|F(x)-F(z)|\le\Lambda\norm{x-z}$ on $K$.`
  - new: `.`
- **Register items:** A/global/proof/001.

### R-C-4 — Unstated identity and loose wording in the case split of Theorem 4's proof (cosmetic; gap of exposition / language)

- **Where:** `sections/global.tex:71-86`.
- **Text:** (a) "compare the supporting plane at $x$ with the inward model at $z-\tau r_z$ to obtain";
  (b) "If $N<0$, reverse the endpoints and use the inward model at $x$:"; (c) "Thus there are
  $A\in[|N|,2\Lambda R]$ …"; (d) "When $M=0$, the same endpoint choice gives an even stronger estimate."
- **Explanation:** (b)-(c): the second display and the claims $A=T-N\ge|N|$, $A\le2\Lambda R$ rest on the identity
  $T-N=(h-g)^T(z-x)-(h-g)^T(z-x_*)=(g-h)^Tr_x$, the radial numerator of the reversed pair, which the proof does not
  state (the companion does, 04_R.tex:94-97: "$(g-h)^Tr_x=T-N\ge|N|$"); $T-N\ge|N|$ is also the only place where
  the sign of $T$ enters ($T\ge0$ holds anyway, by line 68). One line, but it is the step a reader must reconstruct
  to check both the display and the range of $A$.
  (a): the model is the inward model *at* $z$ (base point $z$, gradient $h$) *evaluated at* $z-\tau r_z$; the next
  sentence uses "at $x$" for the base point, so the two sentences use "at" differently. (d): in this proof
  "endpoints" means $x,z$ ("At differentiable endpoints", "reverse the endpoints"), so "the same endpoint choice"
  reads as a choice of $x,z$; what is meant is $\tau=\theta$. Recomputed: all four inequalities and the constant
  $\max\{2M,4\Lambda R/\theta\}$ are correct (checks (b), (c)).
- **Fix** (each old string occurs once):
  - old: `with the inward model at $z-\tau r_z$ to obtain`
    new: `with the inward model at $z$, both evaluated at $z-\tau r_z$, to obtain`
  - old: `If $N<0$, reverse the endpoints and use the inward model at $x$:`
    new: `If $N<0$, reverse the endpoints and use the inward model at $x$. The reversed`
    `pair has radial numerator $(g-h)^Tr_x=T-N\ge|N|$, and` (two source lines)
  - old: `When $M=0$, the same endpoint choice gives an even stronger estimate.`
    new: `When $M=0$, the choice $\tau=\theta$ gives an even stronger estimate.`
- **Register items:** A/global/proof/001, A/global/disp/005, A/global/disp/006, A/global/disp/007.

### R-C-5 — The constant $\theta_\eta$ is not named in Theorem 5's proof (cosmetic; gap of exposition)

- **Where:** `sections/global.tex:160-161`.
- **Text:** "The upper bound in \eqref{art:inward-condition} follows with $M=L\max_{x\in K}\norm{r_x}^2$; its lower
  bound follows from convexity of $F$."
- **Explanation:** (15) asks for $M_\eta$ *and* $\theta_\eta\in(0,1/2]$; only $M$ is given. Any
  $\theta\in(0,1/2]$ works because the estimate holds for $0\le\tau\le1$ (the inward segment lies in $K\subset U$,
  line 47), e.g. $\theta=1/2$ for every band (as in the Lean `centered_inward_condition`). Same omission in
  `sections/local.tex:65-75` (proof of Theorem 7, "The inward condition holds on that sublevel", with
  $M=Lr^2$; item A/local/proof/002).
- **Fix** (old string occurs once):
  - old: `The upper bound in \eqref{art:inward-condition} follows with` + newline +
    `$M=L\max_{x\in K}\norm{r_x}^2$; its lower bound follows from convexity of $F$.`
  - new: `The upper bound in \eqref{art:inward-condition} follows with` + newline +
    `$M=L\max_{x\in K}\norm{r_x}^2$ and $\theta=1/2$ for every band; its lower bound follows from convexity of $F$.`
  - in local.tex (other reader's file), the analogous addition "with $M=Lr^2$ and $\theta=1/2$" after "The inward
    condition holds on that sublevel".
- **Register items:** A/global/proof/003 (and A/local/proof/002).

### R-C-6 — Garbled sentence in the uniform-Lipschitz step (cosmetic; language)

- **Where:** `sections/global.tex:146-149`.
- **Text:** "take a finite cover by neighborhoods carrying local constants and subdivide any segment in $K$ into
  pieces in that cover. Summing the local bounds gives the maximum of those constants along the segment."
- **Explanation:** the argument is right (a Lebesgue number $\delta$ of the finite cover of the compact convex $K$;
  pieces of length $<\delta$ lie in one neighborhood; summing $\norm{\nabla\psi(x_{j+1})-\nabla\psi(x_j)}\le
  L_{\max}\norm{x_{j+1}-x_j}$ gives the Lipschitz bound with $L=L_{\max}$), but "summing the local bounds gives the
  maximum of those constants" says something else than meant (the sum gives a bound *with* the largest constant),
  and the subdivision step needs the Lebesgue number, which is not named.
- **Fix** (old string occurs once):
  - old: `$K$ into pieces in that cover. Summing the local bounds gives the maximum` + newline +
    `of those constants along the segment.`
  - new: `$K$ into pieces shorter than a Lebesgue number of that cover. Summing the` + newline +
    `local bounds over the pieces gives the largest of those constants as a` + newline +
    `Lipschitz constant along the segment.`
- **Register items:** A/global/proof/003.

### R-C-7 — Notation: $T$ is the $t$ of Section 3, and "radial numerator" is never defined (cosmetic; notation)

- **Where:** `sections/global.tex:22-28`; other location `sections/local.tex:427-428`.
- **Text:** global.tex:25 "T=(h-g)^T(z-x),\qquad N=(h-g)^Tr_z."; local.tex:427-428 "Their radial numerator $y^Tz$
  tends to $u^2/2-v^2\ne0$ while $t\to0^+$. The quotient $(y^Tz)^2/t$ is unbounded."
- **Explanation:** Section 3 already names the same quantity $t=y^Ts$ for a differentiable pair
  (energy.tex:238-239, with $y=h-g$, $s=z-x$); Section 4 introduces a second letter $T$ for it, and the proof of
  Corollary 1 silently identifies (14) with (12) through $T=t$ and $N=y^Tr_z$. Conversely, the proof of Theorem 9
  writes $t$ and calls $y^Tz$ "radial numerator", a term defined nowhere in the article (only in Lean,
  `radialNumerator`), to show the failure of (14), which is stated with $T$ and $N$. Minor clashes as well: the
  scalar $T$ next to the transpose superscript $^T$ in the same formulas; $N$ is also the horizon in
  (7), Theorem 2 and the proof of Theorem 3; $R$ (radius bound, line 59) next to the correction $R_k$ of (6) that
  line 11 refers to; $L$ (Lipschitz constant of $\nabla\psi$, line 146) next to $L_\eta$ of Corollary 1's proof,
  which line 162 invokes. One sentence after the display removes the first two points; renaming is optional.
- **Fix** (old string occurs once):
  - old: `The radial secant condition is the following requirement on positive bands:`
  - new: `Here $T$ is the quantity $t$ of Section~\ref{art:energy}, and the radial` + newline +
    `numerator $N=y^Tr_z$, with $y=h-g$, gives $R_k=N^2/T$ in` + newline +
    `\eqref{art:energy-identity} when $(x,z)=(x_k,x_{k+1})$.` + newline +
    `The radial secant condition is the following requirement on positive bands:`
  - (the clause "gives $R_k=N^2/T$ …" is the definitional identity $R_k=(y_k^Tr_{k+1})^2/t_k$ of Lemma 2 and can
    be dropped if a shorter sentence is preferred; the other overloads: no change proposed.)
- **Register items:** A/global/disp/001, A/global/disp/002, A/global/proof/002; A/local/proof/008.

### R-C-8 — "This condition" / "The condition … where it fails" (cosmetic; language)

- **Where:** `sections/global.tex:111` and `115-117`.
- **Text:** "This condition controls only inward first-order modeling error." … "The condition is sufficient;
  Theorem~\ref{art:nonradial-example} will exhibit convergence where it fails on positive bands arbitrarily near
  the minimizer."
- **Explanation:** the paragraph directly follows Corollary 1 ("Under either condition"), so "This condition" can
  be read as (14) or (15); the content shows (15) is meant (the register reads it so, A/global/prose/016, 019).
  Theorem 9 states only the failure of (14) (local.tex:378-380); the failure of (15) there follows from Theorem 4
  by contraposition, which the sentence leaves to the reader.
- **Fix** (each old string occurs once):
  - old: `This condition controls only inward first-order modeling error.`
    new: `Condition~\eqref{art:inward-condition} controls only inward first-order modeling error.`
  - old: `Theorem~\ref{art:nonradial-example} will exhibit convergence where it fails` + newline +
    `on positive bands arbitrarily near the minimizer.`
    new: `Theorem~\ref{art:nonradial-example} will exhibit convergence where` + newline +
    `\eqref{art:radial-condition}, and hence by Theorem~\ref{art:radial-equivalence} also` + newline +
    `\eqref{art:inward-condition}, fails on positive bands arbitrarily near the minimizer.`
- **Register items:** A/global/prose/016, A/global/prose/019 (Lean `nonradial_example_condition_fails` already
  proves both failures).

### R-C-9 — "In particular" introduces an unrelated remark (cosmetic; language)

- **Where:** `sections/global.tex:125-128`.
- **Text:** "Centering is a geometric hypothesis on the objective, not knowledge required by the algorithm. In
  particular, the two summands need not separately be minimized at that center."
- **Explanation:** that neither summand need be minimized at $x_*$ does not follow from centering being an
  objective hypothesis rather than algorithmic knowledge; it is a separate remark (the theorem's last sentence).
- **Fix** (old string occurs once): old `algorithm. In particular, the two summands` → new
  `algorithm. Moreover, the two summands`.
- **Register items:** A/global/prose/023, A/global/prose/024.

### R-C-10 — "Equivalently" for an alternative argument; unstated $x_*$, $U$ (cosmetic; language)

- **Where:** `sections/global.tex:218-221`.
- **Text:** "Theorem~\ref{art:centered}, with $\psi=0$ and $\gamma=F$, gives convergence in value, … Equivalently,
  the inward remainder is identically zero, so the radial convergence corollary applies directly."
- **Explanation:** the last sentence gives a second route (inward condition with $M_\eta=0$, then Corollary 1), not
  an equivalent statement; "Alternatively" is meant. The application of Theorem 5 also needs $x_*=0$ (shown to be
  the minimizer two sentences earlier) and $U=\R^n$, which are not named.
- **Fix** (each old string occurs once):
  - old: `Theorem~\ref{art:centered}, with $\psi=0$ and` + newline + `$\gamma=F$,`
    new: `Theorem~\ref{art:centered}, with $x_*=0$, $U=\R^n$, $\psi=0$ and` + newline + `$\gamma=F$,`
  - old: `convergence of the iterates. Equivalently, the inward remainder`
    new: `convergence of the iterates. Alternatively, the inward remainder`
- **Register items:** A/global/proof/005.

### R-C-11 — No end-of-proof marks anywhere (cosmetic; typesetting)

- **Where:** all six proofs of `sections/global.tex` (ending at lines 91, 109, 163, 187, 222, 241); the same in
  every proof of the article: `sections/energy.tex` (5), `sections/local.tex` (8), `sections/failure.tex` (3),
  `appendices/lower_curvature.tex` (2), `appendices/matrix_algebra.tex` (1), `appendices/planar_geometry.tex` (1),
  `appendices/seed_certificate.tex` (2).
- **Explanation:** `master.tex:2` declares `\smartqed`, but no proof calls `\qed`, and svjour3's `proof`
  environment adds no mark itself (`\spnewtheorem*{proof}`, svjour3.cls:900); the PDF contains no QED square.
  On pp. 13-15 the proofs of Corollary 1, Theorem 5 and Corollary 3 run straight into the following remarks
  ("This condition controls…", "The compact initial sublevel…", "The norm cases include…"), separated only by a
  paragraph indent.
- **Fix:** old `\n\end{proof}` (6 occurrences in global.tex; replace all) → new `\qed\n\end{proof}` (with
  `\smartqed`, `\qed` removes the preceding space and sets the square flush right; after the closing
  `\end{equation}` of Theorem 4's proof it sets the square on its own line, or `\qquad\qed` can be put inside that
  display). Same replacement in the other files listed.
- **Register items:** A/global/proof/001-006 (no mathematical content).

## Coverage table

| Environment (global.tex lines) | Result |
|---|---|
| Setup and notation, display `disp/001` (19-27) | R-C-7 |
| Display (14) `art:radial-condition` (28-37) | read: no finding (R-C-7 for the notation) |
| Display (15) `art:inward-condition` and lines 46-52 | read: no finding |
| Theorem 4 `art:radial-equivalence` (54-57) | read: no finding |
| Proof of Theorem 4, displays `disp/004`-`disp/007` incl. (16) (58-91) | R-C-2, R-C-3, R-C-4, R-C-11 |
| Remark on the converse (93-96) | read: no finding (companion Theorem R:thm:equiv checked) |
| Corollary 1 `art:radial-convergence` (98-102) | read: no finding |
| Proof of Corollary 1 (103-109) | R-C-1, R-C-7, R-C-11 |
| Remarks on the inward condition (111-117) | R-C-8 |
| Section 4.2 introduction (121-128) | R-C-9 |
| Theorem 5 `art:centered` (130-142) | read: no finding |
| Proof of Theorem 5, display `disp/009` (143-163) | R-C-5, R-C-6, R-C-11 |
| Remarks after Theorem 5 (166-173) | read: no finding |
| Corollary 2 `art:mixed-benchmark` (175-181) | read: no finding |
| Proof of Corollary 2 (182-187) | read: no finding (R-C-11 only) |
| Literature remark (189-191) | read: no finding ([GL18] Cor. 4.4 and following discussion checked) |
| Section 4.3 introduction (195-198) | read: no finding |
| Theorem 6 `art:homogeneous` (200-209) | read: no finding |
| Proof of Theorem 6, display `disp/012` (210-222) | R-C-10, R-C-11 |
| Corollary 3 `art:homogeneous-examples` (224-233) | read: no finding |
| Proof of Corollary 3 (234-241) | read: no finding (R-C-11 only) |
| Remarks on norms, literature, companion (243-258) | read: no finding ([GL18] Cor. 4.2, [LO] §5.1, companion Ch. 7 checked) |

## Checks performed (no finding unless stated)

- **(14), (15):** quantifiers $\forall\eta\,\exists C_\eta\,\forall(x,z)$ and $\forall\eta\,\exists M_\eta,\theta_\eta
  \,\forall x\,\forall\tau$ as in the Lean `RadialSecantCondition`, `InwardModelCondition`. For an accepted pair
  $N^2/T=R_k$ (Lemma 2). The lower bound in (15) is automatic for convex $F$ (supporting inequality at $x$). The
  inward point $x-\tau r_x=(1-\tau)x+\tau x_*$ lies in the convex $K$ for $\tau\le1$.
- **Proof of Theorem 4:** $T=D_F(z,x)+D_F(x,z)$ and $T-N=(g-h)^Tr_x$ (exact check (b) on 2000 random rational
  pairs of the benchmark). Case $N\ge0$: supporting plane at $x$ and inward model at $z$ (needs $F(z)\ge F_*+\eta$,
  given) give $\tau N\le D_F(z,x)+M\tau^2/2$. Case $N<0$: supporting plane at $z$ and inward model at $x$ (needs
  $F(x)\ge F(z)\ge F_*+\eta$) give $\tau(T-N)\le D_F(x,z)+M\tau^2/2$, $T-N>|N|$ by $T>0$. $|N|,|T-N|\le2\Lambda R$
  by Cauchy-Schwarz. $\tau=A/M$ ($\le\theta$) gives $A^2\le2MD$; $\tau=\theta$ with $A>M\theta$ gives
  $D>A\theta/2$, $A^2\le2\Lambda R\,A\le(4\Lambda R/\theta)D$; $M=0$, $A=0$ trivial. Then $N^2\le A^2$, $D\le T$, so
  (16) with $C_\eta=\max\{2M_\eta,4\Lambda R/\theta_\eta\}\ge0$ (exact check (c): 20000 sampled $(A,D,M,\theta)$).
- **Proof of Corollary 1:** $W=r_xr_x^T$ is PSD; visibility $(g^Tr_x)^2\ge\eta^2$ from $g^Tr_x\ge F(x)-F_*\ge\eta$;
  secant control $y^TW(z)y=N^2\le C_\eta T$ on eligible pairs in $K_\eta$; transport with $L_\eta=0$ since
  $\Pi_ss=0$; any $\delta_\eta>0$. Theorem 3's hypotheses ($K=\{F\le b\}$ compact, $b>F_*=\min F$, $x_0\in K$)
  hold. Only gap: R-C-1.
- **Proof of Theorem 5:** $F(x_0)>F_*$ (else $x_0$ is a minimizer and $g_0=0$); $x_*\in K\subset U$; $K$ convex;
  Lebesgue-number argument gives a uniform $L$ (R-C-6); $|\psi(x-\tau r_x)-\psi(x)+\tau\nabla\psi(x)^Tr_x|=
  |\int_0^\tau(\nabla\psi(x)-\nabla\psi(x-sr_x))^Tr_x\,ds|\le\frac12L\tau^2\norm{r_x}^2$ for $\tau\in[0,1]$;
  $\gamma$ differentiable at $r_x$ with $\nabla\gamma(r_x)=\nabla F(x)-\nabla\psi(x)$ ($U$ open); Euler identity;
  $\gamma((1-\tau)r_x)=(1-\tau)\gamma(r_x)$ needs the representation at $x-\tau r_x\in K\subset U$; $M=L\max_K
  \norm{r_x}^2$; Corollary 1 with $b=F(x_0)$. Convexity of $\psi$ and of $U$ is not used by this proof (hypotheses
  stronger than needed; no action proposed). θ: R-C-5.
- **Corollary 2:** $\psi=u^2$ ($\nabla\psi$ 2-Lipschitz), $\gamma=|v|$ convex and positively homogeneous, sublevels
  $\{u^2+|v|\le b\}\subset[-\sqrt b,\sqrt b]\times[-b,b]$ closed and bounded, unique minimizer $(0,0)$; the inward
  remainder (1) $=\tau^2u^2$ for $v\ne0$ verified exactly (check (a), 2000 random rational points); the constant of
  Theorem 5's proof is $M=2\max\{b,b^2\}$ (check (d)). $H_0$, $c_1$, $c_2$ and $n=2$ are stated.
- **Theorem 6:** $F(0)=0$; $F\le0$ off zero contradicts coercivity along the ray; $\mu>0$ on the (nonempty, $n\ge1$)
  Euclidean sphere; $F\ge\mu\norm{x}$ by homogeneity; sublevels closed and bounded; unique minimizer $0$;
  $\norm{x_k}\le F(x_k)/\mu\to0$; second route with $M_\eta=0$, $\theta_\eta=1/2$, $b=F(x_0)>0$.
- **Corollary 3:** norms are convex, positively homogeneous, positive off zero, continuous; for the gauge and the
  linear maximum the ray $\{tx\}$ of a nonzero $x$ with $F(x)\le0$ lies in $\{F\le1\}$ resp. $\{F\le0\}$; maxima of
  linear forms are convex and positively homogeneous ($m\ge1$ implicit). Lean readings (Seminorm with
  definiteness; convex degree-one $F$ with bounded $\{F\le1\}$; `IsGreatest` of the $a_i^Tx$ with bounded
  $\{F\le0\}$) match the printed statement.
- **Remarks 243-258:** $\norm{\cdot}_1$ nondifferentiable exactly on coordinate hyperplanes, $\norm{\cdot}_\infty$
  exactly where two maximal magnitudes tie (or at 0); at $(t,t,0,\dots,0)$, $t>0$, the active forms $x_1,x_2$ have
  gradients $e_1\ne e_2$; $n\ge2$ is stated.
- **References in the PDF:** (2), (6), (14)-(16), Theorem 3, Theorem 4, Corollary 1, Theorem 5, Theorem 9 (= the
  nonradial example, p. 22), equation (1) (= `art:mixed-inward-remainder`), [1] = LO, [4] = BB, [5] = GL18 all
  resolve to the intended objects.
- **Statements vs Lean:** `radial_equivalence`, `radial_convergence`, `centered`, `mixed_benchmark`, `homogeneous`,
  `homogeneous_examples_{norm,gauge,maxLinear}` state exactly the printed theorems in the setting of lines 19-20; no
  difference a reader would notice.
- **Typesetting (pp. 11-16):** all text blocks end at $x\le410.9$ pt (right margin) and every page is filled to
  $y=641.6$-$642.4$ pt; `paper.log` has no overfull or underfull box for global.tex; displays (14)-(16), the
  theorem heads and the inline $\max_{x\in K}$ render cleanly. Only point: R-C-11.
- **Recorded issues not repeated:** M7 (abstract, "compact initial sublevels"): no other location in the article
  omits "contained in U" (introduction.tex:85-88, geometry.tex:69, local.tex:3, global.tex:138 all state it).
