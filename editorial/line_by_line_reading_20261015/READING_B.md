# Reader B: line-by-line reading of Section 3 and Appendix A

- **Files read (snapshot `$S/step2/snapshot/paper/`, identical to commit c8db802):**
  `sections/energy.tex` (all 319 lines) and `appendices/matrix_algebra.tex` (all 68
  lines), line by line. For definitions and for every later use of a Section 3
  result I also read `master.tex`, `sections/introduction.tex`, `geometry.tex`,
  `global.tex`, `local.tex`, `failure.tex`, `verification.tex`, `statements/*.tex`,
  `appendices/planar_geometry.tex`, `seed_certificate.tex`, `lower_curvature.tex`,
  `bibliography.tex`, `preprint_references.tex`; the registers `A_energy.json`,
  `A_matrix_algebra.json` (and the `A_global.json` and `C_02_M.json` items that
  touch my findings); the Lean statements in
  `bfgs_lean_article/BfgsArticle/Coverage/Article/MatrixAlgebra.lean`; and, to
  find recurrences, `companion/chapters/02_M.tex` lines 1-200.
- **PDF pages** (`$S/baseline/paper.pdf`): 6-11 (Section 3) and 34-36 (Appendix A),
  rendered at 110 dpi (`png/p06.png` ... `png/p36.png`), with 200-300 dpi crops of
  pages 7, 9, 11 and 35 (`png/*_top.png`, `png/p11_frac.png`). The LaTeX log has no
  overfull box in these pages. The white band under the text on every page is the
  bottom margin of `smallextended` on A4, not a gap: every page's text ends at
  y = 641.6 pt (measured with PyMuPDF).
- **Exact checks:** `check_algebra.py` (40 trials, $n\le5$) and
  `check_algebra_big.py` (120 trials, $n\le6$), Python `fractions`, standard
  library: on 119 random rational instances with $n=1,\dots,6$ (one trial skipped
  for $\beta=0$ or $g=0$; random SPD $H$, $g$, $y$
  with $\beta>0$, $\alpha>0$, $Z$ = the first $j$ columns of a rational orthogonal
  Cayley matrix, for every $1\le j\le n$) it confirms exactly: $y^Ts=\alpha\beta q$,
  $\kappa=-\beta q$, $H_+=PHP^T+\frac{\alpha}{\beta q}vv^T$; the Hessian form (5),
  $\widehat B_k\succeq0$, $\widehat B_ks_k=0$; the energy identity (6) for arbitrary
  $x_k,x_*$; $\det H_+=(\alpha/\beta)\det H$ and the hierarchy (8) for every $j$;
  the compression formula, (36), both Schur identities, the Gram combination and
  its bound, $Z^TH_+Z=Z^T\mathcal FZ+\rho aa^T$, the rank-one change
  $\rho\det A\,u$, $\det\operatorname{Gram}_H(g,Z)=(q-u)\det A$, $0\le u\le q$,
  the lemma's inequality, the full-size case ($u=q$, $w=\kappa$, $z=r$, (36) $=0$);
  and the three expressions of the eigenbasis sum in the proof of Theorem 1 (with
  a rational orthogonal eigenbasis). Every other step (Lemma 1, Lemma 2, the
  normalized hierarchy (10), the weighted potential, the product bound, the limits,
  the trace step and the normalization of Theorem 3) was recomputed by hand.
- **Time spent:** about 22 minutes (03:10-03:32).
- **Counts:** major 0, minor 6, cosmetic 5 (11 findings). No false statement and
  no gap in a proof was found: every inference of every proof in both files follows
  in a few lines, and every identity checks exactly. The findings are undefined
  notation, imprecise references, one further location of M10, and typesetting.

## Findings

### R-B-1. Gram determinants with $g$ are used without definition
- **Where:** `appendices/matrix_algebra.tex:43-46, 51-52, 60` (and line 8, via
  `sections/energy.tex:150`).
- **Text:** "$\det\operatorname{Gram}_H(g,y,Z) =\det A\bigl(\ldots\bigr)$",
  "the Schur complement of $A$ in $\operatorname{Gram}_H(g,Z)$".
- **Category / severity:** notation; minor.
- **Explanation:** the article defines only
  $\operatorname{Gram}_H(y,Z)=[y\ Z]^TH[y\ Z]$, and only inside the proof of
  Theorem `art:minor-hierarchy` (`energy.tex:150`). $\operatorname{Gram}_H(g,y,Z)$
  and $\operatorname{Gram}_H(g,Z)$ appear in Appendix A without definition. The
  evident reading, $[g\ y\ Z]^TH[g\ y\ Z]$ and $[g\ Z]^TH[g\ Z]$, is the one under
  which the identities hold (checked exactly; it is also the register's reading).
  The companion defines the notation at this point (`02_M.tex:85`: "If
  $\operatorname{Gram}_H$ denotes the Gram matrix in the $H$ inner product").
- **Fix** (`matrix_algebra.tex:41`, occurs once):
  ```
  Schur complements give, independently,
  ```
  →
  ```
  With $\operatorname{Gram}_H(g,Z)=[g\ Z]^TH[g\ Z]$ and
  $\operatorname{Gram}_H(g,y,Z)=[g\ y\ Z]^TH[g\ y\ Z]$, Schur complements give,
  independently,
  ```
- **Register items:** `A/matrix_algebra/disp/006`, `A/matrix_algebra/disp/007`,
  `A/matrix_algebra/proof/001` (its note records the point as a wording point).

### R-B-2. The rank-one step: the compression of $H_+$ is not named, and the Schur complement gives only $u\le q$
- **Where:** `appendices/matrix_algebra.tex:56-61`.
- **Text:** "Adding $\rho aa^T$ to the compression changes the coefficient
  $r/\kappa^2$ by $\rho$. [...] For $\rho=\alpha/(\beta q)$, the Schur complement of
  $A$ in $\operatorname{Gram}_H(g,Z)$ gives $0\le u\le q$, so the increase is at most
  $(\alpha/\beta)\det A$."
- **Category / severity:** gap (small) and language; minor.
- **Explanation:** (a) the paragraph never says why adding $\rho aa^T$ with
  $\rho=\alpha/(\beta q)$ produces $Z^TH_+Z$: this is
  $H_+=\mathcal F+\frac{\alpha}{\beta q}vv^T$ (line 17) together with $Z^Tv=Z^THg=a$.
  (b) The Schur complement of $A$ in $\operatorname{Gram}_H(g,Z)$ gives
  $\det\operatorname{Gram}_H(g,Z)=(q-u)\det A\ge0$, i.e. $u\le q$ only; $u\ge0$
  holds because $A^{-1}\succ0$. Only $u\le q$ is needed for the upper bound
  (the factor $\rho\det A$ is positive). Both points are one-line repairs.
- **Fix** (`matrix_algebra.tex:59-61`, occurs once):
  ```
  $Z^T\mathcal FZ$ is used. For $\rho=\alpha/(\beta q)$, the Schur
  complement of $A$ in $\operatorname{Gram}_H(g,Z)$ gives $0\le u\le q$,
  so the increase is at most $(\alpha/\beta)\det A$.
  ```
  →
  ```
  $Z^T\mathcal FZ$ is used. Since $Z^Tv=a$, the value $\rho=\alpha/(\beta q)$
  gives the compression $Z^TH_+Z$. The Schur complement of $A$ in
  $\operatorname{Gram}_H(g,Z)$ gives $u\le q$ (and $u\ge0$ since $A\succ0$),
  so the increase is at most $(\alpha/\beta)\det A$.
  ```
- **Register items:** `A/matrix_algebra/proof/001` (note: "wording points, not
  errors"; Lean `compression_update`, `u_bounds`).

### R-B-3. "$\det A(r-z)$" can be parsed as $\det(A(r-z))$
- **Where:** `appendices/matrix_algebra.tex:43, 45`; recurs in
  `companion/chapters/02_M.tex:87, 91`.
- **Text:** "$\det\operatorname{Gram}_H(y,Z)=\det A(r-z)$",
  "$\det\operatorname{Gram}_H(g,y,Z)=\det A\bigl((q-u)(r-z)-(\kappa-w)^2\bigr)$".
- **Category / severity:** notation; minor.
- **Explanation:** the intended product is $(\det A)(r-z)$ (Lean:
  `A.det * (r - z)`). Read as $\det\bigl(A(r-z)\bigr)=(r-z)^j\det A$, both identities
  are false for $j\ge2$. The same appendix writes $\rho\det A\,u$ with an explicit
  space (line 58) and $\frac{\det A}{\kappa^2}(\ldots)$ in (36); putting the scalar
  first removes the ambiguity.
- **Fix** (`matrix_algebra.tex`, each occurs once):
  ```
   \det\operatorname{Gram}_H(y,Z)&=\det A(r-z),\\
  ```
  →
  ```
   \det\operatorname{Gram}_H(y,Z)&=(r-z)\det A,\\
  ```
  and
  ```
   &=\det A\bigl((q-u)(r-z)-(\kappa-w)^2\bigr).
  ```
  →
  ```
   &=\bigl((q-u)(r-z)-(\kappa-w)^2\bigr)\det A.
  ```
  The companion lines are generated (`editorial/generate_companion.py`): the same
  two replacements as a logged transformation for `02_M.tex:87` and `:91`.
- **Register items:** `A/matrix_algebra/disp/006`; companion `C/02_M/disp/011`,
  `C/02_M/disp/012`.

### R-B-4. "orthogonal basis", "Equation (36) then vanishes"
- **Where:** `appendices/matrix_algebra.tex:64-65`.
- **Text:** "When $j=n$, $Z$ is an orthogonal basis and $u=q$, $w=\kappa$, $z=r$.
  Equation~\eqref{art:compression-determinant} then vanishes".
- **Category / severity:** language; cosmetic.
- **Explanation:** $Z$ is an orthogonal matrix (its columns are an orthonormal
  basis); an equation does not vanish, its right side does. The step to $u=q$,
  $w=\kappa$, $z=r$ is $A^{-1}=Z^TH^{-1}Z$ (since $ZZ^T=I$), worth three words.
- **Fix** (`matrix_algebra.tex:64-65`, occurs once):
  ```
  When $j=n$, $Z$ is an orthogonal basis and $u=q$, $w=\kappa$, $z=r$.
  Equation~\eqref{art:compression-determinant} then vanishes, while the
  ```
  →
  ```
  When $j=n$, $Z$ is an orthogonal matrix, $A^{-1}=Z^TH^{-1}Z$, and $u=q$,
  $w=\kappa$, $z=r$. The right side of \eqref{art:compression-determinant}
  then vanishes, while the
  ```
- **Register items:** `A/matrix_algebra/proof/001`.

### R-B-5. Proof of Theorem `art:reciprocal-growth`: $\beta_k$ is not defined, and the contraction holds only for $k\ge J$
- **Where:** `sections/energy.tex:179` and `:194-198`; the undefined $\beta_k$ recurs
  in `companion/chapters/02_M.tex:129` ("Since $\beta_k\ge c$").
- **Text:** "$\beta_k=\frac{t_k}{d_k}\ge \omega$"; "Multiply
  \eqref{art:normalized-hierarchy} by these weights and sum. [...] Consequently
  $V_\eta(H_{k+1})\le\frac{2\eta}{q_k}V_\eta(H_k)$".
- **Category / severity:** notation; minor.
- **Explanation:** $\beta_k$ appears for the first time in this display. Read as a
  definition ($\beta_k:=t_k/d_k$), the next sentence ("Theorem 1 therefore
  yields") needs the identification with the $\beta$ of Theorem
  `art:minor-hierarchy` for the $k$-th update, $-y_k^TH_kg_k/q_k$; this holds
  because $t_k=y_k^Ts_k=-\alpha_ky_k^TH_kg_k$ and $d_k=\alpha_kq_k$. Writing both
  expressions removes the doubt (the register reads $\beta_k$ as the theorem's
  $\beta$). Second, the bound "as do the remaining terms" uses $d_k/\omega\le\eta$,
  so the displayed contraction holds for $k\ge J$ only; the display does not say so.
  The mathematics is correct (recomputed: the $e_{j+1}$ terms give
  $\eta\sum_{i=2}^{n}(K_0/\eta)^{i-1}e_i\le\eta V_\eta$ because $e_{n+1}=0$).
- **Fix** (`energy.tex`, each occurs once):
  ```
   \beta_k=\frac{t_k}{d_k}\ge \omega,\qquad
  ```
  →
  ```
   \beta_k=-\frac{y_k^TH_kg_k}{q_k}=\frac{t_k}{d_k}\ge \omega,\qquad
  ```
  and
  ```
  Multiply \eqref{art:normalized-hierarchy} by these weights and sum. The
  ```
  →
  ```
  For $k\ge J$, multiply \eqref{art:normalized-hierarchy} by these weights and sum. The
  ```
  (companion: the same identification at `02_M.tex:129`, through the generator).
- **Register items:** `A/energy/proof/004`, `A/energy/disp/017` (note on $\beta_k$),
  `A/energy/disp/020`; companion `C/02_M/proof/004`.

### R-B-6. Further location of M10: the section's opening sentence omits bounded gradients
- **Where:** `sections/energy.tex:8-9`.
- **Text:** "The matrix hierarchy then shows that persistent missed progress cannot
  be paid for by a bounded secant cost per iteration."
- **Category / severity:** hypothesis; minor (an informal roadmap sentence).
- **Explanation:** this sentence announces the contradiction of lines 101-111,
  which rests on Theorem `art:reciprocal-growth`; that theorem needs bounded
  gradients (and $d_k\to0$, automatic here because a minimizer bounds the values
  below). It is the hypothesis whose omission M10 records for lines 108-109; the
  register maps this sentence to the same claim (`A/energy/prose/005` SAME_AS
  `A/energy/prose/010`, whose Lean statement includes bounded gradients).
- **Fix** (`energy.tex:8-9`, occurs once):
  ```
  measuring missed progress. The matrix hierarchy then shows that persistent
  missed progress cannot be paid for by a bounded secant cost per iteration.
  ```
  →
  ```
  measuring missed progress. The matrix hierarchy then shows that, when the
  gradients are bounded, persistent missed progress cannot be paid for by a
  bounded secant cost per iteration.
  ```
- **Register items:** `A/energy/prose/005` (with M10: `A/energy/prose/012`).

### R-B-7. Later use: the subgradient bound is in the proof of Theorem `art:certificate`, not in the theorem
- **Where:** `sections/global.tex:60` (proof of Theorem `art:radial-equivalence`).
- **Text:** "The subgradient bound was proved in Theorem~\ref{art:certificate};"
- **Category / severity:** reference; minor.
- **Explanation:** Theorem `art:certificate` (`energy.tex:270-278`) states no
  gradient bound; the bound is the second step of its proof (`energy.tex:282-285`),
  where it is proved for every compact $K$. The hypothesis is met in `global.tex`
  ($K=\{F\le b\}$ compact), so only the pointer is imprecise. All other later uses
  of Section 3 results satisfy their hypotheses (table below).
- **Fix** (`global.tex:60`, occurs once):
  ```
  The subgradient bound was proved in Theorem~\ref{art:certificate}; supporting
  ```
  →
  ```
  The subgradient bound was shown in the proof of Theorem~\ref{art:certificate}; supporting
  ```
- **Register items:** `A/global/proof/001` (its note records this as a wording point).

### R-B-8. Lemma `art:gram-compression` is cited from Section 3 without saying it is in Appendix A
- **Where:** `sections/energy.tex:143-144` (and `:165`).
- **Text:** "The complete compression calculation in Lemma~\ref{art:gram-compression} gives"
- **Category / severity:** reference; cosmetic.
- **Explanation:** the PDF reads "Lemma 6"; Lemmas 3-5 are in Sections 5-6 and
  Lemma 6 is in Appendix A, which no sentence of the article names (the label
  `art:matrix-algebra` is never referenced).
- **Fix** (`energy.tex:144`, occurs once):
  ```
  Lemma~\ref{art:gram-compression} gives
  ```
  →
  ```
  Lemma~\ref{art:gram-compression} of Appendix~\ref{art:matrix-algebra} gives
  ```
- **Register items:** `A/energy/proof/003`.

### R-B-9. The trace chain in the proof of Theorem `art:certificate` also uses visibility
- **Where:** `sections/energy.tex:290-298`.
- **Text:** "trace monotonicity and \eqref{art:secant-control}--\eqref{art:transport} give"
- **Category / severity:** reference; cosmetic.
- **Explanation:** the last inequality of the chain,
  $\tr(\widehat B_kW(x_k))=E_k-g_k^TW(x_k)g_k/q_k\le E_k-m/q_k$, is visibility
  (11), which the sentence does not cite.
- **Fix** (`energy.tex:291`, occurs once):
  ```
  \eqref{art:secant-control}--\eqref{art:transport} give
  ```
  →
  ```
  \eqref{art:visibility}--\eqref{art:transport} give
  ```
- **Register items:** `A/energy/disp/024`, `A/energy/proof/005`.

### R-B-10. Two citations run together
- **Where:** `sections/energy.tex:210` (PDF page 9).
- **Text:** `\cite[Theorem~3.7]{S16}\cite[Appendices C--D]{FND_JJM24AW}`, rendered
  "[6, Theorem 3.7][10, Appendices C–D]".
- **Category / severity:** typesetting; cosmetic. The only such pair in the article.
- **Fix** (`energy.tex:210`, occurs once):
  ```
  \cite[Theorem~3.7]{S16}\cite[Appendices C--D]{FND_JJM24AW} to the
  ```
  →
  ```
  \cite[Theorem~3.7]{S16}, \cite[Appendices C--D]{FND_JJM24AW} to the
  ```
- **Register items:** `A/energy/prose/020`.

### R-B-11. $\frac{m}{\overline P}$ prints as a double fraction bar
- **Where:** `sections/energy.tex:305` (PDF page 11, display before "contradicting (9)").
- **Text:** `\frac{m}{\overline P}\sum_{k=J}^{N-1}q_k^{-1}`.
- **Category / severity:** typesetting; cosmetic.
- **Explanation:** the overline of $\overline P$ sits directly under the fraction
  bar, so the coefficient looks like $m$ over a doubled bar (`png/p11_frac.png`).
- **Fix** (`energy.tex:305`, occurs once):
  ```
   \frac{m}{\overline P}\sum_{k=J}^{N-1}q_k^{-1}
  ```
  →
  ```
   m\overline P^{-1}\sum_{k=J}^{N-1}q_k^{-1}
  ```
- **Register items:** `A/energy/disp/025`.

## Later uses of Section 3 results (hypotheses checked)

| Location | Result used | Check |
|---|---|---|
| `introduction.tex:58` | Definition `art:admissible` | description matches |
| `introduction.tex:107-116` | Theorems `art:minor-hierarchy`-`art:certificate` | states bounded gradients and $d_k\to0$, as Theorem `art:reciprocal-growth` needs |
| `global.tex:11-12, 17` | (6), (2) | correct objects |
| `global.tex:59-61` | gradient bound on compact $K$ | hypothesis met; pointer imprecise (R-B-7) |
| `global.tex:104-108` (Cor. `art:radial-convergence`) | Def. `art:band-certificate`, Thm `art:certificate` | $K=\{F\le b\}$ compact, $b>F_*=F(x_*)=\min F$ (`global.tex:19-20`); $W=r_xr_x^T$ PSD; visibility $m_\eta=\eta^2$; eligible pairs in $K_\eta$ have $F_*+\eta\le F(z)\le F(x)$ (as $\Delta\ge c_1d>0$) and $T=t\ge\omega d>0$, so (17) gives (12) with $C_\eta\ge0$; $\Pi_sr_z=\Pi_sr_x$ gives (13) with $L_\eta=0$; $\delta_\eta$ is not named but any value works. OK |
| `global.tex:144-162` (Thm `art:centered`) | via the corollary | $b=F(x_0)>F(x_*)$ is proved at lines 144-145. OK |
| `local.tex:72-75` (Thm `art:polyhedral`) | via the corollary | compact sublevel $\{F\le F(x_*)+\varepsilon\}$, $\varepsilon>0$. OK |
| `local.tex:229` | Lemma `art:run-invariants`, gradient bound | $\sum d_k<\infty$ and bounded gradients on compact $K$. OK |
| `local.tex:261-266` | (5), $\widehat B_ks_k=0$ | $E_{k+1}=\lambda_k^2(E_k-(g_k^Tw)^2/q_k)+(y_k^Tw(x_{k+1}))^2/t_k$ recomputed; the bracket is $\ge0$, so $\lambda_k^2\le1+Ld_k$ applies. OK |
| `local.tex:269-271` | normalization of Thm `art:certificate`, Thm `art:reciprocal-growth` | dividing by $\prod_{j=J}^k(1+Ld_j)=P_{k+1}$ gives $\le\overline P m^{-1}(E_J+C(N-J))$; bounded gradients and $d_k\to0$ hold. OK |
| `local.tex:284` | last paragraph of the proof of Thm `art:certificate` | OK |
| `seed_certificate.tex:136-138`, `lower_curvature.tex:168-169` | positive definiteness, by the argument of Lemma `art:run-invariants` (no citation) | $y^Ts>0$ verified there. OK |

## Coverage table

| Environment (snapshot lines) | Result |
|---|---|
| `energy.tex` 3-10, opening paragraph | R-B-6 |
| Definition `art:admissible` (12-28) | read: no finding |
| Notation display (35-42) | read: no finding |
| Lemma `art:run-invariants` (43-55) | read: no finding |
| proof (56-72) | read: no finding (Hessian form verified by multiplying out, and exactly) |
| Lemma `art:reference-energy` (74-89) | read: no finding |
| proof (90-99) | read: no finding |
| paragraph 101-111 | M10 only (already recorded) |
| definition of $e_j$ and paragraph 113-128 | read: no finding |
| Theorem `art:minor-hierarchy` (130-141) | read: no finding |
| proof (142-166) | R-B-8 |
| Theorem `art:reciprocal-growth` (168-174) | read: no finding |
| proof (175-207) | R-B-5 |
| paragraph 209-217 | R-B-10 (companion Chapter 2 = `02_M`, correct) |
| Section 3.2 prose, eligibility (219-247) | read: no finding |
| Definition `art:band-certificate` (249-263) | read: no finding |
| remarks 264-268 | read: no finding |
| Theorem `art:certificate` (270-278) | read: no finding |
| proof (279-314) | R-B-9, R-B-11 (later use: R-B-7) |
| closing paragraph 316-319 | read: no finding |
| `matrix_algebra.tex` Lemma `art:gram-compression` (3-12) | read: no finding (uses $\operatorname{Gram}_H(y,Z)$ from `energy.tex:150`; see R-B-1) |
| proof (13-68) | R-B-1, R-B-2, R-B-3, R-B-4 |

## Remarks without a proposed change

- Letters with two meanings near each other, none of which misleads in context:
  $I$ is the index set in the definition of $e_j$ (`energy.tex:117`) and the
  identity in $\det(I+zH)$ three lines later; $J$ is a $(j+1)$-subset in the proof
  of Theorem `art:minor-hierarchy` and a tail index in the next two proofs; $\eta$
  is a gap (line 102), the weight parameter of $V_\eta$ (line 189) and the band
  level (line 251); in Appendix A the scalar $z=b^TA^{-1}b$ stands next to the
  matrix $Z$. $E_k$ is redefined in the proof of Theorem `art:certificate`
  (consistently: $W=r_xr_x^T$ gives back Lemma `art:reference-energy`'s $E_k$).
  The limiting gap is $\ell$ in Theorem `art:certificate`, while $\ell$ is the
  limiting value in `local.tex:229`, whose proof refers to "exactly as in the proof
  of Theorem `art:certificate`".
- Literature locators were not checked against the cited works; the companion's
  more precise locator for Nocedal (`02_M.tex:282`: Section 5, equations (5.7),
  (5.15), (5.21)) agrees with `energy.tex:67`.
