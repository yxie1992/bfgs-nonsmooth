# Reader E: line-by-line reading of Section 6 (failure) and Appendix C (seed certificate)

- **Files read (snapshot `$S/step2/snapshot/paper/`, = commit c8db802):** `sections/failure.tex` (514 lines) and `appendices/seed_certificate.tex` (200 lines), in full. Also read for definitions and cross-checks: `master.tex`, `statements/negative_upper.tex`, `statements/negative_lower.tex`, `statements/positive_partition.tex`, `sections/introduction.tex`, `sections/geometry.tex`, `sections/energy.tex`, `sections/global.tex`, `sections/local.tex`, `sections/verification.tex`, `appendices/matrix_algebra.tex`, `appendices/lower_curvature.tex`, `figures/cycle_trials.tex`, `figures/generate_figures.py`, `figures/seed_data.json`, `bibliography.tex`; registers `A_failure.json`, `A_seed_certificate.json` (and the relevant items of `A_master.json`, `A_lower_curvature.json`, `A_negative_lower.json`).
- **PDF pages (`$S/baseline/paper.pdf`):** 23–33 (Section 6) and 39–43 (Appendix C, start of D), rendered at 110 dpi; Figures 2 and 3, Table 2, Table 3/Theorem 11 and displays (44)–(47) also at 200–400 dpi. LaTeX log checked for the two files.
- **External references checked:** Lewis–Overton, Math. Program. 141 (2013): Algorithm 4.6 is the unit-first bisection/doubling search (Section 4.1; strict tests A(t), W(t), W includes differentiability), as cited at `failure.tex:33`. Rump, Acta Numerica 2010, Theorem 13.3 is the Krawczyk–Rump existence/uniqueness theorem, a fair "compare" for `seed_certificate.tex:80-81`.
- **Time spent:** about 30 minutes (03:10–03:40).
- **Scratch:** `$S/read_E/` (`check_root.py`, `check_cycle.py`, `check_intervals.py`, `check_shape.py`, `count_olds.py`, `img/`).
- **Summary:** 0 major, 6 minor (R-E-1 … R-E-6), 5 cosmetic (R-E-7 … R-E-11). No false mathematical statement found beyond the known M11; every number, decimal, table entry and certificate bound in the two files was recomputed and holds (verification log at the end).

## Findings

### R-E-1 — further locations of the M11 slip (parameter range omitted; "admissible pair" undefined)
- **Where:** `sections/failure.tex:184-190` (the induction (26)), `:202-209` (Corollary 8), `:493-495`. Other files: `appendices/lower_curvature.tex:88`, `:104`, `:182`, `:295`; informal summaries `failure.tex:15-16`, `seed_certificate.tex:6-7`, `:142`.
- **Quoted text:** (a) `failure.tex:187`: "The two cycle closures therefore give the exact induction" [(26)]; (b) `failure.tex:203`: "The same deterministic run, with $H_0=I$, fails for"; (c) `failure.tex:494-495`: "the same accepted and rejected trial lists persist along that orbit, for every admissible pair $(c_1,c_2)$."
- **Category:** hypothesis (parameter range). **Severity:** minor.
- **Explanation:** (26) and Corollary 8 hold only for the range named at `failure.tex:159-161`, 0<c₁≤1/3 (with any c₂>0, in particular c₁<c₂<1). Exact Armijo ratios at the three acceptances are r₀=0.766578, r₁=0.393191, r₂=0.375206 (recomputed). For c₁ ∈ (r₂,1) the phase-2 trial 1/16 fails Armijo, so x₃ ≠ ρz₀ and (26) is false. The same applies to "the same deterministic run" of Corollary 8. Neither (26) nor the corollary states a range. A reader of the corollary alone would read it for all 0<c₁<c₂<1. The registers read the range in (A/failure/disp/010, corollary note), but the text does not. In (c), "admissible pair" is defined nowhere in the article. The only "admissible" notion so far is Definition 1, admissible runs with 0<c₁<c₂<1. Read that way, (c) is false for c₁>r₂, because the seed margins themselves fail there and so do not persist. Appendix D fixes the range at `lower_curvature.tex:13-15` but never calls it "admissible", and then uses "admissible pair" four times.
- **Proposed fix:**
  - `failure.tex` (1 occurrence): `The two cycle closures therefore give the exact induction` → `For every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$, the two cycle closures therefore give the exact induction`
  - `failure.tex` (1 occurrence): `The same deterministic run, with $H_0=I$, fails for` → `For every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$, the same deterministic run, with $H_0=I$, fails for`
  - `failure.tex` (1 occurrence): `for every admissible pair $(c_1,c_2)$` → `for every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$`
  - Other file, `lower_curvature.tex` (1 occurrence): `fixed pair $0<c_1\le1/3$, $c_1<c_2<1$, as in Theorem~\ref{art:local-failure};` → `fixed pair $0<c_1\le1/3$, $c_1<c_2<1$ (an \emph{admissible pair}), as in Theorem~\ref{art:local-failure};`. This defines the term used at lines 88, 104, 182, 295.
  - The informal summaries (`failure.tex:15-16`, `seed_certificate.tex:6-7`, `:142`) can stay once Lemma 4 states the range (the M11 fix).
- **Register items:** A/failure/disp/010, A/failure/prose/026, A/failure/corollary/art:failure_polyhedral, A/failure/prose/063; other: A/lower_curvature/lemma/art:lower_hyperbolic, A/lower_curvature/proof/001, A/lower_curvature/proof/002, A/lower_curvature/prose/011, A/lower_curvature/prose/027, A/seed_certificate/prose/007, A/seed_certificate/prose/013, A/failure/prose/002.

### R-E-2 — "the accumulation point" is undefined and used for two different points
- **Where:** `failure.tex:465` (Table 3 header), `:505-506`, `:512-513`. Other files: `master.tex:53-54` (abstract), `lower_curvature.tex:11-13`.
- **Quoted text:** "At the accumulation point" (Table 3 column head); "retains global $C^{1,1}$ regularity but prevents second differentiability at the accumulation point."; "the different scalar scales determine which regularity survives at the accumulation point."
- **Category:** language. **Severity:** minor.
- **Explanation:** The intended point is the minimizer 0, where the centers x̄_ℓ and the starts accumulate. The registers also read it this way ("at zero, where the bad starts accumulate"). But Section 6 also says that the iterates of each run accumulate at x̄_ℓ: Figure 3's inset annotation reads "Their contraction copies accumulate at x̄_ℓ, not at x_*", and Theorem 10/11 have x_k^{(ℓ)} → x̄_ℓ. The natural meaning of "the accumulation point" in a convergence paper is the limit of a run. With that reading, Table 3, row 2 ("The first three branches are not twice differentiable") and `:506` are false. At x̄_ℓ every branch is twice differentiable: q_iᵀx̄_ℓ = b_i a_ℓ is a node, ψ_b is affine there, so f_i = μ‖x‖²/2 + affine near x̄_ℓ. The same holds in the C^{2,1} construction (plateaus). The introduction (`introduction.tex:78-79`) and both theorem statements say "at zero" / "at the minimizer".
- **Proposed fix:**
  - `failure.tex` (1 occurrence): `At the accumulation point` → `At the minimizer`
  - `failure.tex` (1): `regularity but prevents second differentiability at the accumulation point.` → `regularity but prevents second differentiability at the minimizer, where the copies accumulate.`
  - `failure.tex` (1): `tree; the different scalar scales determine which regularity survives at\nthe accumulation point.` → `tree; the different scalar scales determine which regularity survives at\nthe minimizer.`
  - Other files, to be merged with the M8 fix: `master.tex` (1): `differentiability at the accumulation point.` → `differentiability at the minimizer.`; `lower_curvature.tex` (1): `of the branches at the accumulation point.` → `of three branches at the minimizer.`
- **Register items:** A/failure/table/art:regularity-map, A/failure/prose/068, A/failure/prose/070; other: A/master/prose/009, A/lower_curvature/prose/010 (both already DISCREPANCY for M8).

### R-E-3 — closure-identity check: "Their sum" is not what is summed; C and E undefined
- **Where:** `seed_certificate.tex:112-123`.
- **Quoted text:** "The middle update is $C+\beta E$, because its two projection factors are independent of the step length …" and "Its projection factors are the orthogonal projector onto $(g_0-g_2)^\perp$, and its rank-one term is $\widetilde\rho$ times the complementary projector. Their sum is $\widetilde\rho I$".
- **Category:** gap / language (and notation: C, E never defined). **Severity:** minor.
- **Explanation:** Taken literally, the sentence adds the projector Π onto (g₀−g₂)^⊥ and ρ̃(I−Π), which is not ρ̃I. The update is Π(C+βE)Π + ss^T/(y^Ts), with s = ρ̃(g₀−g₂) ∥ y = g₀−g₂. The missing step uses the previous sentence: Π = ww^T for the unit w ⊥ g₀−g₂, so Π(C+βE)Π = (w^T(C+βE)w)Π = ρ̃Π. The rank-one term is ρ̃(I−Π). The register calls this a "wording point". C and βE are meant as the projected term and the rank-one term of the middle update B(M₁,g₁,g₂,β) (y^Ts = β(U+129)/256 > 0, recomputed). All identities of the passage were verified exactly at 30 random rational (c,d): (45), w^T(C+βE)w|w|^{-2} = ρ̃, ρ̃−ρ = 2064R(γ−1/16)/(V(U+129)).
- **Proposed fix:**
  - `seed_certificate.tex` (1 occurrence): `The middle update is $C+\beta E$, because its two projection factors` → `The middle update is $C+\beta E$, with projected term $C$ and rank-one term $\beta E$, because its two projection factors`
  - `seed_certificate.tex` (1 occurrence): `projector onto $(g_0-g_2)^\perp$, and its rank-one term is\n$\widetilde\rho$ times the complementary projector. Their sum is` → `projector $\Pi=ww^T$ onto $(g_0-g_2)^\perp$, so its projected term is $\Pi(C+\beta E)\Pi=\widetilde\rho\,\Pi$, and its rank-one term is\n$\widetilde\rho(I-\Pi)$. Their sum is`
- **Register items:** A/seed_certificate/proof/002, A/seed_certificate/disp/010.

### R-E-4 — Lemma 5: convexity attributed to the sign of φ_b′
- **Where:** `failure.tex:335-337`.
- **Quoted text:** "The derivative is negative on the negative half-line and positive on the positive half-line; the outer formulas diverge to infinity. This proves convexity, coercivity and the minimum assertions."
- **Category:** language (insufficient justification). **Severity:** minor.
- **Explanation:** The sign pattern of φ_b′ gives monotonicity on each half-line, the unique zero and coercivity, but not convexity. Convexity needs φ_b″ ≥ 0 on every piece, together with the C² matching just proved: P_b′ ≥ 0 gives φ_b″ = a_ℓ(1+θ)P_b′(ξ)/b ≥ 0 on positive intervals; −6x ≥ 0 on [−1,0]; 6 for x<−1; 0 for x≥b. All facts are in the proof, but the sentence cites the wrong one. This is also the lower bound of (30), which the proof never states.
- **Proposed fix:** `failure.tex` (1 occurrence): `positive half-line; the outer formulas diverge to infinity. This proves\nconvexity, coercivity and the minimum assertions.` → `positive half-line; the outer formulas diverge to infinity. Since also\n$\varphi_b''\ge0$ on every piece ($P_b'\ge0$ on positive intervals; $6$, $-6x$ and $0$ outside), this proves\nconvexity, coercivity and the minimum assertions.`
- **Register items:** A/failure/proof/002, A/failure/lemma/art:upper_scalar_lemma.

### R-E-5 — Section 6.6 reuses a_ℓ, x̄_ℓ with new values and an undefined C_*
- **Where:** `failure.tex:498-502`.
- **Quoted text:** "For the local embedding the scalar node values are now $a_\ell^2$ and the node slopes $a_\ell$. The resulting model is $F(\bar x_\ell+a_\ell z)=a_\ell^2(C_*+Q_\mu(z))$".
- **Category:** notation. **Severity:** minor.
- **Explanation:** In Section 6, a_ℓ = θ^ℓ = 16^{−ℓ} and x̄_ℓ = a_ℓ(2,−32)^T (lines 271, 373). This paragraph silently uses Appendix D's a_ℓ = 128^{−ℓ} (`lower_curvature.tex:207`), its x̄_ℓ = a_ℓc_*, and C_* = 1+μ‖c_*‖²/2, which is defined only at `lower_curvature.tex:282`. A reader of Section 6 meets an undefined C_* and a_ℓ with a changed meaning.
- **Proposed fix:** `failure.tex` (1 occurrence): `For the local embedding the scalar node values are now $a_\ell^2$ and the\nnode slopes $a_\ell$.` → `For the local embedding of Appendix~\ref{art:lower_curvature}, with its own $a_\ell=128^{-\ell}$, centers $\bar x_\ell=a_\ell(2,-32)^T$ and constant $C_*=1+\mu\|(2,-32)\|^2/2$, the scalar node values are now $a_\ell^2$ and the\nnode slopes $a_\ell$.`
- **Register items:** A/failure/prose/065, A/failure/prose/066.

### R-E-6 — Figure 2: panel scales "as indicated" are indicated for panel (a) only
- **Where:** `failure.tex:176` (caption). Drawing: `figures/cycle_trials.tex:10`, `:26`, `:52`.
- **Quoted text:** "The panels use different horizontal and vertical scales, as indicated."
- **Category:** typesetting (figure/caption accuracy). **Severity:** minor.
- **Explanation:** Panel (a) says "Vertical scale enlarged by 22/4.6", which is correct (x = 4.6 cm, y = 22 cm). Panel (b) uses x = 4.2 cm and y = 2.5 cm, so the vertical axis is compressed by 2.5/4.2. Panel (c) uses x = 21 cm and y = 23 cm. Neither is indicated. In (b) the phase-2 ray is drawn at about 42° although its slope 0.98749/0.65643 corresponds to 56°. The plotted coordinates themselves match the recomputed z_j and queries.
- **Proposed fix:** `failure.tex` (1 occurrence): `The panels use different horizontal and vertical scales, as indicated.` → `The panels use different horizontal and vertical scales; the vertical-to-horizontal ratios are $22/4.6$, $2.5/4.2$ and $23/21$ in (a), (b) and (c).`
- **Register items:** A/failure/figure/art:cycle-figure (NON_CLAIM; the caption sentence is not itemized).

### R-E-7 — "classical Hessian" is a term used nowhere else
- **Where:** `failure.tex:484-486`.
- **Quoted text:** "Here a classical Hessian is the derivative of the gradient map, with that map defined in a neighborhood of the point."
- **Category:** language. **Severity:** cosmetic.
- **Explanation:** The convention is meant for "∇²F(x) … at every twice-differentiable point" (Theorem 11) and for "Hessians exist" / "not twice differentiable" (Table 3). Neither uses the words "classical Hessian", and "Here" has no clear antecedent in print: the paragraph follows Table 3 and Theorem 11 on the next page.
- **Proposed fix:** `failure.tex` (1 occurrence): `Here a classical Hessian is the derivative of the gradient map, with that` → `In Theorem~\ref{art:local-failure-lower} and Table~\ref{art:regularity-map}, a Hessian is the classical one: the derivative of the gradient map, with that`
- **Register items:** A/failure/prose/059.

### R-E-8 — typesetting of pages 31, 32, 40, 42 and Figure 3
- **Where:** `failure.tex:455-457`, `:463`, `:433-446` (Figure 3); `seed_certificate.tex:47-51`, `:164-168`.
- **Category:** typesetting. **Severity:** cosmetic.
- **Explanation:**
  - (a) Theorem 11 sits in a `minipage`, which sets \parindent to 0. Its second paragraph ("The objective can be a maximum of four …", p. 32) therefore starts flush left with no space.
  - (b) Table 3: justified narrow p-columns give an underfull hbox (log: "Four uni-formly strongly", badness 2189).
  - (c) The unbreakable minipage leaves an underfull vbox on p. 31 (badness 4193), visible as a stretched gap before §6.6.
  - (d) The equation numbers (44) (p. 40) and (46) (p. 42) fall on a line of their own. (45) (p. 41) is squeezed: "ρ̃(g₀−g₂)" without binary spacing.
  - (e) Figure 3 inset: the labels x̄_ℓ and x₀^{(ℓ)} cross the dotted O(a_ℓ²) box, and "O(a_ℓ²)" touches the outer frame.
- **Proposed fix:**
  - (a) `failure.tex` (1 occurrence): `\noindent\begin{minipage}{\textwidth}` → `\noindent\begin{minipage}{\textwidth}\setlength{\parindent}{15pt}` (svjour3's value).
  - (b) `failure.tex` (1): `\begin{tabular}{p{.29\textwidth}p{.27\textwidth}p{.32\textwidth}}` → `\begin{tabular}{>{\raggedright\arraybackslash}p{.29\textwidth}>{\raggedright\arraybackslash}p{.27\textwidth}>{\raggedright\arraybackslash}p{.32\textwidth}}` (array is loaded).
  - (d) Set (44) and (46) as two-line `gathered` displays.
  - (e) Move the labels in `generate_figures.py` (lines 142-145).
- **Register items:** A/negative_lower/theorem/art:local-failure-lower (layout only), A/failure/table/art:regularity-map, A/failure/figure/art:shrinking-scales, A/seed_certificate/disp/004, A/seed_certificate/disp/010, A/seed_certificate/disp/013.

### R-E-9 — small notation inconsistencies
- **Where:** `seed_certificate.tex:194`; `failure.tex:114` vs `seed_certificate.tex:192` and `failure.tex:421`; `seed_certificate.tex:97`, `:99`; `failure.tex:275` vs `:359`; `failure.tex:89-97`.
- **Category:** notation. **Severity:** cosmetic.
- **Explanation:**
  - (a) Lemma 4 introduces [z]₂ for the second coordinate, precisely to avoid a clash with the point z₂. Appendix C then writes "2−q₂".
  - (b) Lemma 4 says "the three starting points", while Appendix C and the proof of Theorem 10 say "base points". "Starting points" also means x₀^{(ℓ)} in Theorem 10.
  - (c) C.2 says "For arbitrary (c_∘,d_∘)", although (c_∘,d_∘) was defined as the root.
  - (d) "The first update in (21)": (21) displays M₁ explicitly; the update B(I,g₀,g₁,1)=M₁ is in Lemma 4.
  - (e) v is both the ramp coordinate (line 275) and the second coordinate in F(u,v) (line 359).
  - (f) The article never says that the defined steps (22) are the accepted BFGS steps, s_j = −α_jM_jg_j with α = (1,1/4,1/16). For j = 2 this is the displacement identity of (45); it is implicit in p₂ = 16ρ(1−c_∘,−d_∘) at `seed_certificate.tex:174`.
- **Proposed fix:**
  - (a) `seed_certificate.tex` (1): `$2-q_2$` → `$2-[q]_2$`.
  - (b) `failure.tex` (1): `the three starting points` → `the three base points $z_0,z_1,z_2$`.
  - (c) `seed_certificate.tex` (1): `For arbitrary $(c_\circ,d_\circ)$ with the` → `For an arbitrary point $(c_\circ,d_\circ)$, not only the root, with the`.
  - (d) `seed_certificate.tex` (1): `The first update in \eqref{art:seed_matrices} is immediate from` → `The identity $\mathcal B(I,g_0,g_1,1)=M_1$ is immediate from`.
  - (e) Optionally rename the ramp variable (3 places: lines 275, 281, 286).
  - (f) Optionally add after (23): "Direct substitution for $j=0,1$ and the second identity in \eqref{art:closure_identity} for $j=2$ give $s_j=-\alpha_jM_jg_j$ with $(\alpha_0,\alpha_1,\alpha_2)=(1,1/4,1/16)$."
- **Register items:** A/failure/disp/009, A/failure/lemma/art:seed_cycle, A/seed_certificate/prose/010, A/seed_certificate/disp/009, A/seed_certificate/proof/002, A/failure/disp/015, A/failure/disp/005.

### R-E-10 — line-search specification silent at a nondifferentiable trial point
- **Where:** `failure.tex:22-35`.
- **Quoted text:** "It tests Armijo first and weak Wolfe second: (18) … If both tests hold, the length is accepted."
- **Category:** language (completeness of the specification). **Severity:** cosmetic.
- **Explanation:** The Wolfe test in (18) needs ∇F(x+αp). Lewis–Overton's W(t) includes "h is differentiable at t". The trial order, the bisection/doubling rule and the strictness remark are complete, and all queries in both constructions are differentiable (Theorems 10, 11), so no decision depends on this. Still, the "specified implementation" is undefined there.
- **Proposed fix:** `failure.tex` (1 occurrence): `If both tests hold, the length is accepted.` → `If both tests hold, the length is accepted. (Every point queried in this section is differentiable, so the Wolfe test is always defined.)`
- **Register items:** A/failure/prose/003, A/failure/disp/001.

### R-E-11 — wording
- **Where:** `failure.tex:5-6`, `:57-58`; `seed_certificate.tex:124-125`.
- **Category:** language. **Severity:** cosmetic.
- **Explanation:** "an unrestricted deterministic replacement": a replacement of what is unclear; "guarantee" is meant. "fails to follow to the minimum": G is unbounded below (G(tw) = −t) and has no minimum. "clearing their nonzero denominators": the antecedent is "each substitution".
- **Proposed fix:** `failure.tex` (1): `unrestricted deterministic replacement.` → `unrestricted deterministic guarantee.`; `failure.tex` (1): `fails to follow to the minimum.` → `fails to follow.`; `seed_certificate.tex` (1): `checked by clearing their nonzero denominators and expanding.` → `checked by clearing its nonzero denominators and expanding.`
- **Register items:** A/failure/prose/001, A/failure/prose/011, A/seed_certificate/proof/002.

## Coverage table (every proof, theorem-like environment, table and figure in the two files)

| Object | Location | Result |
|---|---|---|
| §6.1 line-search specification, (18), (19) | failure.tex:21-48 | read: R-E-10 (LO Algorithm 4.6 confirmed) |
| Theorem 10 `art:local-failure` (statement in statements/negative_upper.tex, input at failure.tex:49) | — | read: no finding (statement matches its proof; Hessian bounds 51, 51.80, 6.92 ≤ 64) |
| Design paragraphs, g_i, G, (20)–(23) | failure.tex:56-98 | read: R-E-9(f), R-E-11 (numbers: all recomputed) |
| Lemma 4 `art:seed_cycle` | failure.tex:100-120 | read: M11 (known); R-E-9(a),(b) |
| Table 2 `art:trial_table` | failure.tex:122-150 | read: M11 (known); all 12 enclosures, 9 active branches and 9 decisions recomputed, no new finding |
| Paragraph after Table 2 (margins → decisions) | failure.tex:152-162 | read: no finding |
| Figure 2 `art:cycle-figure` | failure.tex:164-182 | read: R-E-6 |
| Homogeneous induction (26), downhill direction w | failure.tex:184-200 | read: R-E-1(a) |
| Corollary 8 `art:failure_polyhedral` | failure.tex:202-209 | read: R-E-1(b) |
| Proof of Corollary 8 | failure.tex:210-219 | read: no finding |
| §6.3 matched scaling (27)–(28) | failure.tex:226-260 | read: no finding |
| Scalar construction (29), completion | failure.tex:262-303 | read: R-E-9(e) |
| Lemma 5 `art:upper_scalar_lemma` | failure.tex:305-317 | read: no finding (constants 96, 102/b, 139264/(5b²), plateau lengths recomputed) |
| Proof of Lemma 5 | failure.tex:318-354 | read: R-E-4 |
| Objective (32), local model (33) and its justification | failure.tex:356-383 | read: no finding |
| Proof of Theorem 10 | failure.tex:385-425 | read: no finding |
| Figure 3 `art:shrinking-scales` | failure.tex:428-446 | read: R-E-8(e); R-E-2 (its "accumulate at x̄_ℓ") |
| Theorem 11 `art:local-failure-lower` (statement in statements/negative_lower.tex, input at failure.tex:455-457; proof in Appendix D, not mine) | — | read: R-E-8(a) (layout); its "hyperbolic" summary checked numerically (J, λ_s, λ_u) |
| Table 3 `art:regularity-map` | failure.tex:461-482 | read: R-E-2, R-E-8(b) |
| Hessian convention | failure.tex:484-486 | read: R-E-7 |
| Lower-curvature summary | failure.tex:488-514 | read: R-E-1(c), R-E-2, R-E-5 |
| C.1 introduction, (43), r̄ | seed_certificate.tex:1-36 | read: no finding (r̄ = root rounded to 50 decimals; |root − r̄|∞ = 6.0·10⁻⁵²) |
| Lemma 8 `art:root_certificate` | seed_certificate.tex:38-41 | read: no finding |
| Proof of Lemma 8, (44) | seed_certificate.tex:42-93 | read: R-E-8(d) only (all bounds recomputed exactly) |
| Proof of the algebraic part of Lemma 4, (45) | seed_certificate.tex:95-139 | read: R-E-3, R-E-9(c),(d), R-E-11 |
| C.3 interval certificate, (46), (47) | seed_certificate.tex:141-200 | read: R-E-9(a), R-E-8(d); M11 at :199-200 (known, register prose/012) |

## Verification log (exact or high-precision recomputation)

- **Root:** Newton in exact fractions from r̄. The root is c_∘ = 0.3184814276271186306464513125029070371791220502360504555…, d_∘ = −1.0252321196757487254813508700130041428451190931844393951… So r̄ is the root rounded to 50 decimals, and |root − r̄|∞ = 6.05·10⁻⁵².
- **(44):** det D = 1.0993·10¹⁰. |AP(r̄)| = (4.56·10⁻⁵², 6.05·10⁻⁵²) < 10⁻⁵⁰. The index set has 18 monomials. max_i Σ|a_{i,ν}||ν| = 6371.66 (row 2: 1594.60) ≤ 7000. 10⁻⁵⁰ + 7000·10⁻⁶⁰ < 10⁻³⁰.
- **Lemma 8 bounds:**
  - U, V, R endpoints on the coarse box are exactly the printed 2397/100, 24113/1000, 119263/1000, 59703/500, 4259/500, 8527/1000.
  - Ranges of the other factors on the coarse box: K ∈ [0.189, 0.209], T ∈ [0.833, 0.836], Y ∈ [1.514, 1.518], U+129 ∈ [152.97, 153.11].
  - Endpoint products give ρ ∈ [0.060102, 0.060294] ⊂ (0.060, 0.061).
- **Seed constants:** ρ = 0.06019920610754376…, b_* = 33.44439068… ∈ (33,34). β = 1/4 and γ = 1/16 at the root. ρ̃ − ρ ≈ 10⁻²⁰⁰.
- **Cycle:**
  - B(I,g₀,g₁,1) = M₁ exactly.
  - M₂ = [[0.674238, 0.849722],[0.849722, 1.227148]], det 0.105362 > 0.
  - p₁ = (127/256, 1/16); p₂ − 16ρ(1−c,−d) ≈ 10⁻⁸⁰.
  - B(M₂,g₂,g₀,1/16) − ρI ≈ 10⁻⁸¹ (80-digit root); z₃ − ρz₀ = 0.
  - z₀ = (0.888433, −0.082297), z₁ = (−0.111567, −0.082297), z₂ = (0.012456, −0.066672), z₃ = (0.053483, −0.004954).
- **Table 2:**
  - 10⁴G values: current 8884.326, 1218.546, 723.217; trials 1218.546, 3845.264, 1364.795, 723.217, 6688.861, 3406.711, 1765.636, 945.098, 534.829. All lie strictly inside the printed open intervals.
  - Active branches 1, 0, 0, 2, 0, 0, 0, 0, 0 as printed; unique active branch at z₀, z₁, z₂ = g₀, g₁, g₂.
  - Naive interval evaluation over the query box (46), computing z_j by (23) and p_j as printed, reproduces every printed enclosure. For example, (6687, 6691) ⊃ [6687.69, 6690.21].
- **(47):**
  - Interval lower bounds (min over the row's expressions): 0.072976, 0.24173, 0.014590, 0.0075038, 0.59643, 0.26826, 0.10418, 0.022140, 0.0020572. All exceed the printed 0.0729 … 0.0020 strictly; the slack is thinnest in row 4 (3.8·10⁻⁶).
  - Exact values at the root: 0.073013, 0.241765, 0.014625, 0.0075407, 0.596564, 0.268349, 0.104242, 0.022188, 0.0021024.
  - Both groupings of the gap expressions pass.
- **Ranges:**
  - Armijo ratios r₀ = 0.76657807, r₁ = 0.39319094, r₂ = 0.37520596 (> 1/3). Every rejection has G(q) − G(z_j) > 0. Wolfe products at acceptances are 1, 0.02348, 0.04103 (> 0, so Wolfe holds for every c₂ > 0).
  - (25): max |g_iᵀz| = 0.888 < 3, max [z]₂ = 0.921 < 2, min G = 0.0535 > 0.
  - Query box: ρ from (20) on the (c,d) box is [0.0601991, 0.0601993] ⊂ [0.06019, 0.06021].
- **Corollary 8:** weights 8/17, 8/17, 1/17 give −1 identically; (−1,16) is the unique minimizer (branch 2 there: −c+16d = −16.72 < −1); the sublevel bounds hold; v − 17 < −15 at all queries.
- **Lemma 5 / Theorem 10:**
  - t₂ = 239/510; t_{b*} = 0.97191; t_b ± ε ∈ (0,1) on [2,34].
  - Constant-derivative lengths/a_ℓ: (0.9817, 13.82) at b = 2, (0.6358, 483.7) at b_*, (0.6297, 491.96) at b = 34; both exceed 1/2 on [2,34] by linearity in b.
  - P_b′ ≤ 96, 102/b, |P_b″| ≤ 24576, 139264/(5b²). L_2 = 6963.2, L_{b*} = 24.90.
  - Hessian norms 51, 51.797, 6.915 (≤ 12 ≤ 64). 3a_ℓ² ≤ 3a_ℓ/16 < a_ℓ/2 for ℓ ≥ 1. The max norm over base points and queries is 1.138.
- **Appendix D hyperbolicity (summarized at failure.tex:491-492):**
  - 10¹⁰J = [[11123986250.73, 6459701027.32],[7515015704.27, 4905136885.83]], inside the printed enclosures.
  - Eigenvalues 0.0384799 and 1.5644324; p(.038) > 0, p(.039) < 0, p(1.564) < 0, p(1.565) > 0.
  - ρ̂(P_*) = ρ.
