# Reading F: Appendix D (`paper/appendices/lower_curvature.tex`)

- **File read line by line:** `step2/snapshot/paper/appendices/lower_curvature.tex`, lines 1-331
  (sha256 60223fd5…, identical to commit c8db802).
- **Read for context:** `sections/failure.tex` (whole), `statements/negative_lower.tex`,
  `statements/negative_upper.tex`, `appendices/seed_certificate.tex`, `sections/energy.tex:1-60`,
  `sections/introduction.tex`, `preprint_references.tex`, the `LO` entry of `bibliography.tex`;
  the register `A_lower_curvature.json` (plus `A_failure.json` and `C_13_L.json` for the ids of
  other locations); the Lean statements and proofs `BfgsCoverage.Article.LowerCurvature.{quadratic_failure,
  lower_hyperbolic, shape_certificate, shape_box, characteristic_signs, return_block_form,
  stable_manifold_positive_scale, copy_runs, copy_transfer}`, `LUniform.{orbit_exists,
  uniform_global_failure, source_spec}`; `companion/chapters/13_L.tex` (to find recurrences).
- **Cited sources checked:** Dyatlov, arXiv:1805.11660v1: §3.1 "Making δ small by rescaling",
  §3.5 Theorem 3 (general stable/unstable manifold theorem) and Remark 4 (the §3.1 rescaling
  applies). These match the locator. Lewis–Overton 2013 (author copy of the published version),
  §2: the invariance of Broyden-class methods under x ↦ Ax. This matches "[LO, Section 2]".
- **PDF pages:** 43-48 of `baseline/paper.pdf`, rendered at 110 dpi (whole pages) and 170-220 dpi
  (crops). The baseline log has no overfull or underfull box in Appendix D.
- **Time spent:** about 25 minutes (03:11-03:35).
- **Exact checks** (Python `fractions`, scratch scripts in `read_F/scratch/`):
  - ḡ: its pairings and weights; min Q_μ = −1/(514μ).
  - J at the 50-digit root centre: 10¹⁰J ≈ [[11123986250.73, 6459701027.32], [7515015704.27,
    4905136885.83]], inside every printed interval. A plain interval evaluation over the two
    printed (c∘,d∘) intervals stays inside the enclosure (entry widths below 0.03 against the
    printed 4-8).
  - λ_s = 0.0384799…, λ_u = 1.5644324…. The four signs of p hold at all 16 vertices of the
    enclosure box (p is affine in each entry).
  - The full 5×5 Jacobian of T_μ at P_* (forward-mode, exact rationals) has the printed block
    form. Its ρ-eigenvector with τ-coordinate 1 is (2.11e-4, −4.08e-4, −3.98e-4, 7.07e-4, 1).
  - D.2 constants: b₀ = b₁ = 1791/1024, b₂ = 33.1934…, and ε < t_b < 1 − ε for both values of
    b. The plateau lengths are 0.9925 and 94.66 (b₀), 0.7163 and 4115.6 (b₂). Also P_b′ ≤ 768,
    L₀ = 438.70…, L₁ = 445.56…, L₂ = 26.29… and C_* = 2305/2048.
  - Incidental, not claimed in the text: det J agrees with ρ to 50 digits.

**Summary.** 13 findings: 0 major, 5 minor, 8 cosmetic. Every mathematical claim of Appendix D
was recomputed and is correct. The minor findings concern three things:
- one hypothesis that the proposition does not supply (R-F-1);
- one undefined term that clashes with a defined term (R-F-2);
- three precision points (R-F-3 to R-F-5).

---

## Findings

### R-F-1: Proposition `art:quadratic_failure` does not put the initial point in V, but D.3 needs it
- **Where:** `lower_curvature.tex:49-50` (statement), `:176-180` (proof), `:293-296` and
  `:305-306` (use).
- **Text:**
  - Statement: "Its accepted lengths repeat $1,1/4,1/16$, and all accepted and rejected query
    points are differentiable and belong to $V$."
  - Proof: "More explicitly, each of the finitely many physical candidate maps has the form
    $\Phi_q(w)=\tau q(w)$ … Every physical query lies in $V$."
  - Use: "Choose, by Proposition~\ref{art:quadratic_failure}, one bad orbit
    $(x_k^{\rm seed},H_k^{\rm seed})$ all of whose queries lie in this neighborhood … For every
    $\ell$, start at $\bar x_\ell+a_\ell x_0^{\rm seed}$ … Equation~\eqref{art:lower_local_model}
    applies to every query because the whole chosen seed orbit lies in its domain."
- **Category:** gap (hypothesis). **Severity:** minor.
- **Explanation:**
  - In this article a query is a trial point x_k + αp_k. Lemma `art:seed_cycle` speaks of "All
    listed queries and the three starting points", and Table `art:trial_table` lists only trial
    points. Every iterate x_{k+1} is an accepted query; the start x₀ is not.
  - Copy ℓ starts at x̄_ℓ + a_ℓx₀^seed. Its first line search needs F and ∇F there to equal
    a_ℓ²(C_* + Q_μ(x₀^seed)) and a_ℓ∇Q_μ(x₀^seed). That requires (55) on a neighbourhood of
    x₀^seed. The same identity at k = 0 is used in F(x_k^(ℓ)) ↓ a_ℓ²C_*.
  - Neither the printed proposition nor its proof places x₀ in V. The proof's maps Φ_q are the
    "physical candidate maps", that is, the trial points. So "the whole chosen seed orbit lies in
    its domain" (:306) is not supplied by the cited result.
  - The repair is one more map of the same kind: x₀ = τz is Φ(w) = τq(w) with q(w) = z and
    Φ(P_*) = 0.
- **Lean:** the library carries the stronger fact:
  - `LUniform.orbit_exists` and `LUniform.source_spec` give `∀ k, O.x k ∈ U`;
    `LUniform.uniform_global_failure` gives `∀ k, R.x k ∈ U`;
  - `copy_runs` uses `LUniform.source.x k ∈ LEmbedding.localDomain` for every k, including 0.
  - The register's reading of the printed proposition, `BfgsCoverage.Article.LowerCurvature.quadratic_failure`,
    states only the queries.
  - So the printed D.3 relies on more than the printed proposition. The statement-level fix is
    already proved in the library.
- **Same slip elsewhere** (generated chapter; fix through `editorial/generate_companion.py`):
  - `companion/chapters/13_L.tex:237` "all queries of the orbit" (C/13_L/proof/002);
  - `:355` "whose accepted and rejected queries are all in that neighborhood" (C/13_L/prose/062);
  - `:363` "applies to every query by the choice of the whole seed orbit" (C/13_L/prose/065).
- **Fix** (`lower_curvature.tex`):
  1. old `and all accepted and rejected query points are` (1 occurrence, line 49) → new
     `and its initial point and all accepted and rejected query points are`
  2. old `each of the finitely many physical candidate maps has` (1, line 176) → new
     `each of the finitely many physical candidate maps, and the initial-point map $w\mapsto\tau z$, has`
  3. old `Every physical query lies in $V$.` (1, line 180) → new
     `The initial point and every physical query lie in $V$.`
  4. old `all of whose queries lie in this` (1, line 294) → new
     `whose initial point and queries all lie in this`
- **Register items:**
  - A/lower_curvature/proposition/art:quadratic_failure (the Lean statement would gain
    `x 0 ∈ V`, available from `uniform_global_failure`);
  - A/lower_curvature/proof/002, A/lower_curvature/prose/027, A/lower_curvature/prose/028,
    A/lower_curvature/disp/021.

### R-F-2: "admissible pair" is never defined and clashes with Definition `art:admissible`
- **Where:** `lower_curvature.tex:13-14`, `:88`, `:104`, `:182`, `:295`.
- **Text:**
  - "The line-search constants are any fixed pair $0<c_1\le1/3$, $c_1<c_2<1$, as in
    Theorem~\ref{art:local-failure};"
  - Later uses: "for every admissible pair $(c_1,c_2)$" (:88), "for all admissible pairs" (:104),
    "every admissible pair" (:182, :295).
- **Category:** notation. **Severity:** minor.
- **Explanation:**
  - "Admissible" is a defined term of the article. Definition `art:admissible` (`energy.tex:12-27`)
    and `introduction.tex:55-58` allow any fixed 0<c₁<c₂<1. "Admissible pair" is never defined.
  - Read with the article's definition, Lemma `art:lower_hyperbolic` would claim the query lists
    for c₁ ∈ (1/3, 1), which is false. As M11 records for the seed, at c₁ = 0.38 the phase-2
    accepted trial fails Armijo: its decrease ratio is about 0.3755.
  - The intended range is the one fixed at :13-14. The Lean `LUniform.Admissible` is
    0<c₁≤1/3 ∧ c₁<c₂<1.
  - This is related to M11 but distinct from it: here the range is stated once, then referred to
    by an undefined word.
- **Same slip elsewhere:** `failure.tex:495` "for every admissible pair $(c_1,c_2)$"
  (A/failure/prose/063), which comes before the appendix.
- **Fix:**
  - `lower_curvature.tex`: old `fixed pair $0<c_1\le1/3$, $c_1<c_2<1$, as in` (1, line 14) → new
    `fixed admissible pair $0<c_1\le1/3$, $c_1<c_2<1$, as in`
  - `failure.tex`: old `for every admissible pair $(c_1,c_2)$` (1, line 495) → new
    `for every pair $0<c_1\le1/3$, $c_1<c_2<1$`
- **Register items:** A/lower_curvature/prose/011, A/lower_curvature/lemma/art:lower_hyperbolic,
  A/lower_curvature/proof/001, A/lower_curvature/proof/002, A/lower_curvature/prose/027;
  A/failure/prose/063.

### R-F-3: The lemma does not say at which point the eigenvalues are taken
- **Where:** `lower_curvature.tex:89-90`.
- **Text:** "and \eqref{art:lower_return} is their return map. Its derivative has eigenvalues"
- **Category:** language. **Severity:** minor.
- **Explanation:** the spectrum is that of DT_μ(P_*): the block form at :143 and the register
  reading (charpoly of `fderiv … seed`). The derivative at other states of the neighbourhood has
  other eigenvalues. As printed, "Its derivative" names no point.
- **Fix:** old `Its derivative has eigenvalues` (1, line 90) → new
  `Its derivative at $P_*$ has eigenvalues`
- **Register items:** A/lower_curvature/lemma/art:lower_hyperbolic, A/lower_curvature/disp/007.

### R-F-4: z_m and τ_m are not introduced, and z₀ already means the seed point
- **Where:** `lower_curvature.tex:171` (also w at :177).
- **Text:** "The physical iterates are $x_{3m}=\tau_mz_m\to0$."
- **Category:** notation. **Severity:** minor.
- **Explanation:**
  - The return orbit (z_m, ζ_m, η_m, τ_m) of the chosen point, and the state letter w used at
    :177, are never introduced.
  - z₀ is the seed point: P_* = (z₀,0,1,0) at :64, and z_j in `failure.tex:94-97`. At m = 0 the
    printed formula therefore reads x₀ = τ₀z₀ with the seed's z₀. That is false in general: the
    chosen start lies on the stable manifold, near the seed but not at it.
- **Fix:** old `The physical iterates are $x_{3m}=\tau_mz_m\to0$.` (1, line 171) → new
  `Let $w_m=(\hat z_m,\zeta_m,\eta_m,\tau_m)$ be the $m$th return of the chosen point $w_0$. The physical iterates are $x_{3m}=\tau_m\hat z_m\to0$.`
- **Register items:** A/lower_curvature/proof/002.

### R-F-5: G is not defined in the appendix the text points to
- **Where:** `lower_curvature.tex:25-27`.
- **Text:** "Use the fixed slopes of Appendix~\ref{art:seed_certificate} and let
  $Q_\mu(x)=\tfrac\mu2\|x\|^2+G(x)$"
- **Category:** reference. **Severity:** minor.
- **Explanation:** g₀, g₁, g₂ and G(z) = max g_iᵀz are defined in Section 6 (`failure.tex:74-77`).
  Appendix C only specifies the pair (c∘,d∘) and never defines G.
- **Fix:** old `Use the fixed slopes of Appendix~\ref{art:seed_certificate} and let` (1, line 25)
  → new `Use the slopes $g_0,g_1,g_2$ and the function $G$ of Section~\ref{art:failure} and let`
- **Register items:** A/lower_curvature/disp/001.

### R-F-6: The shape map and v(ζ,η) are used without being written down
- **Where:** `lower_curvature.tex:109-110`, `:139`.
- **Text:** "Let $J$ be the derivative at $(\zeta,\eta)=(0,1)$ of its normalized shape map." and
  "At $\tau=0$, $Z_3=z+v(\zeta,\eta)$ and $\hat\rho$ is independent of $z$."
- **Category:** notation. **Severity:** cosmetic.
- **Explanation:**
  - The "normalized shape map" is (ζ,η) ↦ ((M₃)₁₂, (M₃)₂₂)/ρ̂ at τ = 0, the middle coordinates of
    (50). It is never displayed; the companion displays it at `13_L.tex:189-192`.
  - v is undefined. It is the sum of the three normalized steps, which at τ = 0 depends only
    on (ζ,η).
  - Minor clashes inside the appendix: J (the Jacobian) against J_b (the primitive of D.2), and
    q_i (the shifted slopes) against q(w) and Φ_q (the query maps).
- **Fix:**
  - old `of its normalized shape map.` (1, line 110) → new
    `of its normalized shape map $(\zeta,\eta)\mapsto((M_3)_{12},(M_3)_{22})/\hat\rho$.`
  - old `$Z_3=z+v(\zeta,\eta)$` (1, line 139) → new
    `$Z_3=z+v(\zeta,\eta)$, with $v$ the sum of the three normalized steps,`
- **Register items:** A/lower_curvature/proof/001.

### R-F-7: A period ends display (49) in mid-sentence
- **Where:** `lower_curvature.tex:72-74`.
- **Text:** `+\frac{SS^T}{Y^TS}.\notag` … "with cyclic gradient indices and $\alpha=(1,1/4,1/16)$."
- **Category:** language (punctuation). **Severity:** cosmetic.
- **Explanation:** the sentence continues after the display, as page 44 shows ("…/YᵀS." then "with
  cyclic gradient indices…").
- **Fix:** old `+\frac{SS^T}{Y^TS}.\notag` (1, line 72) → new `+\frac{SS^T}{Y^TS},\notag`
- **Register items:** A/lower_curvature/disp/005, A/lower_curvature/prose/042.

### R-F-8: Display (55) is asserted for ℓ ≥ 1 but used for every ℓ
- **Where:** `lower_curvature.tex:286`, `:296`.
- **Text:** "$F(\bar x_\ell+a_\ell y)=a_\ell^2\{C_*+Q_\mu(y)\}\qquad(\ell\ge1)$" and "For every
  $\ell$, start at $\bar x_\ell+a_\ell x_0^{\rm seed}$".
- **Category:** notation (index range). **Severity:** cosmetic.
- **Explanation:** (55) is also true for ℓ = 0, through ψ_b(x) = 1+x−b for x ≥ b, and the library
  proves it for all ℓ. But the printed text does not justify ℓ = 0. Theorem `art:local-failure`
  uses ℓ ≥ 1 (`failure.tex:386`).
- **Fix:** old `For every $\ell$, start at` (1, line 296) → new `For every $\ell\ge1$, start at`
- **Register items:** A/lower_curvature/disp/020, A/lower_curvature/disp/021.

### R-F-9: Ramp reference and plateau lengths are imprecise
- **Where:** `lower_curvature.tex:214-215`, `:236-241`.
- **Text:** "Use the same cubic ramp $P_b$ and primitive $J_b$ as in \eqref{art:upper_scalar}, with
  this center and width." and "The two constant-derivative lengths, divided by $a_\ell$, are …
  both greater than $1/2$ for these values of $b$."
- **Category:** reference and language. **Severity:** cosmetic.
- **Explanation:**
  - (29) is the formula for φ_b. P_b and J_b are defined in the unnumbered displays just before it
    (`failure.tex:273-287`).
  - The two lengths lie below and above the node ba_ℓ; the second is measured inside interval
    ℓ−1.
  - For ℓ = 0 there is no interval above b. The plateau of (53) there comes from ψ_b = 1+x−b.
  - Section 6 states both points (`failure.tex:339`, `:346-347`); the appendix states neither.
  - The numbers themselves are right: 0.9925 and 94.66 for b₀; 0.7163 and 4115.6 for b₂.
- **Fix:**
  - (a) old `primitive $J_b$ as in` (1, line 214) → new `primitive $J_b$ as before`
  - (b) old `The two constant-derivative lengths, divided by $a_\ell$, are` (1, line 236) → new
    `The constant-derivative lengths below and above $ba_\ell$, divided by $a_\ell$, are`
  - (c) old `both greater than $1/2$ for these values of $b$. Consequently` (1, line 241) → new
    `both greater than $1/2$ for these values of $b$; the affine outer extension covers the upper side when $\ell=0$. Consequently`
- **Register items:** A/lower_curvature/prose/013, A/lower_curvature/disp/016,
  A/lower_curvature/disp/017.

### R-F-10: Hard-to-parse apposition in the proof of Lemma `art:lower_hyperbolic`
- **Where:** `lower_curvature.tex:102-104`.
- **Text:** "The strict inequalities of Lemma~\ref{art:seed_cycle}, \eqref{art:seed_margins} at each
  acceptance and a value increase at each rejection, decide every test"
- **Category:** language. **Severity:** cosmetic.
- **Explanation:** the sentence reads as a list of three subjects.
- **Fix:** old `\eqref{art:seed_margins} at each acceptance` (1, line 103) → new
  `namely \eqref{art:seed_margins} at each acceptance`
- **Register items:** A/lower_curvature/proof/001.

### R-F-11: Two loose phrases
- **Where:** `lower_curvature.tex:265`, `:174-175`.
- **Text:** "Since $F(x)\ge\mu\|x\|^2/2$ with equality zero at the origin," and "Armijo makes the
  values decrease to zero, which exceeds \eqref{art:quadratic_minimizer}."
- **Category:** language. **Severity:** cosmetic.
- **Explanation:** "with equality zero" is garbled. The second sentence compares a number with an
  equation.
- **Fix:**
  - old `Since $F(x)\ge\mu\|x\|^2/2$ with equality zero at the origin, the` (1) → new
    `Since $F(x)\ge\mu\|x\|^2/2$ and $F(0)=0$, the`
  - old `values decrease to zero, which exceeds \eqref{art:quadratic_minimizer}.` (1) → new
    `values decrease to zero, which exceeds $\min Q_\mu$ in \eqref{art:quadratic_minimizer}.`
- **Register items:** A/lower_curvature/prose/022, A/lower_curvature/proof/002.

### R-F-12: Decimals without a leading zero
- **Where:** `lower_curvature.tex:93`, `:133`.
- **Text:** "$.038<\lambda_s<.039$" and "$p(.038)>0,\qquad p(.039)<0$".
- **Category:** number style. **Severity:** cosmetic.
- **Explanation:** these are the only such decimals in the article. Elsewhere it writes
  "0.060<ρ<0.061" (`failure.tex:82`) and "0.318<c∘<0.319" (`:78`); the companion writes 0.038
  (`13_L.tex:203`). The values are correct (λ_s = 0.03848…).
- **Fix:** old `.038` (2 occurrences, lines 93 and 133) → new `0.038`; old `.039` (2) → new `0.039`.
- **Register items:** A/lower_curvature/disp/007, A/lower_curvature/disp/010.

### R-F-13: Bad line breaks and a stray space
- **Where:** `lower_curvature.tex:46`, `:308`, `:113`.
- **Category:** typesetting. **Severity:** cosmetic.
- **Explanation:**
  - (a) PDF p. 43, Proposition 1: the line breaks inside the inequality "0 < | c₁ ≤ 1/3".
  - (b) p. 48: the break falls after the arrow, "F(x_k^(ℓ)) ↓ | a_ℓ²C_* > 0".
  - (c) p. 44, (51): `10^{10}J\ \in` adds a visible extra space before ∈.
  - Everything else in Appendix D renders cleanly. Displays (49)-(55), the block matrix and the
    enclosure matrix (51) fit the text width, and the log shows no box warnings in Appendix D.
- **Fix:**
  - (a) old `produces for every fixed pair $0<c_1\le1/3$,` (1) → new
    `produces for every fixed pair ${0<c_1\le1/3}$,`
  - (b) old `$F(x_k^{(\ell)})\downarrow a_\ell^2C_*>0$` (1) → new
    `${F(x_k^{(\ell)})\downarrow a_\ell^2C_*>0}$`
  - (c) old `10^{10}J\ \in` (1) → new `10^{10}J\in`
- **Register items:** A/lower_curvature/proposition/art:quadratic_failure,
  A/lower_curvature/disp/008, A/lower_curvature/prose/029.

---

## Coverage table

| Environment or block (snapshot lines) | Result |
|---|---|
| Appendix introduction (1-15) | R-F-2 (M8 at 11-13 already recorded) |
| D.1 opening, display Q_μ (17-28) | R-F-5 |
| ḡ display, least-norm claim, (48) `art:quadratic_minimizer`, nonsmooth minimizer, ∂Q_μ(0) (29-42) | read: no finding (checked exactly) |
| Proposition `art:quadratic_failure` (44-51) | R-F-1, R-F-13 |
| Normalized coordinates, (49) `art:lower_return_substep`, (50) `art:lower_return`, seed closure, analyticity (53-83) | R-F-7 |
| Lemma `art:lower_hyperbolic` (85-96) | R-F-2, R-F-3, R-F-12 |
| Proof of Lemma `art:lower_hyperbolic`, with (51) `art:shape_certificate`, intervals, signs of p, block form, ρ-eigenvector (97-154) | R-F-6, R-F-10, R-F-12, R-F-13 (all values recomputed: no error) |
| Proof of Proposition `art:quadratic_failure` (156-185): inverse function theorem, stable manifold, citation [DY], positivity, limits, all queries in V | R-F-1, R-F-2, R-F-4, R-F-11 (citation checked) |
| D.2 plan, constants, t_b, (52) `art:lower_scalar`, ψ_b′ and ψ_b″, node matching, C^{1,1}, plateau lengths, (53) `art:lower_plateau`, no ψ_b″(0) (187-247) | R-F-9 (all constants recomputed) |
| (54) `art:lower_objective`, μ-strong convexity, three branches not twice differentiable, L_i < 439, 446, 27, compact sublevels, nonsmooth minimizer, Hessian bounds (249-279) | R-F-11 |
| D.3 (55) `art:lower_local_model`, its justification, choice of the seed orbit, copying, limits, active gradients, query norms (281-311) | R-F-1, R-F-2, R-F-8, R-F-13 |
| D.3 whitening, constants μ̲ and L̄, citation [LO, §2], conclusion (313-331) | read: no finding (citation checked) |
| Theorem `art:local-failure-lower` (proved here; statement in `statements/negative_lower.tex`): every conclusion traced to D.2-D.3 | read: no finding beyond R-F-1 (x₀^(ℓ) → 0 and F(x̄_ℓ) = a_ℓ²C_* are immediate) |
