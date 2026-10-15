# Reader D: line-by-line reading of Section 5 and Appendix B

## Header

- **Files read in full** (snapshot `$S/step2/snapshot/paper/`, identical to commit c8db802):
  `sections/local.tex` (440 lines, Section 5) and `appendices/planar_geometry.tex`
  (234 lines, Appendix B). Also `statements/positive_partition.tex`, the statement of
  Theorem 7 (`art:polyhedral`), whose proof is in `local.tex`.
- **Read for definitions and the results used:** `master.tex`, `sections/introduction.tex`,
  `sections/geometry.tex`, `sections/energy.tex` (Definition 1, Lemma 1, Theorems 2 and 3),
  `sections/global.tex` (conditions (14) and (15), Corollary 1, Theorem 5),
  `bibliography.tex` and `preprint_references.tex`.
- **Registers:** `A_local.json`, `A_planar_geometry.json`, `A_positive_partition.json`.
  The Lean statements of `planar_cluster`, `planar_cluster_field`, `planar_cluster_energy`,
  `planar_convergence`, `planar_max`, `planar_max_hessian_contours`, `nonradial_example`,
  `planar_field` and `corner_curve` were read in the live coverage modules (read only).
- **PDF pages:** 16 to 23 and 36 to 39 of `$S/baseline/paper.pdf`, rendered at 110 dpi,
  with zooms at 170 to 200 dpi of pages 19, 20 and 38. The line right edges were measured
  with PyMuPDF; no line passes the right margin. `paper.log` has no warning on these pages.
- **Exact checks:** Python `fractions` and a small polynomial routine, in
  `read_D/scratch/`. They cover the determinant D, the three Cramer numerators, the box
  bounds, the tie formula and its expansion, the radial jump, d, t, Δ, and the limit of
  yᵀz. A numerical run confirms eligibility for c₁ = 1/4, c₂ = 1/2.
- **Cited sources checked online:** Bogosel 2022 preprint, Section 2, equation (4)
  (x(θ) = p n + p′ t, tangent (p + p″) t); Wachsmuth–Wachsmuth 2022 preprint, Theorem 2.5
  (Baillon–Haddad on open convex sets); Lewis–Wylie 2019 preprint, Propositions 5.5–5.6
  (robust affine independence, continuous unique multipliers). All three say what the text
  attributes to them.
- **Time spent:** about 30 minutes (03:10 to 03:40 PDT).
- **Summary:** 7 findings: major 0, minor 2 (R-D-1, R-D-2), cosmetic 5 (R-D-3 to R-D-7).
  The mathematics of both files holds as printed. Every inference was recomputed (see
  "Checks without findings"). The findings are:
  - a missing qualifier d ≤ 1 where Theorem 8's proof uses Lemma 7;
  - imprecise descriptions of the region of the construction;
  - symbols reused within one proof;
  - bad line breaks;
  - three small wording points.

In the tables of fixes, "×n" is the number of occurrences of the old string in the file.
A `⏎` in an old string marks a source line break.

## Findings

### R-D-1. Theorem 8's proof states λ² ≤ 1 + Ld without the lemma's condition d ≤ 1

- **Where:** `sections/local.tex:251-260` (PDF p. 20).
- **Quoted:** "For each sufficiently close eligible pair in that neighborhood, it gives
  uniform constants $m>0,C,L\ge0$ and scalars $\lambda>0,\beta$ with … $w(z)=\lambda
  w(x)+\beta s,\qquad \lambda^2\le1+Ld.$ Compactness implies
  $\operatorname{dist}(x_k,\Gamma)\to0$, so these estimates apply to the entire tail, not
  just a selected subsequence."
- **Category:** gap (hypothesis of the cited lemma). **Severity:** minor.
- **Explanation:** Lemma 7 (`art:planar-field`), item 3 (`planar_geometry.tex:33`), gives
  λ² ≤ 1 + Ld only under "d ≤ 1 ⟹". Its proof needs this restriction: the chord bound
  e^{4Ad} ≤ 1 + (e^{4A} − 1)d (`planar_geometry.tex:186-188`) fails for d > 1. The theorem's
  display drops the restriction, and line 266 uses the factor (1 + Ld_k) on the tail.
  - Close pairs do satisfy d ≤ 1, but no line says so.
  - Repair: Σ d_k < ∞ (first line of the proof) gives d_k → 0, so d_k ≤ 1 on the tail.
    Alternatively, take δ ≤ 1/Λ, where Λ bounds the subgradients on the compact buffer;
    then d ≤ Λ‖s‖ ≤ 1. The Lean proof does the latter (`planar_cluster_field` takes
    `min δ (1/G)`).
  - The sentence about the tail also relies silently on s_k → 0 ("The steps tend to zero",
    line 235) to get ‖s_k‖ < δ.
- **Fix** (`sections/local.tex`):

  | old (×1) | new |
  |---|---|
  | `For each sufficiently close eligible pair in that neighborhood,` | `For each sufficiently close eligible pair in that neighborhood with $d\le1$,` |
  | `Compactness implies $\operatorname{dist}(x_k,\Gamma)\to0$, so these estimates` | `Compactness implies $\operatorname{dist}(x_k,\Gamma)\to0$; with $s_k\to0$ and $d_k\to0$, these estimates` |

- **Register items:** A/local/proof/005, A/local/disp/008. The planar register item
  A/planar_geometry/prose/001 already notes the restriction.

### R-D-2. The region of the planar construction: "noncritical" and "the compact level set"

- **Where:**
  - `sections/local.tex:177` "Here is the construction near a compact noncritical part of
    a positive level." (p. 19)
  - `sections/local.tex:209-210` "These yield one field on a neighborhood of the compact
    level set, not just separate directions at its corners." (p. 19)
  - `sections/local.tex:297-298` "In the plane these same assumptions leave at most two
    active branches at a noncritical point, which supplies the required regular
    switching." (p. 21)
- **Category:** language (wrong word that changes the meaning). **Severity:** minor.
- **Explanation:** The construction needs every point of the compact set to be
  non-affine-critical (Lemma 7, `planar_geometry.tex:12`). It builds the field only near
  that compact set C ⊂ {F = ℓ}; Theorem 8 uses the cluster set Γ.
  - **"Noncritical."** For convex F, "critical" ordinarily means stationary (0 ∈ ∂F). At a
    positive level every point is non-stationary, so "noncritical" restricts nothing.
    The actual restriction is non-affine-criticality, defined at lines 157-159, and the two
    differ. The paper's own seed corner is a counterexample:
    it is nonstationary, yet affine critical, since its three slopes are affinely
    independent (`geometry.tex:35-38`).
  - **Line 298.** Here "noncritical" again means non-affine-critical: the proof says "Away
    from affine criticality" (lines 344-345). Under Corollary 7's assumptions the two
    notions agree near x_* only as a consequence of the affine-correctness argument, which
    comes later.
  - **"The compact level set."** It reads as the whole level {F = ℓ}. That set may contain
    affine-critical points, where no structure is assumed ("No local representation is
    required at affine-critical points", line 226). The field lives near a compact
    non-affine-critical part of the level.
- **Fix** (`sections/local.tex`):

  | old (×1 each) | new |
  |---|---|
  | `compact noncritical part` | `compact non-affine-critical part` |
  | `of the compact level set` | `of that compact part of the level` |
  | `at a noncritical point,` | `at a non-affine-critical point,` |

- **Register items:** A/local/prose/027, A/local/prose/034, A/local/prose/038.

### R-D-3. Symbols reused for different objects in one argument

This is the same kind of slip as the resolved M3.

- **Where:** `appendices/planar_geometry.tex` (pp. 36-39); `sections/local.tex:52-69`
  (p. 17), `local.tex:205` and `local.tex:218` (pp. 19-20).
- **Category:** notation. **Severity:** cosmetic.
- **Explanation, with a fix for each:**
  - **(a) `e`: Dw entry and Euler's number.** In the transport paragraph `e` is the (n,n)
    entry of Dw (`planar_geometry.tex:118, 151`: "(a−e)s_T"). Three lines later it is
    Euler's number (`:188`: "e^{4Ad}", "e^{4A}").

    | old (×1, `planar_geometry.tex`) | new |
    |---|---|
    | `$\lambda^2\le e^{4Ad}\le1+(e^{4A}-1)d$.` | `$\lambda^2\le\exp(4Ad)\le1+(\exp(4A)-1)d$.` |

  - **(b) `θ`: normal angle and segment parameter.**
    - It is the normal angle in n(θ), T(θ), h(t,θ) and θ(x) (`planar_geometry.tex:71-113`;
      also `local.tex:190-197`).
    - It is the segment parameter in item 2 of the lemma (`:26`) and in q(θ), φ(θ), D(θ),
      H(θ) (`:144-183`).
    - In the transport paragraph "the basis (T,n)" is taken at the normal angle of
      ∇F(q(θ)), not at θ.

    | old (×1, `planar_geometry.tex`) | new |
    |---|---|
    | `Write $q(\theta)=x+\theta s$,` | `Write $q(\theta)=x+\theta s$ ($\theta\in[0,1]$ is now a segment parameter, not a normal angle),` |

  - **(c) `r`: radius and r_x.** In the proof of Theorem 7, `r` is the radius of
    B_r(x_*) (`local.tex:52, 69`). `r_x = x − x_*` appears in the same display:
    "≤ ½Lτ²‖r_x‖² ≤ ½Lr²τ²".

    | old (×1, `local.tex`) | new |
    |---|---|
    | `Shrink to a common ball $B_r(x_*)` | `Shrink to a common ball $B_\rho(x_*)` |
    | `\le\tfrac12Lr^2\tau^2.` | `\le\tfrac12L\rho^2\tau^2.` |

  - **(d) `t`: level and curvature.**
    - In Theorem 8, hypothesis 1 uses `t` for a level (`local.tex:218`); the proof uses
      t = yᵀs (lines 255, 265).
    - Lemma 7 has the same double use: the curvature in its statement (`:27`) and in the
      proof (`:138-140, 207, 220-230`), but the level in "Corner motion" and (38)
      (`:43-79`).
    - Optional fix for the theorem only, below. No change is proposed for the appendix:
      renaming the level there would touch about 15 places in two files, and the two
      meanings never meet in one formula.

    | old (×1, `local.tex`) | new |
    |---|---|
    | `For every $F_*<t\le b$, the boundary of $\{F\le t\}$` | `For every $F_*<c\le b$, the boundary of $\{F\le c\}$` |

  - **(e) `j`: corner index and branch index.** `j` indexes corners (p_j, v_j, χ_j;
    `planar_geometry.tex:43-94, 157`). In the secant paragraph it indexes branches
    (`:210-220`); the two-branch chart's branches are otherwise f₁, f₂. Optional fix:

    | old (×1 each, `planar_geometry.tex`) | new |
    |---|---|
    | `For different endpoint branches $i,j$ in a two-branch chart` | `For different endpoint branches $i,k$ in a two-branch chart` |
    | `(\nabla f_j(p)-\nabla f_i(p))^Tw(p)=0` | `(\nabla f_k(p)-\nabla f_i(p))^Tw(p)=0` |
    | `Put $r=\nabla f_j(z)-\nabla f_j(x)$,` | `Put $r=\nabla f_k(z)-\nabla f_k(x)$,` |
    | `\nabla f_j(x)^Ts=t-d-r^Ts` | `\nabla f_k(x)^Ts=t-d-r^Ts` |

  - **(f) `λ` used before it is defined.** In `local.tex:205`, "the transport factor
    $|\log\lambda|\le C d$" uses λ before it is defined. It is defined at line 256 and in
    Lemma 7, item 3. Earlier in this section, λ was the lasso weight (lines 116-135).
    The strings contain `|`, so they are given as blocks.

    old (×1, `local.tex`):
    ```
    $2d$, giving the transport factor $|\log\lambda|\le C d$.
    ```
    new:
    ```
    $2d$, giving $|\log\lambda|\le C d$ for the transport factor $\lambda$ in $w(z)=\lambda w(x)+\beta s$.
    ```

- **Register items:** A/local/proof/002 (r), A/local/proof/005 (t), A/local/prose/032 (λ),
  A/local/theorem/art:planar-cluster (t), A/planar_geometry/proof/001 (e, θ, j, t),
  A/planar_geometry/disp/009, A/planar_geometry/disp/011 and A/planar_geometry/disp/014 (e),
  A/planar_geometry/lemma/art:planar-field (θ, t).

### R-D-4. Bad line breaks inside short inline formulas

- **Where:**
  - p. 20, Theorem 8 (`local.tex:213`), and p. 21, Corollary 7 (`local.tex:302`): the line
    breaks after "→" in "Let F : ℝ² →⏎ℝ be finite and convex".
  - The same slip recurs on p. 13, Theorem 5 (`sections/global.tex:131`, "Let F : ℝⁿ
    →⏎ℝ").
  - p. 38 (`planar_geometry.tex:165-166`): "… and φ′(0) =⏎−d." The line breaks after "=",
    so "−d." starts a line.
- **Category:** typesetting. **Severity:** cosmetic.
- **Fix:** keep the formulas unbreakable. After the rebuild, check that the first lines of
  Theorem 8 and Corollary 7 are not underfull.

  | file | old (×1 each) | new |
  |---|---|---|
  | `local.tex` | `Let $F:\R^2\to\R$ be finite and convex, attain` | `Let \mbox{$F:\R^2\to\R$} be finite and convex, attain` |
  | `local.tex` | `Let $F:\R^2\to\R$ be finite and convex with a unique minimizer` | `Let \mbox{$F:\R^2\to\R$} be finite and convex with a unique minimizer` |
  | `global.tex` | `Let $F:\R^n\to\R$ be finite and convex, and suppose` | `Let \mbox{$F:\R^n\to\R$} be finite and convex, and suppose` |
  | `planar_geometry.tex` | `$\varphi'(0)=-d$.` | `\mbox{$\varphi'(0)=-d$}.` |

- **Observations, no defect and no warning:**
  - **p. 19.** The display defining 𝒞_aff has about twice the normal display skips: the
    page is flush-bottom and Theorem 8 moved to p. 20.
  - **p. 20.** The one-line display for E_{k+1} (`local.tex:262-267`) runs exactly from
    margin to margin with compressed operator spacing. If wanted, split it:

    old (×1):
    ```
     E_{k+1}=⏎ \lambda_k^2\left(E_k-\frac{(g_k^Tw(x_k))^2}{q_k}\right)⏎       +\frac{(y_k^Tw(x_{k+1}))^2}{t_k}⏎ \le(1+Ld_k)(E_k-m/q_k)+C.
    ```
    new:
    ```
     \begin{aligned}⏎ E_{k+1}&=⏎ \lambda_k^2\left(E_k-\frac{(g_k^Tw(x_k))^2}{q_k}\right)⏎       +\frac{(y_k^Tw(x_{k+1}))^2}{t_k}\\⏎ &\le(1+Ld_k)(E_k-m/q_k)+C.⏎ \end{aligned}
    ```
- **Register items:** A/local/theorem/art:planar-cluster, A/local/corollary/art:planar-max,
  A/local/disp/009 (optional display split), A/planar_geometry/proof/001 (lines 165-166,
  right after A/planar_geometry/disp/012). Elsewhere: A/global/theorem/art:centered.

### R-D-5. A tautological sentence in the polyhedral paragraph

- **Where:** `sections/local.tex:39-40` (p. 16).
- **Quoted:** "After removing the finitely many cells that miss $x_*$, every remaining cell
  contains $x_*$."
- **Category:** language. **Severity:** cosmetic.
- **Explanation:** Taken literally, this is a tautology; the register notes the same
  (A/local/prose/005). The intended content, used in the proof (lines 49-50), is that near
  x_* only cells containing x_* occur, because the finitely many closed cells that miss
  x_* avoid a ball around it.
- **Fix** (`sections/local.tex`):

  | old (×1) | new |
  |---|---|
  | `After removing the finitely many cells that miss $x_*$, every⏎remaining cell contains $x_*$.` | `Near $x_*$ only cells containing $x_*$ occur: the finitely many⏎closed cells that miss $x_*$ avoid a ball around it.` |

- **Register item:** A/local/prose/005.

### R-D-6. "The numerator" and "the quotient" have no antecedent in the transport estimate

- **Where:** `appendices/planar_geometry.tex:153-156` (p. 38).
- **Quoted:** "The numerator has magnitude at most a constant times $|s_n|\norm{s}$. Since
  $|D|\ge\kappa\norm{s}$ and $\varphi'=\norm{\nabla F}\,s_n$, the quotient is bounded by a
  constant times $|\varphi'|$."
- **Category:** language (small expository gap). **Severity:** cosmetic.
- **Explanation:** The text never says that the derivative of D(θ) = det(s, w(q(θ))) at a
  smooth point is D′(θ) = det(s, Dw s). Nor does it say that the quotient meant is
  D′/D = H′. H is introduced only three lines later. The reader must supply both.
- **Fix** (`appendices/planar_geometry.tex`; given as blocks because the strings contain
  `|`):

  old (×1):
  ```
  The numerator has magnitude at most a constant times $|s_n|\norm{s}$.
  ```
  new:
  ```
  Since $D'(\theta)=\det(s,Dw\,s)$ there, the numerator of $D'/D$ has magnitude at most a constant times $|s_n|\norm{s}$.
  ```

- **Register items:** A/planar_geometry/disp/011, A/planar_geometry/disp/012.

### R-D-7. "The global theorem" does not say which theorem

- **Where:** `sections/local.tex:3` (p. 16).
- **Quoted:** "The global theorem requires the initial sublevel to lie in the region where
  its representation is valid."
- **Category:** reference. **Severity:** cosmetic.
- **Explanation:** Section 4 has two global theorems (Theorems 5 and 6) and three
  corollaries. The sentence means Theorem 5 (`art:centered`), the only one with a
  representation region.
- **Fix** (`sections/local.tex`):

  | old (×1) | new |
  |---|---|
  | `The global theorem requires` | `Theorem~\ref{art:centered} requires` |

- **Register item:** A/local/prose/001.

## Checks without findings (recomputed)

### Section 5.1

- **Lemma 3.**
  - δ > 0 holds by continuity, compactness of the sphere and uniqueness.
  - The radial bound: with y = x_* + r(x − x_*)/‖x − x_*‖, convexity gives
    F(y) − F_* ≤ (r/‖x − x_*‖)(F(x) − F_*).
  - Coercivity gives compact sublevels.
  - ε = δ/2 gives a sublevel inside the open ball.
  - Armijo traps the run.
- **Theorem 7's proof.**
  - The ball avoids the discarded cells and lies in U ∩ ⋂V_i.
  - Convexity of P_i keeps the inward segment in U ∩ P_i.
  - The right derivatives at τ = 0 agree.
  - The Taylor bound with constant L/2 holds.
  - The lower bound follows from convexity of F.
  - The inward condition holds with M = Lr², θ = 1/2.
  - Corollary 1's hypotheses are satisfied.
- **Corollaries 4 and 5.**
  - The quadratic pieces are C^{1,1} extensions; the loss sum keeps them.
  - Corollary 5's shrink to an open convex ball, then Lemma 3, then Theorem 5 is valid.
- **Lasso decomposition (17).** |x_i| = σ_i x_i on the neighborhood, and
  |x_i| = |(x − x_*)_i| for i ∈ I_0. The residual-norm decomposition is valid.

### Section 5.2

- **Least-norm point.** a ⊥ (direction space) gives gᵀa = ‖a‖², so gᵀ(−a/‖a‖²) = −1.
- **Corners.**
  - The corner velocity pairing 1 follows by differentiating f_i(p_j(t)) = t.
  - Disjoint normal arcs: a common normal exposes the segment [p, q] in the boundary.
  - Over a positive level, cone(∂F) = N_{{F≤ℓ}}.
- **Field identities.**
  - w = (nᵀv)n + (Tᵀv)T = v.
  - ∂_θ(hn + h_θT) = (h + h_θθ)T.
  - Dw maps the tangent to a multiple of T.
- **Variation of F along the chord.** ∫|φ′| ≤ ∫(φ′ + 2d) = 2d − Δ ≤ 2d.

### Theorem 8 and Corollaries 6 and 7

- **Theorem 8.**
  - Steps tend to zero: the two-sided bound on the chord gives F = ℓ on [x, z].
  - Interior level points are impossible: write p as a convex combination of a minimizer
    and a point beyond p.
  - The hypotheses of Lemma 7 hold for C = Γ: ℓ ≤ b, strict contour at ℓ, structure off
    𝒞_aff.
  - The energy identity is exact: B_{k+1} = B̂_k + yyᵀ/t and B̂_k s_k = 0.
  - The inequality holds: B̂_k ⪰ 0 and λ² ≤ 1 + Ld (see R-D-1).
  - Normalization as in Theorem 3 gives Σ q_k⁻¹ ≤ P̄(E_J + C(N − J))/m, which contradicts
    Theorem 2: gradients are bounded and d_k → 0.
- **Corollary 6.** The cluster point lies in K ∩ 𝒞_aff ⊆ argmin F, so the limit value is
  F_*.
- **Corollary 7.**
  - The normal equations give the unique balance λ(p), continuous and positive near x_*.
  - ∂(max) = conv(active gradients), by the support and separation arguments given.
  - An affine balance extended by zeros equals λ(p), so it is convex and p is a minimizer.
  - At most two branches are active off 𝒞_aff.
  - Two active branches: distinct gradients, and linear dependence would put 0 on their
    affine line.
  - Strong convexity excludes boundary segments: the midpoint value is < t, so the
    midpoint is interior.

### Theorem 9 (exact arithmetic)

- **Hessians.** diag(2,1), diag(1,3), diag(3,2) all lie between I and 3I.
  (f₀ + f₁ + f₂)/3 = u² + v².
- **Determinant and coefficients.**
  - det[(∇f_i, 1)] = 3 + 3v − 3uv = 3(1 + v − uv).
  - Cramer's rule gives exactly Dλ₀ = 1 − 4u + 3v − 7uv, Dλ₁ = 1 + 2u − 3v − uv and
    Dλ₂ = 1 + 2u + 3v + 5uv. They sum to D.
- **Box bounds** (|u|, |v| ≤ 1/10, bilinear, so minima at the vertices).
  - D ≥ 267/100 is sharp.
  - The numerators have minima 37/100, 51/100 and 55/100. The printed 23/100, 49/100 and
    45/100 are valid termwise lower bounds, not sharp but true.
  - {F ≤ 1/100} ⊂ disk of radius 1/10 ⊂ box.
- **Tie.** The tie f₀ = f₁ is v + v² = u + u²/2, so v = (−1 + √(1 + 4u + 2u²))/2
  = u − u²/2 + u³ + O(u⁴). At the tie f₂ < f₀.
- **Radial jump and the pair.**
  - (∇f₀ − ∇f₁)ᵀ(u, v) = u + u² − v − 2v² = u²/2 − v² on the tie, < 0 for small u.
  - d = 2e(1 + 3v + 3e) and t = 2e(1 + 2v + 4e) identically.
  - Δ − [e(1 + 4v) + e²] = (f₁ − f₀)(u, v), which is 0 on the tie.
  - yᵀz at e = 0 equals u²/2 − v² modulo the tie.
- **Eligibility, checked numerically** for u ∈ {0.05, 0.01, 0.001} and small e: Δ/d ≈ 0.5,
  t/d ≈ 1, eligible for (1/4, 1/2), and N²/t grows like 1/e.

### Lemma 7

- **Construction.**
  - The inverse function theorem gives the C² corner curve; there is one level-ℓ corner
    per chart and finitely many in all.
  - Normal arcs have width < π, satisfy nᵀv_j > 0, and are disjoint.
  - h is a convex combination of positive quantities; (40) holds near each curve.
  - Pairing at a smooth point: ‖∇F‖h > 0. At a corner: 1 for all subgradients.
  - The gradient bound comes from ‖g‖‖x − x_*‖ ≥ F(x) − F_*.
- **Transversality.** The limit ŝ = −w(p)/‖w(p)‖ is forced by d > 0 and the pairing ≥ η.
  Then t/‖s‖ → 0, which contradicts weak Wolfe.
- **Transport.**
  - det(T, n) = −1, and det(s, Dw s) = s_n[(a − e)s_T + b s_n], verified symbolically.
  - |H′₊| ≤ A|φ′₊| ≤ A(φ′₊ + 2d), using φ′₊ ≥ −d.
  - The one-sided comparison lemma holds: its minimum is attained before 1.
  - λ = D(1)/D(0) by Cramer's rule in the basis (s, w(x)).
  - The chord bound for exp holds on [0, 1].
- **Secant correction.**
  - Same branch: the descent-lemma proof of ‖∇f(z) − ∇f(x)‖² ≤ 2M·Bregman is valid,
    the step stays within ‖z − x‖ of z, and Bregman ≤ t by the supporting inequality
    at z.
  - Crossing: the tie point from the IVT, |yᵀw(z)| ≤ A₁‖s‖,
    ‖s‖ ≤ A₂(2d + t + M‖s‖²) ≤ A₂(1 + 2/(1 − c₂))t + A₂M‖s‖², and t ≥ a₀‖s‖.
- **Fit with Section 5.** Lemma 7 delivers exactly what Theorem 8's proof uses: visibility
  m = η², secant C = C₀, the frame relation, and λ² ≤ 1 + Ld with L = e^{4A} − 1 (up to
  d ≤ 1, R-D-1). It also delivers what the summary at `local.tex:201-207` cites:
  transversality and |log λ| ≤ C₁d with C₁ = 2A.

### Statements against Lean

No printed statement in these files differs noticeably from its register reading. Two
readings are worth recording:

- Corollary 4: "has the local convergence property" is read for every open U ∋ x_*.
- Corollary 5: "a neighborhood" is read as open and convex. The proof shrinks to one.

## Coverage table

| Environment or proof | Snapshot lines | Result |
|---|---|---|
| Section opening (roadmap) | `local.tex:3-9` | R-D-7 |
| Lemma 3 `art:localization` | `local.tex:16-22` | read: no finding |
| Proof of Lemma 3 | `local.tex:23-36` | read: no finding |
| Paragraph before Theorem 7 | `local.tex:38-44` | R-D-5 |
| Theorem 7 `art:polyhedral` (statement in `statements/positive_partition.tex:1-18`) | input at `local.tex:46` | read: no finding |
| Proof of Theorem 7 | `local.tex:48-76` | R-D-3(c) |
| Corollary 4 `art:plq` | `local.tex:78-83` | read: no finding |
| Proof of Corollary 4 | `local.tex:84-89` | read: no finding |
| Remarks on penalties | `local.tex:91-99` | read: no finding |
| Corollary 5 `art:local-centered` | `local.tex:101-108` | read: no finding |
| Proof of Corollary 5 | `local.tex:109-113` | read: no finding |
| Lasso decomposition, equation (17) `art:local-l1-decomposition`, residual norms | `local.tex:115-143` | read: no finding |
| Section 5.2 prose: 𝒞_aff, roles of the hypotheses, construction summary | `local.tex:147-210` | R-D-2, R-D-3(f) |
| Theorem 8 `art:planar-cluster` | `local.tex:212-227` | R-D-3(d), R-D-4 |
| Proof of Theorem 8 | `local.tex:228-272` | R-D-1; R-D-4 (display, optional) |
| Corollary 6 `art:planar-convergence` | `local.tex:274-279` | read: no finding |
| Proof of Corollary 6 | `local.tex:280-285` | read: no finding |
| Section 5.3 opening | `local.tex:294-299` | R-D-2 |
| Corollary 7 `art:planar-max` | `local.tex:301-320` | R-D-4 |
| Proof of Corollary 7 | `local.tex:321-359` | read: no finding |
| Theorem 9 `art:nonradial-example` | `local.tex:367-382` | read: no finding |
| Proof of Theorem 9 | `local.tex:383-433` | read: no finding; all numbers recomputed |
| Closing remarks | `local.tex:435-440` | read: no finding |
| Appendix B opening | `planar_geometry.tex:3-6` | read: no finding |
| Lemma 7 `art:planar-field` | `planar_geometry.tex:8-38` | read: no finding; R-D-3(b),(d) notation |
| Proof of Lemma 7, corner motion, equation (37) | `planar_geometry.tex:40-56` | read: no finding |
| Proof of Lemma 7, joining, equations (38) to (41), Dw | `planar_geometry.tex:58-123` | read: no finding |
| Proof of Lemma 7, transversality | `planar_geometry.tex:125-141` | read: no finding |
| Proof of Lemma 7, transport, equation (42) | `planar_geometry.tex:143-189` | R-D-3(a),(b), R-D-4, R-D-6 |
| Proof of Lemma 7, secant correction | `planar_geometry.tex:191-233` | R-D-3(e) |
