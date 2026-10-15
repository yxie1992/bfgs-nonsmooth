# Line-by-line reading, reader A

## Header

- **Snapshot read:** `$S/step2/snapshot/paper/` (identical to commit c8db802), with
  `S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode`. All line
  numbers below are snapshot line numbers.
- **My files:** `master.tex` (title, abstract); `sections/introduction.tex`;
  `statements/negative_lower.tex`, `statements/negative_upper.tex`,
  `statements/positive_partition.tex`; `sections/geometry.tex` (with
  `figures/gradient_geometry.tex`, which it inputs); `sections/verification.tex`;
  `bibliography.tex`; `preprint_references.tex`.
  The three statements are not input by the introduction: `positive_partition` is
  input at `local.tex:46` (Theorem 7), `negative_upper` at `failure.tex:49`
  (Theorem 10), `negative_lower` at `failure.tex:456` (Theorem 11, inside a
  minipage). They are therefore the theorems themselves; I compared them with
  their proofs (`local.tex:48-76`; `failure.tex:356-425` with Lemma
  `art:seed_cycle`, Table `art:trial_table`; Appendix D) and with every summary of
  them (abstract, introduction, Section 2, Table `art:regularity-map`, Section 7).
- **Also read** (for definitions, the results my files summarize, and references):
  `energy.tex`, `global.tex`, `local.tex`, `failure.tex`, all four appendices; the
  seven registers `A_master`, `A_introduction`, `A_negative_lower`,
  `A_negative_upper`, `A_positive_partition`, `A_geometry`, `A_verification`;
  companion `master.tex`, `research_story.tex`, `current_verification.tex`,
  `correspondence.tex`; read only in the live repository:
  `editorial/LITERATURE_LEDGER.json`, `editorial/JOURNAL_FIT.md`,
  `editorial/AI_AND_AUTHOR_ACTIONS.md`, `bfgs_lean_article/AXIOM_AUDIT.json`,
  `bfgs_lean_article/KERNEL_REPLAY.json`, `TODO_*.md`, `AGENTS.md`, `HANDOFF.md`,
  `BfgsArticle/Coverage/Article/Geometry.lean` (one declaration).
- **PDF pages rendered** (`$S/baseline/paper.pdf`, 110 dpi, images in
  `$S/read_A/img/`): 1, 2, 3, 4, 5, 6 (title, abstract, Sections 1–2), 17
  (Theorem 7), 24, 25 (Theorem 10), 32 (Theorem 11), 33, 34 (Section 7), 48, 49
  (references); page 4 figure also at 400 dpi. LaTeX log `$S/baseline/paper.log`
  checked for boxes in my files.
- **Time spent:** about 30 minutes (03:10–03:40, 15 October 2026).
- **Summary:** 18 findings: **0 major, 9 minor, 9 cosmetic**. The mathematics
  printed in my files (equation (1), the pairings, the affine/convex balance facts,
  equation (35), the active-gradient test) is correct, and the three theorem
  statements agree with their proofs. The minor findings are summary sentences that
  leave out or garble a hypothesis or a location (R-A-1 to R-A-3, R-A-5), references
  and notation (R-A-4, R-A-6), out-of-date verification and AI-use statements
  (R-A-7, R-A-8), and one figure (R-A-9).

## Findings

### R-A-1 — "at the accumulation point" in the abstract places the irregularity at the wrong point

- **Where:** `master.tex:51-54`.
- **Text:** "One construction is a maximum of four globally convex $C^{2,1}$
  branches; another retains uniform strong convexity with $C^{1,1}$ branches that
  lose second differentiability at the accumulation point."
- **Category:** language (wrong word). **Severity:** minor. It is the same sentence
  as M8 but a separate slip.
- **Explanation:** In optimization, "accumulation point" usually means a cluster
  point of the iterates. The preceding sentence has just said that the runs
  "converge to nonstationary points". Each failing run converges to
  $\bar x_\ell\ne0$, and there every branch is smooth: near
  $\bar x_\ell=a_\ell c_*$ each scalar argument $q_i^Tx$ lies in the affine region
  of $\psi_{b_i}$ (`lower_curvature.tex:242-243, 288-291`), so $f_0,f_1,f_2$ are
  quadratics there, and $f_3$ is a quadratic everywhere. The branches fail to be
  twice differentiable only at $0$, the minimizer, where the bad centers
  accumulate. Theorem 11 says "at zero" (`negative_lower.tex:21-22`) and the
  introduction says "at the minimizer" (`introduction.tex:78-79`). Read with the
  usual meaning, the abstract puts the loss of regularity at the limit of the run,
  where the failure mechanism acts. That is false.
- **Fix** (together with M8):
  - In `master.tex`, `differentiability at the accumulation point.` (occurs once)
    becomes `differentiability at the minimizer.`
  - With M8 the sentence then reads: "…another retains uniform strong convexity
    with $C^{1,1}$ branches, three of which lose second differentiability at the
    minimizer."
- **Other locations:**
  - `companion/research_story.tex:52-53` repeats the abstract's sentence (it is
    already listed under M8): `the accumulation point. These are two distinct
    exclusions` (occurs once) becomes `the minimizer. These are two distinct
    exclusions`.
  - The companion texts listed under M8 (`13_L.tex:3`, `01_I.tex:103`) use the same
    phrase.
  - In Section 6 and Appendix D (`failure.tex:465, 506, 513`;
    `lower_curvature.tex:13`) the phrase comes right after the centers
    $\bar x_\ell\to x_*$ are described and reads correctly. Harmonizing them is
    optional.
- **Register:** `A/master/prose/009`.

### R-A-2 — Table 1 caption: global convergence inferred from compact sublevels alone (another location of M7)

- **Where:** `geometry.tex:84-85`.
- **Text:** "The benchmark $u^2+|v|$ has compact sublevels everywhere, so the first
  row gives global convergence."
- **Category:** hypothesis. **Severity:** minor.
- **Explanation:** Row 1 (Theorem 5) needs the compact initial sublevel to lie in
  the region where the centered representation holds. The caption infers global
  convergence from compactness alone, which is exactly the inference M7 records as
  false in general: the coercive cap $\overline G$ of Corollary
  `art:failure_polyhedral` has compact sublevels and a centered representation on a
  ball around its minimizer, yet its run fails. For $u^2+|v|$ the representation
  holds on all of $\R^2$ (proof of Corollary `art:mixed-benchmark`, $U=\R^2$), so
  the conclusion is true; only the stated reason is incomplete. The Lean item
  `Geometry.benchmark_compact_sublevels_global` proves the two facts, not the "so".
- **Fix:** in `geometry.tex`, `compact sublevels everywhere, so the first row gives
  global convergence.` (occurs once) becomes `compact sublevels and a centered
  representation on all of $\R^2$, so the first row gives global convergence.`
- **Register:** `A/geometry/prose/031`.

### R-A-3 — Table 1, row 3: "($\lambda>0$)" suggests that $\lambda>0$ is enough

- **Where:** `geometry.tex:75-77`.
- **Text:** "Finite polyhedral smooth-piece partition, including squared loss plus
  $\lambda\norm{x}_1$ ($\lambda>0$), Theorem~\ref{art:polyhedral} & Common low
  sublevel near the unique minimizer".
- **Category:** hypothesis (summary). **Severity:** minor.
- **Explanation:** For the $\ell_1$-regularized least-squares objective,
  uniqueness of the minimizer is an extra hypothesis (Corollary `art:plq`;
  `local.tex:135`: "Uniqueness is a hypothesis here; $\lambda>0$ alone does not
  supply it"). Counterexample: $n=2$, $A=(1\ 1)$, $b=1$, $\lambda=1/2$. Then
  $F(x)=\tfrac12(x_1+x_2-1)^2+\tfrac12(|x_1|+|x_2|)\ge3/8$, with equality on the
  whole segment $\{x\ge0,\ x_1+x_2=1/2\}$ (checked exactly). The cell names
  $\lambda>0$ as the only condition; uniqueness appears only through the definite
  article in the next column. The register reads it that way (`prose/029`), but
  the parenthesis invites the wrong reading that `local.tex:135` warns against.
- **Fix:** in `geometry.tex`,
  `$\lambda\norm{x}_1$ ($\lambda>0$), Theorem~\ref{art:polyhedral}` (occurs once)
  becomes `$\lambda\norm{x}_1$ ($\lambda>0$, unique minimizer),
  Theorem~\ref{art:polyhedral}`.
- **Register:** `A/geometry/prose/029`.

### R-A-4 — Section 7 uses "whitening" and the letter $A$ before they are defined

- **Where:** `verification.tex:24-30`.
- **Text:** "…gives the same pattern before whitening: … After the one fixed change
  $x=Az$, the gradients are $0,0,0,A^Te_2$, with $A^Te_2\ne0$. … (or
  $\lambda_3A^Te_2\ne0$ after whitening)."
- **Category:** notation. **Severity:** minor.
- **Explanation:** "Whitening" occurs nowhere else in the article. The change
  $x=Az$ with $A=(H_0^{\rm seed})^{1/2}$ is defined only in Appendix D
  (`lower_curvature.tex:313-325`), which comes after Section 7. Section 6 mentions
  only "one fixed affine change" (`failure.tex:503-504`). So in Section 7 the letter
  $A$ has no antecedent, and earlier sections use it for other objects: the data
  matrix of the $\ell_1$ example (`local.tex:116`) and $A(x)$ in the proof of
  Corollary `art:planar-max` (`local.tex:322`). The mathematics is right:
  $A^Te_2\ne0$ because $A$ is invertible.
- **Fix:** three replacements in `verification.tex`, each old string occurring once:
  - `Equation~\eqref{art:lower_objective} gives the same pattern before whitening:`
    becomes `Equation~\eqref{art:lower_objective} gives the same pattern before the
    fixed change of coordinates of Appendix~\ref{art:lower_curvature}:`
  - `After the one fixed change $x=Az$, the gradients are $0,0,0,A^Te_2$,` becomes
    `After that change, $x=Az$ with $A=(H_0^{\rm seed})^{1/2}$, the gradients are
    $0,0,0,A^Te_2$,`
  - `$\lambda_3A^Te_2\ne0$ after whitening)` becomes `$\lambda_3A^Te_2\ne0$ after
    that change)`
- **Register:** `A/verification/prose/012`, `013`, `015`.

### R-A-5 — The list of remaining questions: what "broader" means, and the constant range of the examples

- **Where:** `verification.tex:53-57`.
- **Text:** "The broader local question for finitely many uniformly strongly convex
  $C^2$ branches remains open here. The examples concern the specified weak-Wolfe
  implementation and exceptional deterministic starts; …"
- **Category:** language. **Severity:** minor.
- **Explanation:**
  - (a) "Broader" has no referent. Part of this class is settled by the article.
    For a planar maximum of uniformly strongly convex $C^2$ branches whose active
    gradients at $x_*$ are affinely independent with positive weights, Corollary
    `art:planar-max` gives a local basin: its last assertion turns the common
    positive lower Hessian bound into the strict-contour hypothesis, and strong
    convexity gives the unique minimizer. What is open is the degenerate planar
    case and dimension $n\ge3$. The examples' active gradients $0,0,0,e_2$
    (lines 21-31) are degenerate in the same way, though neither example has
    strongly convex $C^2$ branches.
  - (b) Both failure theorems are proved only for $0<c_1\le1/3$, $c_1<c_2<1$.
    Section 7's description of the examples' scope names the implementation and
    the starts but not the constants. Whether failures exist for $c_1>1/3$ is not
    addressed anywhere. M11 shows that the certified tree itself breaks for
    $c_1>r_2\approx0.3752$.
- **Fix:** three replacements in `verification.tex`, each old string occurring once:
  - `The broader local question for finitely` becomes
    `The local question for finitely`
  - `many uniformly strongly convex $C^2$ branches remains open here.` becomes
    `many uniformly strongly convex $C^2$ branches remains open here outside the
    nondegenerate planar case of Corollary~\ref{art:planar-max}.`
  - `The examples concern the specified weak-Wolfe implementation and exceptional`
    becomes `The examples concern the specified weak-Wolfe implementation with
    $0<c_1\le1/3$ and exceptional`
- **Register:** `A/verification/prose/025` (OPEN) and `026`.

### R-A-6 — "The following paragraph" reads as the article's next paragraph

- **Where:** `introduction.tex:36-38`.
- **Text:** "The following paragraph explicitly leaves convergence of every BFGS
  sequence to $(0,0)$ open~\cite[Corollary~4.4 and following discussion]{GL18}."
- **Category:** reference. **Severity:** minor.
- **Explanation:** The article's own next paragraph (lines 44-53) is about
  Xie–Wächter and Gebken. The sentence means the paragraph of [GL18] that follows
  its Corollary 4.4, which only the citation's locator reveals.
- **Fix:** in `introduction.tex`, `The following paragraph explicitly leaves
  convergence of every BFGS sequence` (occurs once) becomes `The paragraph after
  that corollary explicitly leaves convergence of every BFGS sequence`.
- **Register:** `A/introduction/prose/009`.

### R-A-7 — The verification paragraph does not match the current verification record

- **Where:** `verification.tex:59-63`; also `introduction.tex:124-126`.
- **Text:** "The complete companion supplies pinned Lean sources, exact theorem
  contracts and their correspondence to the manuscripts, compiler and dependency
  audits, and versioned source/build records."
- **Category:** reference (statement about the records). **Severity:** minor.
- **The current facts:**
  - Axiom audit: PASS, 5403 declarations at `9f03d7c`, including every
    coverage-register name (`bfgs_lean_article/AXIOM_AUDIT.json`, 15 October).
  - Kernel replay: PASS; lean4checker v4.19.0 replayed 783 modules
    (`KERNEL_REPLAY.json`).
  - Literal Lean coverage of every article claim, in
    `editorial/lean_coverage/register/`.
- **What the companion and the records say:**
  - The companion reports the axiom audit with the stale count "All 2026 Lean
    names" (`companion/current_verification.tex:8`; already W30).
  - Neither the companion nor the article mentions the kernel replay or the
    coverage registers (also noted in the register).
  - The "versioned source/build records" (`release/`, 13 September) predate the
    October revisions ("Release receipts are now stale", `TODO_LEAN_REVIEW.md`).
  - The correspondence's proof locations for `lower_curvature.tex` are stale.
- **Consequence:** The sentence is not false, but it describes the 13 September
  record. It will be accurate only after the planned release run and a refresh of
  the companion, and it leaves out the two strongest current checks.
- **Fix:**
  - (1) Refresh the release records and `current_verification.tex`, as already
    planned.
  - (2) In `verification.tex`, `compiler and dependency audits,` (occurs once)
    becomes `compiler, axiom and kernel-replay audits,`. Add a matching companion
    sentence in `current_verification.tex`, e.g. "lean4checker v4.19.0 replayed
    every declaration of the 783 project modules through the Lean kernel; the run
    passed (\path{bfgs_lean_article/KERNEL_REPLAY.json})."
  - (3) Optional, once M7–M11 are applied: a sentence that every claim of the
    article is classified in the coverage registers and paired with its Lean proof.
- **Register:** `A/verification/prose/027`, `A/introduction/prose/049`.

### R-A-8 — The AI-use statement points to a companion disclosure that leaves out the October work

- **Where:** `verification.tex:67-71`.
- **Text:** "Large language models assisted theorem development, proof
  reconstruction, formalization, literature searches, software and writing. The
  companion documents this substantive research assistance and the automated
  author-side reviews."
- **Category:** reference (statement about the records). **Severity:** minor (it
  concerns a disclosure that MP requires, `editorial/JOURNAL_FIT.md`).
- **Explanation:** The companion's disclosure (`companion/master.tex:63-69`) names
  only "OpenAI ChatGPT/Codex systems"; so does
  `editorial/AI_AND_AUTHOR_ACTIONS.md:3,9`. Since 13 October the Lean review, the
  statement change M6 (Theorem 11 for every admissible pair, with new Lean
  modules), the Lean coverage of every claim and the manuscript reviews were done
  by Claude in OpenCode (`AGENTS.md:5-6`, `TODO_LEAN_REVIEW.md:3`,
  `TODO_MANUSCRIPT_REVIEW.md:3`, `HANDOFF.md:3`). The article's second sentence
  holds only once the companion covers this.
- **Fix:** in `companion/master.tex` (written by hand), `OpenAI ChatGPT/Codex
  systems assisted mathematical development and correction,` (occurs once) becomes
  `OpenAI ChatGPT/Codex systems and, from October 2026, Anthropic Claude (in
  OpenCode) assisted mathematical development and correction,`. Make the same
  addition in `editorial/AI_AND_AUTHOR_ACTIONS.md`.
- **Register:** `A/verification/prose/030`.

### R-A-9 — Figure 1(b) does not visibly show that zero lies outside the convex hull; one arrow in the caption is misdescribed

- **Where:** `geometry.tex:20-30`; `figures/gradient_geometry.tex:15-22`; page 4.
- **Text:** "Its convex hull excludes zero … Arrows indicate gradients, not BFGS
  steps."
- **Category:** typesetting (figure). **Severity:** minor.
- **Explanation:**
  - The distance from $0$ to $\mathrm{conv}\{g_0,g_1,g_2\}$ is
    $\|\bar g\|=1/\sqrt{257}\approx0.062$. The nearest point
    $\bar g=(1,-16)/257$ lies on the edge $[g_1,g_0]$ (`lower_curvature.tex:31-35`),
    and at abscissa $0$ that edge passes through $-1/16$. At the figure's scale of
    1.5 cm per unit this is a gap of 0.94 mm.
  - The open marker at $0$ has radius 1.7 pt (0.60 mm) and the edge is drawn
    "thick". The visible gap is therefore about 0.2 mm, and on the rendered page
    (also at 400 dpi) the marker touches the edge. The panel thus seems to put
    zero on the boundary of the hull, the opposite of what the caption states.
  - The caption's last sentence calls all arrows gradients, but the dashed
    "descent" arrow of the left panel is a descent direction.
- **Fix:**
  - In `geometry.tex`, `definition uses the isolated root. Arrows indicate
    gradients, not BFGS steps.}` (occurs once) becomes `definition uses the
    isolated root. Zero lies just above the edge $[g_1,g_0]$, at distance
    $1/\sqrt{257}$ from the hull. Solid arrows indicate gradients and the dashed
    arrow a common descent direction; none is a BFGS step.}`
  - Optionally, in `figures/gradient_geometry.tex`, `\fill[white] (0,0) circle
    (1.7pt);\draw (0,0) circle (1.7pt);` (occurs once) becomes `\fill[white] (0,0)
    circle (1pt);\draw (0,0) circle (1pt);`
- **Register:** `A/geometry/figure/art:gradient-geometry`, `A/geometry/prose/010`,
  `012`.

### R-A-10 — Figure 1 (and Table 3) are never cited in the text

- **Where:** `geometry.tex:9, 32`; other location `failure.tex:461-482`.
- **Category:** reference. **Severity:** cosmetic.
- **Explanation:** `\ref{art:gradient-geometry}` occurs nowhere. Line 32 says
  "The right panel" without naming the figure, and the left panel is never
  mentioned in the text. Table `art:regularity-map` (Table 3) is likewise never
  referenced. Springer journals expect every figure and table to be cited.
- **Fix:**
  - In `geometry.tex`, `with both gradients. The inward radial model` (occurs once)
    becomes `with both gradients (Figure~\ref{art:gradient-geometry}, left). The
    inward radial model`.
  - In `geometry.tex`, `The right panel asks a different question` (occurs once)
    becomes `The right panel of Figure~\ref{art:gradient-geometry} asks a different
    question`.
  - In `failure.tex`, `The two constructions separate upper branch regularity from
    positive lower` (occurs once) becomes `The two constructions
    (Table~\ref{art:regularity-map}) separate upper branch regularity from positive
    lower`.
- **Register:** `A/geometry/figure/art:gradient-geometry`;
  `A/failure/table/art:regularity-map`.

### R-A-11 — Section 7 wording: "at every scale" and "certified perturbed orbit"

- **Where:** `verification.tex:14-15`, `43`.
- **Category:** language. **Severity:** cosmetic.
- **Explanation:**
  - The bad centers occur at the scales $a_\ell=16^{-\ell}$ (Theorem 10) and
    $a_\ell=128^{-\ell}$ (Theorem 11). That is infinitely many shrinking scales, as
    `geometry.tex:98` says, not every scale.
  - In this article "certified" means a finite rational certificate (the seed and
    the trial tree). The perturbed orbit comes from the stable-manifold theorem,
    and the article stresses that no rounded state is asserted to lie on that
    manifold (`failure.tex:495-496`, caption of Figure 2).
- **Fix:** two replacements in `verification.tex`, each old string occurring once:
  - `at every scale around the same minimizer.` becomes `at infinitely many
    shrinking scales around the same minimizer.`
  - `Along the certified perturbed orbit` becomes `Along the perturbed orbit of
    Proposition~\ref{art:quadratic_failure}`
- **Register:** `A/verification/prose/008`, `019`.

### R-A-12 — The number of equation (1) is pushed onto its own line

- **Where:** `geometry.tex:9-13`; page 4.
- **Category:** typesetting. **Severity:** cosmetic.
- **Explanation:** The display together with "$\qquad(v\ne0,\ 0\le\tau\le1)$" is
  too wide, so the tag "(1)" sits alone on the next line.
- **Fix:** two replacements in `geometry.tex`, each old string occurring once:
  - `The inward radial model also has a small error:` becomes `The inward radial
    model also has a small error: for $v\ne0$ and $0\le\tau\le1$,`
  - `=\tau^2u^2\qquad(v\ne0,\ 0\le\tau\le1).` becomes `=\tau^2u^2.`
- **Register:** `A/geometry/disp/001`.

### R-A-13 — Table 1: layout, and two undefined terms

- **Where:** `geometry.tex:62-88`; page 5.
- **Category:** typesetting and notation. **Severity:** cosmetic.
- **Explanation:**
  - The justified narrow `p` columns give underfull boxes (`paper.log:1041-1061`,
    badness up to 10000 at lines 70-71) and visibly stretched spacing ("Theo- rem
    5", "Optimal values; unique minimizer gives whole-").
  - Rows 2 and 3 run together.
  - "Structural region" occurs only here; Theorem 5's set is the open convex $U$
    on which the representation holds.
  - "Accepted runs" is undefined; the article's term is admissible runs.
- **Fix:** replacements in `geometry.tex`, each old string occurring once:
  - `\begin{tabular}{@{}p{.40\textwidth}p{.22\textwidth}p{.29\textwidth}@{}}`
    becomes `\begin{tabular}{@{}>{\raggedright\arraybackslash}p{.40\textwidth}>{\raggedright\arraybackslash}p{.22\textwidth}>{\raggedright\arraybackslash}p{.29\textwidth}@{}}`
    (the `array` package is loaded).
  - Append `\addlinespace` after each of `& Optimal values; unique minimizer gives
    whole-sequence convergence\\`, `& Whole sequence converges to zero\\` and
    `& Whole sequence converges to the minimizer\\` (`booktabs` is loaded).
  - `& Compact initial sublevel in the structural region` becomes `& Compact
    initial sublevel inside the region of the representation`.
  - `The results concern accepted runs, without a presumed matrix limit.}` becomes
    `The results concern admissible runs, without a presumed matrix limit.}`
- **Register:** `A/geometry/table/art:positive-outcomes`, `A/geometry/prose/027`,
  `032`.

### R-A-14 — The paragraph break in Theorem 11 is invisible

- **Where:** `negative_lower.tex:12-14`, set in a minipage at `failure.tex:455-457`;
  page 32.
- **Category:** typesetting. **Severity:** cosmetic.
- **Explanation:** A minipage sets `\parindent` to 0. The statement's second
  paragraph ("The objective can be a maximum …") therefore starts flush left with
  no space, as if it continued the first.
- **Fix:** in `failure.tex`, `\noindent\begin{minipage}{\textwidth}` (occurs once)
  becomes `\noindent\begin{minipage}{\textwidth}\setlength{\parindent}{15pt}`
  (`svjour3.cls:159` sets `\parindent` to 15pt).
- **Register:** `A/negative_lower/theorem/art:local-failure-lower`.

### R-A-15 — The reference list: order, a stray `\par`, date style

- **Where:** `bibliography.tex`; `introduction.tex:6`; pages 1, 48-49.
- **Category:** typesetting and bibliography style. **Severity:** cosmetic.
- **Explanation:**
  - (a) The list is neither alphabetical nor in order of first citation, so the
    first citation in the text prints as "[9,8,7]".
  - (b) The Powell entry contains `\par` (line 20), which breaks the entry after
    its title (page 48).
  - (c) Dates are styled inconsistently. Gebken has "(8 May 2026)" where every
    other entry has a year. Online-first dates are given for five entries (LO,
    Lewis–Zhang, Asl–Overton, Mascarenhas 2004, Bogosel) and not for the rest.
  - The bibliographic data agree with `LITERATURE_LEDGER.json` wherever the ledger
    records them (WW journal data, the JJM24AW DOI, Rump's Theorem 13.3). All 17
    entries are cited, and every `\cite` key exists.
- **Fix:**
  - In `bibliography.tex`, `minimization without exact line searches}.\par`
    (occurs once) becomes `minimization without exact line searches}.`
  - In `introduction.tex`, `\cite{FND_P76,FND_BN89,FND_N92}` (occurs once) becomes
    `\cite{FND_N92,FND_BN89,FND_P76}`, which prints [7,8,9].
  - In `bibliography.tex`, `Journal of Optimization Theory and Applications 209,
    article 57 (8 May 2026).` (occurs once) becomes `Journal of Optimization Theory
    and Applications 209, article 57 (2026); published online 8 May 2026.`
  - Optional: sort the list alphabetically: Asl, Banerjee, Bogosel, Byrd, Combettes,
    Gebken, Guo, Jin, Lewis–Overton, Lewis–Zhang, Mascarenhas 2004, Mascarenhas
    2007, Nocedal, Powell, Rump, Schöpfer, Wachsmuth. Then order the keys inside
    `introduction.tex:6` and `energy.tex:124` to match.
- **Register:** `A/introduction/prose/001` (citation site).

### R-A-16 — Preprint citations repeat the author's name; unused keys and stale comments

- **Where:** `introduction.tex:44-46, 65, 66-67`; `preprint_references.tex:21-27`.
- **Category:** bibliography style. **Severity:** cosmetic.
- **Explanation:**
  - `\preprintcite` prints the authors, so the text reads "Diao (Diao, 2026
    preprint, arXiv:2609.09686v1)" (page 3). It reads similarly for "Xie–Wächter's
    … (Xie and Wächter, …)" and "Lewis–Overton's … (Lewis and Overton, *Behavior
    of BFGS …*, 2008 manuscript)".
  - The formats differ: titles appear only for DY and NEG_LO08, initials only for
    WW22.
  - `preprint_references.tex` defines two keys that are never cited (LL18, JM25v2).
    Its comments refer to bibliography entries LL and FND_JM25 that are not in
    `bibliography.tex` (removed in the 12 September pruning, ledger
    `bibliography_pruning`). None of this shows in the PDF.
- **Fix:**
  - In `introduction.tex`, `Diao~\preprintcite{NEG_DIAO26}` (occurs once) becomes
    `Diao (2026 preprint, \href{https://arxiv.org/abs/2609.09686v1}{arXiv:2609.09686v1})`.
  - In `preprint_references.tex`, delete these two blocks (each occurs once;
    replace each by nothing):

    ```
    % This is a version pointer for LL, not a second canonical bibliography entry.
    \@namedef{bfgspreprint@LL18}{Lewis and Liang, 2018 preprint,
      \href{https://arxiv.org/abs/1807.03134v1}{arXiv:1807.03134v1}}
    ```

    ```
    % FND_JM25 is published in NeurIPS 2025 and is cited normally. This alias is
    % available only when a locator specifically concerns its earlier version.
    \@namedef{bfgspreprint@JM25v2}{Jin and Mokhtari, 2025 preprint version,
      \href{https://arxiv.org/abs/2507.00361v2}{arXiv:2507.00361v2}}
    ```
- **Register:** `A/introduction/prose/012`, `022`, `023` (citation sites).

### R-A-17 — Edition date and PDF keywords

- **Where:** `master.tex:29-30`.
- **Category:** typesetting (metadata). **Severity:** cosmetic.
- **Explanation:**
  - "Author-review edition, 13 September 2026" predates the October revisions;
    for example, M6 changed the statement of Theorem 11.
  - The PDF keywords ("…local convergence, formal verification") differ from the
    printed `\keywords` (line 61).
- **Fix:**
  - In `master.tex`, `\date{Author-review edition, 13 September 2026}` (occurs
    once) gets the final edition date at the release run.
  - In `master.tex`, `pdfkeywords={BFGS, convex nonsmooth optimization, local
    convergence, formal verification}` (occurs once) becomes `pdfkeywords={BFGS,
    convex nonsmooth optimization, global convergence, local convergence,
    counterexample}`.
- **Register:** none (metadata of `A/master/abstract/001`).

### R-A-18 — Small language points

- **Category:** language. **Severity:** cosmetic.
- **Points:** each old string occurs once.
  - (a) `introduction.tex:33-36`: the display is unpunctuated ("for the mixed model
    [display] Corollary 4.4 gives…").
    - Old: `                    F(u,v)=u^2+|v|` followed by a newline and `\]`.
    - New: `                    F(u,v)=u^2+|v|,` followed by a newline and `\]`.
  - (b) `geometry.tex:58-60`: "An admissible run … it does not assert" — a run
    asserts nothing.
    - Old: `it does not` + newline + `assert that an arbitrary line-search`.
    - New: `the definition does not` + newline + `assert that an arbitrary
      line-search`.
  - (c) `master.tex:45`: the abstract has stated no families.
    - Old: `including the stated max-linear and gauge families`.
    - New: `including coercive max-linear functions, norms and gauges`.
  - (d) `negative_lower.tex:7-8`: "the same" has no comparison object; Theorem 10
    says it explicitly.
    - Old: `produces the same infinite` + newline + `full-BFGS runs.`
    - New: `produces infinite` + newline + `full-BFGS runs, the same for every such
      pair.`
  - (e) `introduction.tex:46-47`: the theorem meant is not identified; it is the
    companion's Chapter 7 dichotomy (`global.tex:255-258`).
    - Old: `a value-convergence theorem` + newline + `for a broader homogeneous
      family`.
    - New: `the companion's value-convergence theorem` + newline + `for a broader
      homogeneous family (Chapter~7)`.
  - (f) `introduction.tex:119-123`: the outline omits Section 7.
    - Old: `Sections~\ref{art:global} and~\ref{art:local} prove its global and
      local` + newline + `consequences, and Section~\ref{art:failure} gives the
      deterministic` + newline + `counterexamples.`
    - New: `Sections~\ref{art:global} and~\ref{art:local} prove its global and
      local` + newline + `consequences, Section~\ref{art:failure} gives the
      deterministic` + newline + `counterexamples, and
      Section~\ref{art:verification} lists the remaining questions.`
- **Register:** `A/introduction/disp/001`, `A/geometry/prose/026`,
  `A/master/prose/004`, `A/negative_lower/theorem/art:local-failure-lower`,
  `A/introduction/prose/013`, `A/introduction/prose/051`.

## Checked without finding (summary)

- **Equation (1):**
  $(1-\tau)^2u^2+(1-\tau)|v|-u^2-|v|+\tau(2u^2+|v|)=\tau^2u^2$ for $v\ne0$,
  $0\le\tau\le1$.
- **Pairings:** both limiting gradients give $-2u^2$.
- **Figure vertices:** they are the 10-digit roundings of the root box.
- **Seed slopes:** affinely independent. $g_0^Tw=g_1^Tw=-1$ and
  $g_2^Tw\in(-16.72220,-16.72219)$ for $w=(-1,16)$, from the root box with exact
  fractions.
- **Affine/convex balance facts** (`geometry.tex:43-53`): every step is correct.
- **Hessian bounds of Theorem 10:** 51, $51\cdot65/64<52$ and
  $6\|g_2\|^2<6.92$, all below 64. At most five trials per search (Table
  `art:trial_table`).
- **Equation (35)** and the active-gradient test of Section 7: $\psi_b'(0)=0$; all
  four branches are active at 0; no strictly positive weights exist.
- **Theorems 7, 10, 11:** every clause is proved in `local.tex:48-76`,
  `failure.tex:356-425` (via Lemma `art:seed_cycle` and the margins at
  `failure.tex:154-162`; M11 known) and Appendix D (whitening constants
  $\underline\mu=\mu\lambda_{\min}$, $\overline L=512\lambda_{\max}$ rechecked). The
  summaries in the introduction (`71-82`, `85-102`), Section 2, Table
  `art:regularity-map` and Section 7 agree with them, except as listed above and in
  M7/M8.
- **References:** every `\ref`, `\eqref`, "above"/"below" in my files points to the
  intended object.
- **Bibliography keys:** all 17 bibliography keys are cited; every `\preprintcite`
  key is defined.
- **Abstract format:** 221 words and 5 keywords (MP: 150–250 words, 4–6 keywords).
- **Literature attributions** agree with the 12 September ledger: LO Challenge 7.1
  items and hypotheses; GL18 Corollaries 4.2/4.4 and their open paragraph; BG
  Theorem 3.1 with (B1.1)–(B1.5); XW Theorem IV.1; nonconvexity of Lewis–Zhang and
  Diao; scaled memoryless update in Asl–Overton; exact search in NEG_LO08;
  [N92, Section 5] trace/determinant potential.

## Coverage table

| File : lines | Item (label or register id) | Result |
|---|---|---|
| `master.tex:20-30` | title, date, PDF metadata | R-A-17 |
| `master.tex:37-63` | abstract (`A/master/abstract/001`, prose/001–013) | R-A-1, R-A-18(c); M7, M8 known |
| `introduction.tex:3-11` | opening (prose/050, 001, 002) | R-A-15 |
| `introduction.tex:13-17` | three answers (prose/003) | read: no finding |
| `introduction.tex:19-26` | Challenge 7.1, scope (prose/004, 005) | read: no finding |
| `introduction.tex:28-42` | Guo–Lewis, display $F(u,v)$ (prose/006–011, disp/001) | R-A-6, R-A-18(a) |
| `introduction.tex:44-53` | Xie–Wächter, Gebken (prose/012–017) | R-A-16, R-A-18(e) |
| `introduction.tex:55-60` | admissible runs (prose/018–020) | read: no finding |
| `introduction.tex:62-82` | Deterministic limits (prose/021–030) | R-A-16 |
| `introduction.tex:84-102` | Global and local convergence (prose/031–039) | read: no finding |
| `introduction.tex:104-116` | Analysis with degenerating matrices (prose/040–046) | read: no finding |
| `introduction.tex:118-126` | outline, companion (prose/047–049, 051) | R-A-18(f), R-A-7 |
| `positive_partition.tex:1-18` | Theorem 7 `art:polyhedral` (proof `local.tex:48-76`) | read: no finding |
| `negative_upper.tex:1-25` | Theorem 10 `art:local-failure` (proof `failure.tex:385-425`) | read: no finding (M11 known in the proof chain) |
| `negative_lower.tex:1-23` | Theorem 11 `art:local-failure-lower` (proof Appendix D) | R-A-14, R-A-18(d) |
| `geometry.tex:3-9` | mixed ridge (prose/040, 001–004) | R-A-10 |
| `geometry.tex:10-13` | equation (1) `art:mixed-inward-remainder` | R-A-12 |
| `geometry.tex:14-18` | (prose/005–008) | read: no finding |
| `geometry.tex:20-30` | Figure 1 `art:gradient-geometry` (prose/009–012) | R-A-9, R-A-10 |
| `geometry.tex:32-41` | seed corner (prose/013–018) | R-A-10 |
| `geometry.tex:43-53` | affine vs convex balance (prose/041, 019–024) | read: no finding |
| `geometry.tex:55-60` | quantifiers (prose/042, 025, 026) | R-A-18(b) |
| `geometry.tex:62-88` | Table 1 `art:positive-outcomes` (prose/027–032) | R-A-2, R-A-3, R-A-13 |
| `geometry.tex:90-95` | affine maxima (prose/033–035) | read: no finding |
| `geometry.tex:97-104` | local distinction (prose/036–039) | read: no finding |
| `verification.tex:3-7` | synthesis (prose/001–003) | read: no finding |
| `verification.tex:9-19` | why the counterexamples evade (prose/004–010) | R-A-11; M9 known |
| `verification.tex:21-34` | planar hypotheses test (prose/011–018) | R-A-4; M8 known |
| `verification.tex:36-42` | equation (35) `art:jump-secant` | read: no finding |
| `verification.tex:43-47` | (prose/019–022) | R-A-11 |
| `verification.tex:49-57` | remaining questions (prose/023–026) | R-A-5 |
| `verification.tex:59-65` | Formal verification (prose/027–029) | R-A-7 |
| `verification.tex:67-71` | AI assistance (prose/030) | R-A-8 |
| `bibliography.tex:1-39` | 17 entries | R-A-15 |
| `preprint_references.tex:1-33` | 9 preprint keys | R-A-16 |

There are no proof environments in my files; the proofs of Theorems 7, 10 and 11 are
in `local.tex`, `failure.tex` and Appendix D, and are listed with their theorems
above.
