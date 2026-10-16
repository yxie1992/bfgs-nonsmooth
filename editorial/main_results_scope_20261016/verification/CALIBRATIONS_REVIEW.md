# M42 calibrations and obstruction — independent review

16 October 2026. Reviewer: GPT-6 Astra, independent of the implementation agent.

## Verdict

**PASS for the complete joint hypotheses, actual full-BFGS histories, and prescribed-initialization obstruction.** The witnesses are genuine: the objective, compact sublevel, all positive-band certificates, valid line-search constants, initialization, and infinite actual-gradient BFGS history hold together in the two calibration examples. The gauge has all the homogeneous objective hypotheses and a genuinely differentiable positive-value starting state, but no differentiable weak-Wolfe first step from that state.

There are **no MUST-fix mathematical, quantifier, compilation, axiom, or import defects**, and no mandatory correction to the three propositions. One **SHOULD** item concerns retaining an explicit smallest-eigenvalue consequence for the printed proposition; an independently compiled and axiom-audited scratch proof is supplied for the fix pass. Two **OPTIONAL** TeX precision/scope improvements are listed below. The main joint witnesses do not depend on any of those changes.

### Reviewed inputs

- `bfgs_lean_article/BfgsArticle/HypothesisExamples.lean`, 792 lines, SHA-256 `39134726105a010df070f544fcba0bb8d186cce212546dafdf9017a3b7ad778a`.
- Implementation report `../calibrations/FINAL_REPORT.md`.
- `paper/appendices/hypothesis_examples.tex`: `art:examples-mixed` (12–62), `art:examples-full-rank` (64–85), `art:examples-no-step` (185–208), and the introductory convention (3–8).
- Relevant summary in `paper/sections/geometry.tex` (111–138), checked against `art:admissible`, `art:band-certificate`, `art:certificate`, and `art:homogeneous`.
- `AGENTS.md` and `HANDOFF.md` were read. The two-quadratic/existence-criterion/nonradial implementations and integration tooling were outside this review.

The source hash matches the implementation report. The production source was unchanged at the end of the main audit. Repository files were read only; all review artifacts are in this directory.

## Findings and exact corrections

### S1 — SHOULD: export the literal smallest-eigenvalue consequence

**Locations:** `paper/appendices/hypothesis_examples.tex:28–29`; `bfgs_lean_article/BfgsArticle/HypothesisExamples.lean:456–461,514–521`.

The paper explicitly says that the smallest eigenvalue of `H_k` tends to zero. The production module proves the exact diagonal formula and matrix convergence, but does not export a statement identifying the smallest eigenvalue. The printed assertion is correct: `0 < (1/2)^k ≤ 1`, so the least spectral value is `(1/2)^k`. This is a small literal-coverage bridge, not a flaw in the history or the joint assumptions.

**Correction:** after `Mixed.run_matrix_limit`, export the two results in `SpectralChecks.lean` inside the production `Mixed` namespace, naming them `run_least_eigenvalue` and `run_smallest_eigenvalue_tends_zero`. Their conclusions are:

```lean
IsLeast (spectrum ℝ (run.H k)) ((1 / 2 : ℝ) ^ k)

(∀ k, IsLeast (spectrum ℝ (run.H k)) ((1 / 2 : ℝ) ^ k)) ∧
  Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0)
```

The supplied proof rewrites with `run_matrices` and the **root-level** Mathlib lemma `spectrum_diagonal`, then uses `pow_le_one₀` and geometric convergence. It compiles with zero warnings and uses only the three standard axioms. The coordinator has a complete proof ready to retain with the existing TeX sentence; the suggested production exports above are a convenient way to expose it. This recommendation is about the assigned module's available conclusions; the coverage module/register remain the coordinator's separate responsibility.

### O1 — OPTIONAL: display the already verified full sublevel range

**Location:** `paper/appendices/hypothesis_examples.tex:21`.

The draft states the run for `b = 2/3`. That is true, but `Mixed.joint_witness` already proves the same conjunction for every `b ≥ 2/3`, as requested in the review brief.

**Exact replacement:**

```tex
For every $b\ge2/3$ an actual infinite admissible run in $K_b$, with
```

This strengthens the exposition without requiring a Lean change.

### O2 — OPTIONAL: make the projector's nonzero-step domain explicit

**Locations:** `paper/appendices/hypothesis_examples.tex:50–52,78–79`; projector formula at `paper/sections/energy.tex:249`.

The Lean projector is total, including `s = 0`; the printed quotient `I-ss^T/(s^Ts)` is ordinarily used only for `s ≠ 0`. The current proof context supplies nonzero steps for eligible pairs, so this does not invalidate either certificate. The phrase “any two endpoints” can nevertheless be read as including a repeated endpoint in the projected assertion.

**Exact replacements:**

```tex
Thus secant control holds for all differentiable endpoint pairs in $K_b$,
in particular for the eligible ones. For an eligible pair, $s\ne0$ and
$z=x+s$ give $\Pi_s z=\Pi_s x$, so projected transport holds with equality.
```

```tex
Visibility is $g^TIg=\norm{x}^2=2F(x)\ge2\eta$. For any two endpoints,
$y=s$, so $y^TIy=t$. For every eligible pair, the constant field makes
the projected-transport inequality an equality.
```

## Definitions and complete-assumption audit

1. **Actual objective and gradient.** `Vec n = Fin n → ℝ` and `Mat n` are the ordinary coordinate vector/matrix types. `gradientFunctional g v = dot g v` is the Euclidean gradient functional. Every gradient premise in the certificates and run structures is `HasFDerivAt`, not a directional derivative or a selected subgradient. Real-valued objectives are finite everywhere.
2. **Euclidean quadratic.** The objective is `sqNorm x / 2`, with `sqNorm = ∑ i, x i ^ 2`. `Quadratic.objective_euclidean` explicitly relates it to the norm of `euclideanVector x`. No squared Pi/sup norm is substituted. The independent test at `(1,1)` gives objective `1`, not `1/2`.
3. **Full run semantics.** `AdmissibleBFGSRun` includes finite convex objective, fixed valid `c₁,c₂`, initially SPD matrix, positive step lengths, nonzero actual gradients at every finite index, the position step, the full inverse-BFGS update, and both ordinary Armijo and weak Wolfe inequalities. It assumes neither bounded gradients nor summability, matrix convergence, iterate convergence, or a recurrence in place of the update. The reused `UnexcitedMetric.run` was read through these fields, including its actual-gradient and full-update proofs.
4. **All eligible pairs.** `EligiblePair` has actual derivatives at both endpoints, `d > 0`, `c₁ d ≤ Δ ≤ d`, and `(1-c₂)d ≤ t`. It has no assumption that the pair lies on the displayed history or is BFGS-realizable. `BandCertificate` quantifies over all such pairs in each positive band with `d ≤ δ`. Both constructors implement these exact fields.
5. **Constants and PSD.** `W = I` is SPD and symmetric; `W = xxᵀ` is symmetric PSD. Both are finite-valued matrices. The frozen structure has no `C_nonneg` field, but the production `certificate_parameters` and `joint_witness` conclusions explicitly supply `0 ≤ C`, closing that potential mismatch with the article. `m > 0`, `L ≥ 0`, `δ > 0` are structure fields.
6. **Compactness/minimizer.** For each objective, the implementation proves nonnegativity, value zero at zero, and `F x = 0 ↔ x = 0`, together with `IsLeast (range F) 0`. `Localization.sublevel_compact` then supplies compactness for every real sublevel from finite convexity and the attained unique minimizer. No compactness or unique-minimum premise is left for the caller.
7. **Band quantifiers.** Both calibration constructors work for arbitrary real `c₁,c₂` and every `η > 0`; the joint witnesses use the actual run constants. This is stronger than the paper's valid-constant convention and `0 < η ≤ b`. Empty high bands are allowed, but the examples also have nonempty positive bands and actual accepted pairs in them.
8. **Main-theorem applicability.** Independent scratch consumers apply `transported_certificate_convergence_on_sublevel` to each constructor for an arbitrary admissible run and starting sublevel. Both applications compile without supplying gradient bounds, summability, curvature control, or convergence as extra premises. Thus the constructions satisfy the convergence theorem's assumptions, rather than merely resembling its notation.

## Per-principal-declaration checks

Names below have prefix `BfgsVerification.HypothesisExamples.`. Line numbers are in the reviewed 792-line production source. All public declarations, not only those in this table, were axiom-audited.

### Quadratic

| Declaration(s), lines | Quantifier and coverage check |
|---|---|
| `objective`, `objective_euclidean`, 31,39–42 | Every natural dimension; literal Euclidean half squared norm. No sup-norm error. |
| `objective_convex`, `objective_hasGradient`, `gradient_eq`, 44–56 | Convexity on all space, actual full-space gradient `x` at every point, uniqueness of any claimed gradient. |
| `objective_nonneg`, `objective_eq_zero_iff`, `objective_minimum`, `sublevel_compact`, 60–76 | Attained minimum zero, unique minimizer zero, every real sublevel compact; no hidden positivity/compactness assumption. |
| `certificate`, `certificate_parameters`, 79–108 | Every set `K`, every real constant pair, every positive `η`. `W = I`, `m = 2η`, `C = 1 ≥ 0`, `L = 0`, `δ = 1`; PSD/visibility/all-pair secant and transport fields implemented. Rank exactly `n` and positive definiteness at every `x`. |
| `exact_field_equalities`, 111–122 | Secant equality for every endpoint pair and exact projected identity-field transport. Nonzero-step paper interpretation noted in O2. |
| `inverseBFGS_identity`, 125–133 | Actual full inverse update fixes `I` for `y=s`; no compressed or surrogate update. The actual run has nonzero steps/positive curvature. |
| `run`, 170–191 | Every prescribed `x₀ ≠ 0` in any finite dimension. `x_k=2^{-k}x₀`, `g_k=x_k`, `H_k=I`, `α_k=1/2`, `(c₁,c₂)=(1/4,1/2)`. All structure fields discharged. Nonzero start automatically excludes dimension zero. |
| `run_values`, `run_scalars`, `run_weak_wolfe_eq`, 193–220 | Values `4^{-k}F(x₀)`; `q=‖x_k‖₂²`, `d=q/2`, `Δ=3q/8=3d/4`, `t=q/4`; weak Wolfe exactly equality. |
| `run_limits`, 223–232 | Values and iterates tend to zero directly by geometric decay, with no convergence premise. |
| **`joint_witness`**, **236–259** | For every nonzero `x₀`, one actual `R` and `b=F(x₀)>0` jointly carry convexity, unique minimum, compactness, all iterate containment, every positive-band certificate with exact parameters/rank/nonnegative `C`, exact initialization/history, and both limits. |
| `planar_projection`, `planar_run_nonempty`, 262–274 | Explicit rank-two/nonzero-projection calibration and actual run from `(1,1)`. The sample projector at `(1,0)` is a field example, not falsely asserted to be the step of that particular history. |

### Mixed ridge

| Declaration(s), lines | Quantifier and coverage check |
|---|---|
| `objective`, `objective_formula`, 281–283 | Definitionally the literal `u²+|v|`, not a separate abstract objective satisfying an assumed formula. |
| `objective_convex`, `objective_eq_zero_iff`, `objective_minimum`, `sublevel_compact`, 285–304 | All-space finite convexity, attained unique minimum zero, every real sublevel compact. |
| `gradient_eq_of_nonneg`, `gradient_eq_of_nonpos`, `differentiable_coordinate_ne_zero`, 307–335 | Every actual full-space gradient is the appropriate `(2u,±1)`. At `v=0`, distinct supporting gradients rule out differentiability. The nonstrict sign branches introduce no false smoothness claim at the kink. |
| `radial_pairing`, 337–340 | At every differentiable point, `gᵀx=2u²+|v|`, hence visibility on the entire positive band. |
| `opposite_sign_bound`, `secant_bound`, 347–397 | Exact coefficient `2b`. For every real `b`, all actual-gradient endpoints with only `F(z)≤b`, `(yᵀz)²≤2b t`. No eligibility, positive curvature, smallness, first-endpoint sublevel, or displayed-run restriction. Four sign cases cover all differentiable endpoints. |
| `projected_transport`, 400–413 | Exact equality for all endpoint pairs, using `Π_s s=0` and the outer-product projection identity. No continuity or rank assumptions on the field. |
| `certificate`, `certificate_parameters`, 416–438 | `W=xxᵀ`, `m=η²>0`, `C=2b`, `L=0`, `δ=1`; all objective-only band pairs covered. `b>0` supplies the article's `C≥0`. |
| `run`, 441–444 | Literal specialization `A=1,v₀=2/3,ρ=1/2,c₁=1/4,c₂=1/2`; the necessary strict ratio inequality is discharged numerically. It is an actual infinite full-BFGS run. |
| `run_points`, `run_gradients`, `run_matrices`, `run_initial`, `run_constants`, 446–472 | Every finite `k`: `x_k=(0,(2/3)(-1/2)^k)`, `g_k=(0,(-1)^k)`, `H_k=diag(1,2^{-k})`, `α_k=1`; start `(0,2/3)`, `H₀=I`, exact constant pair. |
| `run_values`, `run_scalars`, 474–504 | `F(x_k)=(2/3)2^{-k}`, `d_k=2^{-k}`, `Δ_k=(1/3)2^{-k}=d_k/3`, `t_k=2·2^{-k}=2d_k`. Armijo and Wolfe use the actual step/gradient fields. |
| `run_limits`, `run_matrix_limit`, 506–521 | Both point/value limits are zero; actual matrices converge to `diag(1,0)`. The literal smallest-eigenvalue bridge is S1. |
| **`joint_witness`**, **526–552** | For **every `b≥2/3`**, objective facts, compact positive sublevel, the same explicit actual run, all iterate/scalar formulas, containment, every positive-band certificate with the same run constants and `C≥0`, and convergence hold together. |
| `run_nonempty`, 554 | Concrete inhabitant, not an implication from an assumed run. |

**About “sharp”:** the implemented theorem proves the requested `2b` estimate; it does not contain a separate least-possible-constant assertion. The draft does not assert optimality of `C` among eligible-pair certificates. For the stronger unrestricted differentiable-pair estimate the coefficient is indeed sharp as a supremum: take `z=(√(b-τ),τ)` and `x=(0,τ)`, with `0<τ<b`; the quotient `(yᵀz)²/t=2(b-τ)` tends to `2b`. Those ascending pairs are not generally eligible. The review does not interpret “sharp” as a claim of optimality on the smaller eligible-pair class for fixed `c₁,c₂,η,δ`.

### Gauge and prescribed initialization

| Declaration(s), lines | Quantifier and coverage check |
|---|---|
| `family`, `objective`, `branch_values`, `objective_formula`, 560–592 | Three literal slopes `(1,0),(-1,1),(-1,-1)`, zero offsets, exactly `max{u,-u+v,-u-v}`. |
| `objective_abs_formula`, `objective_convex`, `objective_continuous`, `objective_homogeneous`, 594–607 | Finite convex continuous objective; degree-one homogeneity for every `t≥0`, including zero. |
| `coordinate_bounds`, `objective_eq_zero_iff`, `objective_minimum`, 609–637 | `G≥|u|`, `G≥|v|/2`; minimum zero uniquely attained at zero. |
| `sublevel_compact`, `objective_coercive`, 639–649 | Every real sublevel compact; actual coercivity `Tendsto G (cocompact (Vec 2)) atTop`, not an assumed bounded-iterate property. |
| `admissible_runs_converge`, 653–658 | For every infinite admissible run on this exact objective, values and iterates tend to zero by the homogeneous theorem. It asserts conditional convergence, not run existence for the obstructed initial data. |
| `initialPoint`, `initialGradient`, `ray`, `ray_step`, 660–670 | Exact start `(ε,0)`, gradient `(1,0)`, ray `(ε-α,0)`, identity-metric BFGS displacement, for all real ray parameters. |
| `ray_gradient_before`, 672–678 | For all `α<ε`, a full-space Fréchet gradient exists and equals `(1,0)`; strict activity is checked against both other branches. |
| `ray_value_after`, `ray_not_differentiable_after`, 680–701 | For all `α≥ε`, value `α-ε`; both distinct slopes `(-1,1),(-1,-1)` are active, excluding ambient differentiability. Includes the origin and the entire negative horizontal continuation, even though the one-dimensional restriction is smooth beyond the origin. |
| `initial_state`, 703–714 | Every `ε>0`: value exactly `ε>0`, actual full-space nonzero gradient, SPD identity. This is not a nonsmooth or stationary starting state. |
| `no_differentiable_weak_wolfe`, 718–731 | Every `c₂<1`, every `α>0`, every proposed actual endpoint gradient: Wolfe is impossible. No Armijo, `c₁`, or nonexistence-of-gradient assumption is silently substituted. Before the origin Wolfe forces `c₂≥1`; at/beyond it no full derivative exists. |
| `no_admissible_run`, 734–748 | Any actual run with the specified `x₀,H₀` would give precisely the forbidden first derivative and Wolfe inequality. Quantifies over all valid line-search constant pairs through the run type. |
| **`joint_obstruction`**, **754–780** | For **every `ε>0`**, all objective hypotheses, positive differentiable initial state, exact ray, both ray regimes, universal first-step obstruction, and absence of a run from those data hold jointly. |
| `obstructed_state_exists`, 782–788 | Concrete witness `ε=1` establishes a real obstructed positive-value state; no impossible hypothesis is used to manufacture the obstruction. |

## Non-vacuity checks

- **Quadratic:** `x₀=(1,1)` in dimension two is explicitly nonzero. The closed specialization of `joint_witness` elaborates. `F(x₀)=1`; a positive band at `η=1/2` is nonempty, formally checked. The first actual accepted pair also lies in the band `η=1/4` with `d₀=1=δ`; thus pair control has a concrete nonempty application.
- **Mixed:** the closed specialization `b=2/3` elaborates. The band `η=1/3` contains the start and the next accepted point, of values `2/3` and `1/3`; `d₀=1=δ`. Both endpoints are actual differentiability points. Band nonemptiness is checked independently in Lean.
- **Gauge:** the closed specialization `ε=1` elaborates, with positive value and actual nonzero gradient. The obstruction concerns the **first** accepted step. A nonexistent infinite history is not being used as evidence that an existing history stagnates or violates a convergence theorem. No existence of an infinite run on this gauge from other data is asserted by this module or by the reviewed proposition.

## TeX proof and reference checks

- `art:examples-mixed`: sign cases and all constants match. In the crossing case `S=|v|+|w|>0` because differentiable endpoints have nonzero second coordinates; the displayed weighted Cauchy–Schwarz estimate is equivalent to the division-free Lean proof. Visibility uses `(gᵀx)²`, not an assumed gradient bound. The history gives `s=-Hg`, `y=-2g`, `Δ=d/3`, `t=2d`; the full update and both inequalities follow with the stated constants. The spectral sentence is mathematically correct; S1 supplies its explicit formal bridge.
- `art:examples-full-rank`: the appendix's Euclidean convention matches `objective_euclidean`. `∇F=x`, `y=s`, `m=2η`, `C=1`, full rank, identity update, and `Δ=3d/4` all match. The nonzero-start hypothesis is essential and retained. The theorem is not specialized to dimension two.
- `art:examples-no-step`: the bounds establish coercivity and uniqueness; strict activity supplies the initial gradient. Dividing Wolfe by the positive `α` yields exactly the printed impossible inequality `-1≥-c₂`. At `α=ε` all three slopes tie; for `α>ε` the last two tie and are maximal. The final paragraph correctly distinguishes the initialization obstruction from nonoptimal stagnation. The reference `art:homogeneous` is to the appropriate finite/convex/coercive/degree-one theorem.
- `geometry.tex:111–130,135–138`: the automatic analytical consequences follow under the admissible-run convention and compact sublevel. The references to the mixed/full-rank certificates and the homogeneous first-step obstruction are accurate; the text keeps the existence/convergence distinction. Assertions about the other agents' examples were not reviewed here.
- Visual inspection: relevant portions of supplied pages **6, 50, 51, 52**, plus independently rendered **53** from the 54-page `paper/build/master.pdf`. Formulas and references are readable and agree with the source. The proposition/proof page breaks introduce no mathematical ambiguity or clipping.

## Compilation, axioms, and hygiene

### Main audit — PASS

The complete production file was copied verbatim into `Audit.lean`, followed by `#check` and `#print axioms` for **all 90 public declarations**, and seven independent consumer/non-vacuity checks. No import of a new `.olean` was required.

Command, with working directory `bfgs_lean_article`:

```sh
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/review_calibrations/Audit.lean \
  > /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016/review_calibrations/Audit.log 2>&1
```

Final result: **exit 0, zero errors, zero warnings**. All 90 production declarations have exactly `[propext, Classical.choice, Quot.sound]`; all seven scratch checks use only these standard axioms. `AuditSummary.json` mechanically validates the counts, absence of `sorryAx`, absence of diagnostics, and unchanged production-source hash.

The initial scratch-consumer run needed an explicit vector dimension and an explicit absolute-value simplification. Those errors occurred only in the appended review checks; the production source and its 90 axiom checks were already clean. The retained `Audit.previous.log` is superseded by `Audit.log`.

### Smallest-eigenvalue bridge — PASS

`SpectralAudit.lean` consists of the same unmodified source snapshot plus `SpectralChecks.lean`. Compiled with the same working directory, environment, and `lake env lean` command, substituting `SpectralAudit.lean`/`SpectralAudit.log` for the main audit paths: **exit 0, zero errors, zero warnings**. Both new proof declarations use exactly `[propext, Classical.choice, Quot.sound]`. `SpectralAuditSummary.json` validates those two outputs and rechecks the production hash. The initial scratch attempt qualified `spectrum_diagonal` with `Matrix`; that lemma is root-level. This was a reviewer proof-script correction, not a production error; `SpectralAudit.previous.log` is superseded.

### Hygiene — PASS

- All production names are within `BfgsVerification.HypothesisExamples`, with only the intended `Quadratic`, `Mixed`, and `Gauge` subnamespaces.
- Five direct mathematical `BfgsVerification.*` imports. Inspection of the **105-module project import closure** finds no `Coverage.*`, `BfgsArticle` root, or `BfgsVerification` root import.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, custom opaque proof device, extern reduction, or linter suppression in the assigned source. The audited axiom closures also exclude hidden uses of such proof shortcuts.
- Every review Lean invocation was sequential, with `LEAN_NUM_THREADS=4` and the prescribed Lake environment; no build/update/clean/exe or repository-mutating git command was run.

### Artifacts

`HypothesisExamples.snapshot.lean`, `metadata.json`, `Audit.lean`, `Checks.lean`, `Audit.log`, `AuditSummary.json`, `SpectralChecks.lean`, `SpectralAudit.lean`, `SpectralAudit.log`, `SpectralAuditSummary.json`, `prepare_audit.py`, `summarize_audit.py`, `page_53.png`, `page_53.txt`, and this report. Superseded review-script diagnostic logs are retained with `.previous.log` names.

### Completion note

**Review complete.** The 90-declaration production audit, seven independent contract/non-vacuity checks, and two literal spectral-bridge proofs all pass with standard axioms only. The three joint claims are truly verified; the remaining recommendations are the S1 proof-retention follow-up and optional O1/O2 wording changes. No Lean process remains running for this review.
