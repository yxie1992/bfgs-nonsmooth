# M42 independent review: final article additions and literal Lean coverage

16 October 2026. Reviewer: GPT-6 Astra, independent of the implementation agent.

## Verdict

**PASS for the mathematics, literal theorem correspondence, and joint hypothesis/run witnesses. Two minor documentation corrections remain before calling the coverage integration complete: R1 and R2 below.**

I checked every sentence, definition, display, and connecting proof step in the new appendix, all twenty new geometry/local prose items, and the five new Chapter 7 items. I found no false mathematical assertion, dropped hypothesis, reversed quantifier, unjustified `LEAN`/`PROOF` status, or missing joint witness. No manuscript correction or additional mathematical proof is required. The attained-Rayleigh/eigenvector statement is a genuine characterization of the least eigenvalue; the optional actual-spectrum check below supplies an even more direct library-level formulation.

All 27 new article coverage declarations and all seven inspected Chapter 7/core declarations compile and use exactly `[propext, Classical.choice, Quot.sound]`. Both assigned-file and full strict coverage checks pass. All 57 PDF pages changed relative to the supplied baselines were rendered at 110 dpi and inspected; there is no new visual/reference defect. Final LaTeX warning counts agree with the baselines.

## 1. Reviewed snapshot and boundaries

- Repository: `/Users/yxie/Projects/bfgs-nonsmooth`.
- Scratch root `S`: `/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016`.
- Read the complete review prompt, `AGENTS.md`, `HANDOFF.md`, the coverage method, the implementation report, both core implementation reports including fix-pass dispositions, and both independent core reviews.
- The assignment identified reviewed core commit `1ef18d9`. During the read-only review the coordinator's HEAD advanced to `b783e4e6ec283239c80ba4faa1a63c7f669c47ef`. The scoped source hashes continued to match the supplied core/coverage reports. `snapshot/` and `static_summary.json` identify the precise reviewed files.
- Reviewed source: the complete 208-line `paper/appendices/hypothesis_examples.tex`; additions at `paper/sections/geometry.tex:111–138` and `paper/sections/local.tex:444–451`; `companion/chapters/07_H.tex:102–111`; their registers; the new article coverage module; and the relevant Chapter 7 declarations/docstrings. The exact cited article assumptions, run/certificate definitions, and implementation contracts were also read.
- The infrastructure agent's assembler/additions-helper/correspondence paths, generated ledger, and pending manifests were outside this review. Repository source files and git were not mutated. Core modules/oleans were not rebuilt. All review output is in `S/review_coverage/`.

Important source hashes:

| Source | SHA-256 |
|---|---|
| `BfgsArticle/HypothesisExamples.lean` | `39134726105a010df070f544fcba0bb8d186cce212546dafdf9017a3b7ad778a` |
| `BfgsArticle/TwoQuadraticExample.lean` | `cd5e4550d341a44442925692125100e3bb952c1e110d0a75dc8004ee545ba518` |
| `BfgsArticle/Coverage/Article/HypothesisExamples.lean` | `4d738b9b3d9843a25d540c62dbebe1d86375fb86ac393ce56c79a401e5a345f3` |
| `BfgsArticle/Coverage/Companion/Ch07H.lean` | `b9b692a8d4f0a683b7501217bad74104ec5d0bc6a53d38b6c4451f53f119285f` |
| `paper/appendices/hypothesis_examples.tex` | `e6d8c5c1bb154bd83c10251bc33257edec0f54de664898ce876054734012c10e` |

Lean paths in this report are relative to `bfgs_lean_article/` unless stated otherwise.

## 2. Findings and concrete fixes

### R1 — Minor required documentation fix: finish the Chapter 7 line-reference carry-forward

The authoritative item ranges, all 70 shifted explicit `companion/chapters/07_H.tex:...` citations, and the five newly inserted citations are correct. However, the following current-document references still contain pre-insertion numbers. These are navigational defects, not mathematical defects or reasons to change item statuses.

**(a) `BfgsArticle/Coverage/Companion/Ch07H.lean:74–91`: eighteen rows of the introductory `Items` table.** Add eleven to the post-insertion TeX line numbers in the `Lines` column. Leave its `24–28` reference unchanged. Exact replacements:

| Lean line | Current TeX range | Correct TeX range |
|---:|---|---|
| 74 | 106–122 | 117–133 |
| 75 | 124–132 | 135–143 |
| 76 | 142–146 | 153–157 |
| 77 | 24–28, 170–218 | 24–28, 181–229 |
| 78 | 247–261 | 258–272 |
| 79 | 272–317 | 283–328 |
| 80 | 335–361 | 346–372 |
| 81 | 367 | 378 |
| 82 | 377–384 | 388–395 |
| 83 | 405–408 | 416–419 |
| 84 | 417–425 | 428–436 |
| 85 | 431–433 | 442–444 |
| 86 | 448–471 | 459–482 |
| 87 | 461–463 | 472–474 |
| 88 | 498–534 | 509–545 |
| 89 | 543–563 | 554–574 |
| 90 | 594–657 | 605–668 |
| 91 | 675–719 | 686–730 |

**(b) `editorial/lean_coverage/register/C_07_H.json:1305`, item `C/07_H/prose/031`, note.** The six parenthesized proof-step references lack the word `line`, so the preceding resync missed them:

- `values_dichotomy (330-331` → `values_dichotomy (341-342`;
- `q_not_bounded_away (339` → `q_not_bounded_away (350`;
- `potential_lower_bound (339-340` → `potential_lower_bound (350-351`;
- `reciprocal_summable_of_weighted (346-347` → `reciprocal_summable_of_weighted (357-358`;
- `bounded_away_of_pointwise (363-364` → `bounded_away_of_pointwise (374-375`;
- `finite_limit_zero (364` → `finite_limit_zero (375`.

**(c) The same register at line 1750, item `C/07_H/prose/058`, note.** Replace `Lines 577-578: maxLinear_planar_zero_branch_iterates; 578-580:` with `Lines 588-589: maxLinear_planar_zero_branch_iterates; 589-591:`.

The unchanged `resolved_discrepancies` descriptions are historical and are not part of this correction. `reference_findings.json` contains machine-readable replacements and the explicit-reference check.

### R2 — Minor required method-format fix: put the new item citation first in the cited coverage docstrings

Coverage-method rule 3 (`editorial/lean_coverage/README.md:76–79`) requires a coverage docstring to start with `Item ... (file:lines)`. The new citations are accurate and attached to the correct declarations, but were appended at the ends of previously unregistered helper docstrings:

| Declaration in `BfgsCoverage.Companion.Ch07H` | Docstring lines | New item |
|---|---:|---|
| `maxLinear_affine_free_no_run` | 1597–1603 | `C/07_H/prose/077`, TeX 102–104 |
| `tilt_collinear_no_run` | 1493–1497 | `C/07_H/prose/078`, TeX 104–106 |
| `tilt_two_values_no_run` | 1544–1546 | `C/07_H/prose/078`, TeX 104–106 |
| `maxLinear_line_no_run` | 1430–1436 | `C/07_H/prose/079`, TeX 107–109 |

Move each existing `Item` citation to the beginning of its docstring, followed by the current mathematical description. In particular the first two are the first `LEAN` names of the new items. This is a documentation convention correction only: first-name module ownership and the semantic correspondence already pass. The existing `TiltNoInfiniteRunQuestion` docstring already starts with its original item citation and can retain the added second citation for `prose/080`.

### O1 — Optional evidence strengthening: retain an actual-spectrum corollary

**Locations:** appendix 28–29; coverage `mixed_smallest_eigenvalue:79–106`; register `A/hypothesis_examples/proposition/art:examples-mixed`.

The current theorem proves all of the following for the displayed matrices: the least value of `vᵀH_kv` on `sqNorm v = 1` is `2^{-k}`; `(0,1)` is a unit eigenvector with that eigenvalue; and `2^{-k} → 0`. This is a valid least-eigenvalue characterization: every eigenvalue of the real symmetric matrix has a unit eigenvector, and evaluating the proved lower bound on it gives the comparison. It is substantially more than entrywise convergence to a singular matrix. There is no false eigenvalue claim or dropped spectral assumption.

For a completely direct Mathlib-spectrum formulation, `SpectralCheck.lean` independently proves and audits

```lean
IsLeast (spectrum ℝ (Mixed.run.H k)) ((1 / 2 : ℝ) ^ k)
```

and its joint limit, using the earlier independent reviewer's `spectrum_diagonal` proof and the current coverage limit. Both statements compile with only the standard axioms. Retaining this short corollary in the owned coverage module and listing it in the existing proposition item would make the library-level correspondence especially explicit. It is an optional strengthening of the encoding, not an additional mathematical hypothesis or a required correction.

## 3. Literal mathematics and quantifiers

### 3.1 Shared definitions and assumptions

- `Vec n` has the finite-Pi norm/topology, but the quadratic objective and Rayleigh sphere explicitly use `sqNorm`/`euclideanVector`. There is no substitution of the sup norm for the Euclidean norm. Coordinate dot products represent actual ambient Fréchet derivatives through `gradientFunctional`.
- `AdmissibleBFGSRun` was checked against Definition `art:admissible`: it includes global convexity, fixed valid constants, initial SPD, every positive length, every nonzero actual gradient, every position step, the full inverse-BFGS update, Armijo, and weak Wolfe. It contains no convergence or gradient-bound assumption. The appendix's reference to that definition supplies the positive-dimension convention; the general wrappers retain `1 ≤ n`.
- `EligiblePair` uses both actual ambient derivatives, positive predicted decrease, the Armijo/convex decrease sandwich, and the weak-Wolfe curvature lower bound. It is an objective-pair predicate, not an assumed realizability assertion.
- `BandCertificate` quantifies over every eligible pair in the positive band with `d ≤ δ`, and over all differentiable band points for visibility/PSD. Its signs include `m > 0`, `L ≥ 0`, `δ > 0`; both new certificate statements explicitly add the article's `C ≥ 0`. Symmetric PSD is encoded by `Matrix.PosSemidef`. Compactness and the attained minimum are supplied separately in the same result sets.
- The O2 wording is correct: the printed quotient projector is now invoked only for eligible, hence nonzero-step, pairs. The total Lean projector's extension at zero does not enlarge the printed assertion.

### 3.2 Mixed ridge — appendix 12–62

Coverage: `mixed_certificates`, `mixed_history`, `mixed_smallest_eigenvalue`, the four `mixed_*` proof-display theorems; items `proposition/art:examples-mixed`, `disp/001–006`, `proof/001`.

1. `mixed_certificates` keeps **every `b > 0`**, not only `b ≥ 2/3`. It proves the literal objective, convexity, attained unique minimum zero, compact sublevel, and the exact field/constants for every `0 < η ≤ b`. The line-search pair is arbitrary and valid; the core constructor actually works more generally.
2. Visibility is `(gᵀx)² ≥ η²`, from `g=(2u,sign v)` and `gᵀx=2u²+|v|≥F(x)≥η`. Full-space differentiability excludes `v=0`.
3. Both same-sign identities and their `2F(z)t` bound are literal conclusions. Both opposite-sign identities include `S>0`; the two cases exhaust all differentiable endpoint pairs. The intermediate weighted-Cauchy expression is proved, rather than only its final `2bt` consequence. The difference identity is `4((r-u)|w|-Sr)²/S`, followed by `|w|²/S≤|w|` and `F(z)≤b`.
4. All endpoint pairs in the printed sublevel satisfy secant control. Eligible pairs have `s≠0`, and `Π_s z=Π_s x` gives exact projected transport for `xxᵀ`, with `L=0`.
5. The history is specifically at **`b=2/3`** and for the same objective/certificate/constants. Its start is `(0,2/3)`, `H₀=I`, `(c₁,c₂)=(1/4,1/2)`, and `α_k=1`. The actual gradients are `(0,(-1)^k)`. `s_k=-H_kg_k`, `y_k=-2g_k`, `d_k=2^{-k}`, `Δ_k=d_k/3`, `t_k=2d_k` give both printed line-search inequalities.
6. The actual inverse update leaves the first diagonal entry equal to one and halves the second. Every finite iterate is differentiable and nonstationary. The theorem supplies containment and both value/iterate convergence for this same run.
7. The exact least-Rayleigh value, unit eigenvector, and geometric limit are proved locally in the coverage module and incorporated into the joint-history statement. The spectral issue is resolved substantively; O1 supplies a direct-spectrum alternative.

### 3.3 Full-rank calibration — appendix 64–85

Coverage: `quadratic_certificates`, `quadratic_history`, `quadratic_history_decrease`; items `proposition/art:examples-full-rank`, `disp/007`, `proof/002`.

The objective is precisely `sqNorm x / 2 = ‖euclideanVector x‖²/2` in every `n≥1`. All positive sublevels, the unique attained minimizer, every `0<η≤b`, the identity field, `m=2η`, `C=1≥0`, `L=0`, `δ=1`, SPD, and rank exactly `n` are supplied. These are not restricted to the planar sample.

For every prescribed `x₀≠0`, the same objective and `b=F(x₀)>0` carry the actual run `x_k=2^{-k}x₀`, `g_k=x_k`, `H_k=I`, `α_k=1/2`, with the printed constants. No unspecified substitute start is used. Nonzero initial data ensure nonzero gradients at every finite index. The full inverse update fixes the identity because `y=s`; `Δ=3d/4` and weak Wolfe is exactly equality. All iterates lie in the stated compact sublevel and both limits are zero. The secant equality holds for any endpoints; the printed transport assertion is correctly restricted to eligible pairs.

### 3.4 General step and infinite-run existence — appendix 89–120

Coverage: `strict_wolfe_step`, `admissible_run_exists`; items `lemma/art:examples-run-existence`, `disp/008`, `proof/003`, `prose/004–005`.

The exception set in both wrappers is failure of **full-space** `DifferentiableAt ℝ F` at `x+t•p`, for every differentiable base point and every nonzero direction. Global convexity and boundedness below remain hypotheses. SPD and the nonzero actual gradient give `p=-Hg≠0` and `D=gᵀp<0`.

The printed proof matches `AdmissibleRunExistence:85–190`: the secant slope is continuous for positive times, tends to `D` at zero, and exceeds `c₁D` eventually by the lower bound. Since `D<c₂D<c₁D<0`, an open positive interval has slopes between the latter two values; its complement of the countable bad-time set is nonempty. The upper bound is strict Armijo; the endpoint supporting inequality gives strict weak Wolfe. The wrapper correctly divides the core's step-pairing inequality by `α>0` to obtain the printed direction pairing.

The infinite clause adds nonstationarity at **every** differentiability point, as printed. `AdmissibleRunExistence:199–244` chooses a next state from every actual-gradient SPD state and recurses on all natural indices; positive curvature preserves SPD under the unmodified inverse update. All prescribed initial-point/matrix/constants equalities are retained, including the initial actual gradient. There is no claim about a specified line-search implementation and no mere finite-prefix substitute for an infinite run.

### 3.5 Two-quadratic family — appendix 124–162

Coverage: `two_quadratic_formula`, all three hypothesis-expansion theorems, `two_quadratic_objective_geometry`, `two_quadratic_planar_hypotheses`, `two_quadratic_finite_max_hypotheses`, `two_quadratic_joint`, `two_quadratic_tie_determinant`; items `proposition/art:examples-two-quadratics`, `disp/009–010`, `proof/004`.

- The definition unfolds to the exact maximum in the original coordinates. The only objective premises are `a,b,c>0`. No condition `a≠c` is introduced anywhere; the `a=c` line case is explicitly proved.
- The actual Hessians are `diag(2a,2b)` and `diag(2c,2b)`, bounded below by `2 min(a,b,c) I`. Their average is the stated positive quadratic. The unique attained minimum is zero, all real sublevels are compact, and strong convexity excludes boundary segments at every positive level.
- The switching equation and ambient differentiability equivalence identify exactly `v=(c-a)u²/2`. The two actual gradients differ by two in their second coordinates. Their tie determinant is exactly the printed `-2u(a+c+b(c-a)²u²)`; its bracket is positive, and a tie with `u=0` is the origin.
- Affine criticality uses the affine hull of the **actual convex subdifferential**, not a chosen collection of slopes. At smooth points it implies stationarity/optimality; at nonzero ties the independent gradients exclude zero from their affine hull. The critical set is exactly `{0}`.
- The three expansion theorems expose every field. The literal planar conjunction matches `local.tex:214–229,276–281`: finite convex objective, attained minimum, every prescribed `B>0`, compactness, all intermediate strict contours, an open-neighborhood smooth or convex active-`C²` two-branch representation with independent actual gradients, and `C_aff∩K_B⊆argmin F`.
- The finite-max package matches `local.tex:303–322`, with the open neighborhood chosen as all space, both original active indices retained, gradients `(0,1),(0,-1)`, affine independence, and positive half weights summing to one and balancing to zero. Its strict-contour threshold is chosen before the run.
- `two_quadratic_joint` states the objective hypotheses and convergence of **every admissible run before** quantifying over every differentiable start, every SPD matrix, and every valid constant pair. The existential run has exactly those data and converges for the same family. Its convergence is not assumed to prove existence.
- The line polynomial is `(a-c)p_u²t² + [2(a-c)x_up_u+2p_v]t + [(a-c)x_u²+2x_v]`; its constant term is nonzero at a differentiability point. Thus the connecting “at most two” statement is correct, including `a=c`. The exported theorem gives finiteness, which suffices for countability. The sharper root count is an undisplayed connecting proof step, permitted by the coverage method; it is not an uncovered displayed or named theorem. A differentiable stationary point would be the unique, nondifferentiable minimizer, giving the required nonstationarity.

### 3.6 Printed three-quadratic example — appendix 164–181

Coverage: `nonradial_runs`, `nonradial_initial_value`; items `corollary/art:examples-nonradial-runs`, `proof/005`.

The theorem concerns precisely the existing `PlanarQuadraticExample.objective` from Theorem `art:nonradial-example`. It retains **every differentiable** `x₀` with `F(x₀)<1/100`, **every** SPD initial matrix, and **every** valid pair. The arbitrary-data existence theorem and the explicit-basin convergence theorem are applied to the same run. Universal low-start convergence is also stated separately. The value calculation is exactly `1001/10^6<1/100` at `(1/1000,0)`, and that point has a genuine full-space derivative with branch 0 strictly winning.

I checked the polynomial proof in `AdmissibleRunExistence:293–391`, rather than inferring finiteness from an arbitrary quadratic restriction. The pairwise differences are

`u-v+u²/2-v²`, `2u+v-u²/2-v²/2`, and `u+2v-u²+v²/2`.

The first and third equality sets are the nondegenerate hyperbolas `(u+1)²/2-(v+1/2)²=1/4` and `(v+2)²/2-(u-1/2)²=7/4`; the middle one is the circle `(u-2)²+(v-1)²=5`. The circle has a nonzero quadratic coefficient on every nonconstant line. For either hyperbola, identically vanishing quadratic and linear coefficients force the base point onto a null-direction line through its center, inconsistent with the nonzero level. The implementation explicitly excludes simultaneous vanishing of all three coefficients. Hence every pairwise difference restricts to a nonzero polynomial of degree at most two on every nonconstant line. The finite union of their zero sets contains all ambient nondifferentiability times.

The averaging lower bound `F≥u²+v²` gives boundedness below and unique minimum zero. The distinct active gradients at zero rule out full differentiability there; convexity then excludes any differentiable stationary point. These are the complete premises of the existence criterion, not assumed regularity of a line restriction.

### 3.7 Gauge obstruction — appendix 185–208

Coverage: `gauge_formula`, `gauge_no_step`, `gauge_covered_convergence`, `gauge_ray_minimizer`; items `proposition/art:examples-no-step`, `proof/006`, `prose/006`.

The formula is exactly `max{u,-u+v,-u-v}`. The conjunction supplies all finite/convex/coercive/degree-one homogeneous hypotheses of Theorem `art:homogeneous`, the attained unique minimizer, and every prescribed `ε>0` differentiable start with actual gradient `(1,0)` and identity metric. The inequalities `G≥|u|` and `2G≥|v|` prove the claimed growth and uniqueness.

For `0<α<ε`, the ray endpoint has the same actual gradient, and weak Wolfe requires the impossible `-1≥-c₂` for every `c₂<1`. For **all** `α≥ε`, the two distinct last slopes are active, so the full-space endpoint is nondifferentiable, even where the scalar ray restriction is smooth. These cases cover the whole positive ray. Any alleged admissible run with the stated point and metric would supply the forbidden first endpoint. No Armijo premise is needed for this obstruction. At `α=ε>0` the ray reaches the minimizer; the conclusion is correctly described as a prescribed-initialization obstruction, not a nonoptimal stagnating history.

### 3.8 Geometry/local summary sentences

All sixteen `A/geometry/prose/044–059` and four `A/local/prose/045–048` are valid `SAME_AS` summaries with the inherited hypotheses documented:

- `044–047`: admissibility gives SPD preservation and positive curvature; finite convexity bounds subgradients on compact sets; Armijo plus that compact-sublevel setting gives summable predicted decreases. `C/02_M/prose/007` is exactly the independent compact-subgradient bound; this register reference does not introduce a forbidden article coverage import.
- `048–052`: centered representation/initial-sublevel containment, finite smooth cell extensions and uniqueness, the squared-loss/positive-ℓ₁ example, indexed active-gradient affine independence/positive balance, and the common positive actual-Hessian sufficient condition all match their cited theorem hypotheses. The prose does not replace the full theorems by fewer assumptions.
- `053–058`: the new joint witnesses and obstruction have the stated scope. “Every dimension” means `n≥1`; “curved switching” describes the family, whose cited proposition includes its straight-line specialization. Nonradial existence for every matrix/pair is witnessed at the numerical differentiable low start and, more strongly, every such differentiable low start.
- `059` is a correct scope summary of sufficient examples. The local paragraph likewise preserves the exact value, full-space differentiability, arbitrary matrix/pair scope, and all-positive-sublevel two-branch geometry. No genericity or necessity result is silently asserted.

### 3.9 Chapter 7 caveat and classifications

The complete new paragraph is present at `companion/chapters/07_H.tex:102–111`.

| Item | Status | Independent semantic check |
|---|---|---|
| `prose/076` | `NON_CLAIM` | Lead-in distinguishes conditional run conclusions from existence; substantive assertions have their own items. |
| `prose/077` | `LEAN` | `maxLinear_affine_free_no_run` has precisely ambient `n≤2`, a finite maximum, and `0∉aff(range a)`, concluding `IsEmpty (AdmissibleBFGSRun n F)`. Nonemptiness of the slope family follows from the maximum representation. Dimension zero admits no nonzero-gradient run; in one dimension the common pairing forces a single slope; in two dimensions slopes lie on an affine line missing zero. |
| `prose/078` | `LEAN` | `tilt_collinear_no_run` takes the exact explicit representation `b_i=c+β_i d`, in arbitrary tangential/ambient dimension, including `d=0`. Lifted slopes `(b_i,1)` lie on the line through `(c,1)` in direction `(d,0)`, with independent base/direction when `d≠0`. `tilt_two_values_no_run` includes any number of original indices with at most two distinct slopes, including one value. |
| `prose/079` | `PROOF` of `prose/077` | The note correctly states that it also proves `prose/078`. `maxLinear_line_no_run` takes the two extreme scalar slopes, gives a linear objective if they coincide, and otherwise obtains `|pᵀx|+qᵀx` with independent `p,q`, equivalent to the maximum of two independent linear forms. The existing two-piece nonexistence theorem applies; no many-piece finite-termination theorem is assumed. |
| `prose/080` | `OPEN` | `TiltNoInfiniteRunQuestion` is an unproved universal no-infinite-run proposition. Its collinear cases are proved, so the unresolved existence/counterexample issue is correctly isolated to noncollinear higher-dimensional families. The item does not assert that a run exists. |

The cited section is exactly `H:connection-to-the-two-piece-paper`, now source lines 455–482 and printed Section 7.6.1. It discusses the correct two-piece model and Xie–Wächter result. The entire mathematical code of `Ch07H.lean`, after stripping comments, is token-identical to the prior committed source. No theorem assumption or conclusion was changed by this citation update.

## 4. Coverage structure and declaration checks

- **54 new items:** appendix 29, geometry 16, local 4, Chapter 7 five. Status totals: `LEAN 14`, `DEFINITION 1`, `PART_OF 4`, `PROOF 7`, `SAME_AS 25`, `NON_CLAIM 2`, `OPEN 1`. There are no new `TODO` or `DISCREPANCY` items.
- All first `LEAN` names are declared in their owning coverage module. All prose anchors match their current source ranges. Every new article named declaration is cited by the appendix register.
- The four statement displays classified `PART_OF` are literally included in their owning result's theorem set. The two-quadratic definition is correctly `DEFINITION`, with the actual definitions plus an unfolding theorem. The five proof displays have their own literal `LEAN` statements. The six appendix proof environments have correct targets; the Chapter 7 reduction has the stated primary target and explicit secondary-proof note.
- The 27 article declarations were all read, elaborated, and axiom-audited: the seven mixed declarations, three quadratic declarations, two general existence declarations, nine two-quadratic declarations, two nonradial declarations, and four gauge declarations.
- The five non-vacuity examples are actual witnesses: mixed run, Euclidean quadratic run, two-quadratic prescribed-state run, numerical nonradial prescribed-state run, and a genuinely differentiable positive-value obstructed gauge state.
- Old geometry/local registers and metadata are preserved exactly: 46 and 76 old items respectively. Their old TeX contents are exact prefixes of the updated files.
- All 99 shifted old Chapter 7 item ranges are correct. All old fields other than ranges and notes are unchanged; all 70 shifted explicit file citations are correct. Relative to the prior committed register, 26 old notes have numeric line-reference changes in total (including the explicit resync change as well as the manual note pass). Their nonnumeric content is unchanged. R1 identifies the remaining shorthand/index references.
- The current O2 proof hashes for appendix `proof/001` and `proof/002` pass strict validation and match the substantively valid nonzero-projector clarification.
- The article module imports exactly `BfgsArticle.HypothesisExamples`, `BfgsArticle.TwoQuadraticExample`, and `BfgsArticle.AdmissibleRunExistence`. It uses no root or other coverage import. No forbidden proof/trust device or linter suppression occurs in its code.

## 5. Independent compilation and axiom evidence

All Lean invocations were sequential, with `LEAN_NUM_THREADS=4`, from `bfgs_lean_article/`. The owned import overlay was used for the new article dependencies; its three core links resolve to the two reviewed isolated oleans and the existing `AdmissibleRunExistence.olean` respectively.

`article_audit.lean` is the **complete, unchanged 686-line coverage source** followed by `#check` and `#print axioms` for all 27 declarations. `chapter7_audit.lean` similarly contains the complete unchanged current Chapter 7 coverage source, followed by the six cited Chapter 7 declarations/definition and `TwoPieceBudget.no_infinite_independent_two_piece`. Thus the checks freshly elaborate the changed modules rather than merely importing old coverage oleans.

| Check | Result | Artifact |
|---|---|---|
| New article coverage source + all 27 declarations | exit 0, 30.64 s, no errors/warnings, standard axioms only | `article_audit.log`, `article_audit_summary.json` |
| Changed Chapter 7 source + seven relevant declarations | exit 0, 11.06 s, no errors/warnings, standard axioms only | `chapter7_audit.log`, `chapter7_audit_summary.json` |
| Two direct actual-spectrum review theorems | exit 0, no errors/warnings, standard axioms only | `SpectralCheck.lean`, `spectral_check.log` |
| Four assigned TeX files, strict coverage | exit 0, all 294 items final/appropriately open | command below; matching rows in full log |
| Full strict coverage | exit 0, 2529 items | `full_coverage_strict.log` |
| Source hashes, exact anchors, old-item preservation, Chapter 7 unchanged code, first-name ownership/import checks | pass | `static_summary.json`, `reference_findings.json` |

Reproduction commands:

```sh
# From bfgs_lean_article, S as defined above:
export S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env sh -c \
  'LEAN_PATH="$S/coverage:$S/calibrations:$S/twoquadratic:$LEAN_PATH" lean "$S/review_coverage/article_audit.lean"'

# Chapter 7 imports its already-built article dependencies, with no new core imports:
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  "$S/review_coverage/chapter7_audit.lean"

PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env sh -c \
  'LEAN_PATH="$S/coverage:$S/calibrations:$S/twoquadratic:$LEAN_PATH" lean "$S/review_coverage/SpectralCheck.lean"'

# From the repository root:
python3 editorial/lean_coverage/check_coverage.py --strict \
  paper/appendices/hypothesis_examples.tex paper/sections/geometry.tex \
  paper/sections/local.tex companion/chapters/07_H.tex
python3 editorial/lean_coverage/check_coverage.py --strict
```

`run_checks.py` records exact commands, elapsed times, complete axiom lists, and before/after source hashes. No `lake build/update/clean/exe` was run, and no core source/olean was rebuilt. Geometry/Local coverage code was unchanged; their new classifications are cross-references, not new Lean declarations.

## 6. Final PDFs and warning comparison

Compared every page's text with `S/baseline/{paper,companion}.pdf`, rendered the changed pages using `page.get_pixmap(dpi=110)`, and inspected **all** resulting images:

- Paper: baseline 49 pages, current 54; changed pages **6–54**, 49 images. New text is on pages 6, 24, and 49–53. This also checks the reflowed existing pages, figures, tables, and references.
- Companion: 108 pages before and after; changed PDF pages **5, 46–52**, eight images. The caveat is on PDF page 46 / printed page 40; the cited Section 7.6.1 is on PDF page 49 / printed page 43. Page 5 is the updated contents page.
- Every new formula and rational constant is legible. The mixed/full-rank proofs contain the final eligible-pair wording. The proposition/proof page breaks are coherent. Cross-references resolve to the intended definitions, appendix, propositions, corollaries, theorem, and section. No clipping, overlap, missing glyph, or unresolved reference was observed.
- Final `paper/build/master.log`: **0 warnings, 0 overfull, 0 underfull**, same as baseline.
- Final `companion/build/master.log`: **0 warnings, 0 overfull, 2 underfull**, exactly the same two baseline messages (badness 2088 at lines 1–1 and 10000 at lines 33–36). The temporary label-change warning in the first companion latexmk pass is resolved in the final pass.

Reviewed PDF hashes:

- Paper: `9108a1520c91b8af02f722aa852e560784bb23c70bacaece599c7881b420398e`.
- Companion: `b958f4933a34044cd1ab6b26603efb65f81b97ace65bf2dd6212736e0796214c`.

`pdf_summary.json` records baseline/current hashes, page counts, changed-page lists, and warning messages. `visual/` holds all 110-dpi PNGs and extracted page text.

## 7. Completion and handoff

All assigned mathematical, literal-coverage, compilation/axiom, strict-checker, and final-PDF checks were completed. There is no blocked check or unresolved mathematical question within this review scope. The full-package build, package-wide axiom audit/kernel replay, and release/infrastructure integration are the coordinator's subsequent checks.

The fix pass should address **R1** (remaining Chapter 7 navigation ranges) and **R2** (item-first docstring format), then recheck the corresponding coverage metadata. **O1** is optional and comes with a compiled, audited scratch implementation. No new statement or proof needs weakening. All review-created files are confined to `S/review_coverage/`; no review Lean process remains running.
