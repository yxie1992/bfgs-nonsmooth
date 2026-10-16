# M42 literal Lean coverage — implementation report

**Complete; ready for independent review and a returned fix pass.**

16 October 2026, delegated coverage work on the coordinator's shared WIP,
base `3de9c74`. All 27 named coverage declarations compile and have standard-only
axiom dependencies. Both the three-file and full-repository strict coverage
checks pass. No uncovered item or mathematical discrepancy was identified.

## 1. Deliverables and ownership

Repository files written:

1. `bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean`
   — new, 686 lines, 27 theorems and five explicit non-vacuity examples.
2. `editorial/lean_coverage/register/A_hypothesis_examples.json`
   — new, 22 mechanical items and seven prose items.
3. `editorial/lean_coverage/register/A_geometry.json`
   — 16 appended prose classifications, `prose/044`–`059`.
4. `editorial/lean_coverage/register/A_local.json`
   — four appended prose classifications, `prose/045`–`048`.

Static checks compare every old geometry/local entry and all old register metadata
with `3de9c74`: exactly preserved. The original 109 geometry lines and 442 local
lines match `S/tex_base/` exactly. No old-range relocation or other register/module
resync is required. The final full strict check reports no integration errors.

The dependency source hashes still match the two supplied implementation reports:

| Source | SHA-256 |
|---|---|
| New coverage module | `4d738b9b3d9843a25d540c62dbebe1d86375fb86ac393ce56c79a401e5a345f3` |
| Core `HypothesisExamples.lean` | `39134726105a010df070f544fcba0bb8d186cce212546dafdf9017a3b7ad778a` |
| Core `TwoQuadraticExample.lean` | `cd5e4550d341a44442925692125100e3bb952c1e110d0a75dc8004ee545ba518` |

Core sources and oleans were treated as read-only. Imports are exactly the two
core modules and `BfgsArticle.AdmissibleRunExistence`. No root or other coverage
module is imported. No git mutations or Lake build/update/clean/exe occurred.

## 2. Coverage counts

| Register / scope | LEAN | DEFINITION | PART_OF | PROOF | SAME_AS | NON_CLAIM | Total |
|---|---:|---:|---:|---:|---:|---:|---:|
| New appendix | 12 | 1 | 4 | 6 | 5 | 1 | **29** |
| Geometry additions | 0 | 0 | 0 | 0 | 16 | 0 | **16** |
| Local additions | 0 | 0 | 0 | 0 | 4 | 0 | **4** |
| **All new items** | **12** | **1** | **4** | **6** | **25** | **1** | **49** |
| Full geometry register | 16 | 0 | 0 | 0 | 36 | 10 | 62 |
| Full local register | 45 | 1 | 3 | 8 | 14 | 9 | 80 |

Three-file strict check: **171 items**, all final, no discrepancies or errors.
Full strict check: **2524 items** (668 article, 1856 companion), all final;
the existing 12 `OPEN` items are unrelated previously classified questions.
The full status totals are DEFINITION 192, LEAN 1132, NON_CLAIM 448, OPEN 12,
PART_OF 124, PROOF 91, SAME_AS 525.

All new prose anchors were checked against their exact current line ranges.
All three JSON files are canonical `indent=1, ensure_ascii=False`, with newline.
Every named declaration is cited in the appendix register and in `Audit.lean`.

## 3. Every new declaration and its item

Prefix all names below with `BfgsCoverage.Article.HypothesisExamples.`.
Item prefixes below are `A/hypothesis_examples/`.

| Declaration(s) | Item | Literal content |
|---|---|---|
| `mixed_certificates` | `proposition/art:examples-mixed` | Every `b>0`, all `0<η≤b`, literal objective, convexity, unique attained minimum, compact sublevel, exact radial certificate and `C≥0`. |
| `mixed_smallest_eigenvalue` | same | Least Rayleigh value on `sqNorm v=1` is `2^{-k}`, attained at the unit eigenvector `(0,1)`, and tends to zero. |
| `mixed_history` | same | Objective facts, all certificates and the printed actual-gradient full-BFGS run jointly at `b=2/3`, exact initialization/history/constants, containment, limits and least-Rayleigh limit. |
| `mixed_same_sign_secants` | `disp/003` | Both exact same-sign identities and `(yᵀz)²≤2F(z)t`. |
| `mixed_opposite_sign_secants` | `disp/004` | `S>0`, `t=2(r−u)²+2S`, `yᵀz=2(r−u)r+2|w|`. |
| `mixed_crossing_cauchy` | `disp/005` | Every inequality of the full weighted intermediate chain through `t(2r²+2|w|²/S)`, `2F(z)t`, `2bt`. |
| `mixed_history_scalars` | `disp/006` | Literal `d=2^{-k}`, `Δ=d/3`, `t=2d` on that history. |
| `quadratic_certificates` | `proposition/art:examples-full-rank` | Every `n≥1`, `b>0`, `0<η≤b`, Euclidean `sqNorm/2`, compactness/minimum/uniqueness, exact identity certificate, SPD and rank `n`. |
| `quadratic_history` | same | Every nonzero prescribed start, the same objective/certificates/sublevel and actual full-BFGS history, exact initialization/formulas and convergence. |
| `quadratic_history_decrease` | `proof/002` | Literal `Δ=3d/4` and weak-Wolfe equality for that run. |
| `strict_wolfe_step` | `lemma/art:examples-run-existence` | Exact full-space countable exceptional-set condition, actual gradient, SPD metric, direction `p=-Hg`, positive differentiable endpoint, strict Armijo and strict direction-paired weak Wolfe. |
| `admissible_run_exists` | same | Additional nonstationarity gives an actual infinite run for every differentiable `x₀`, SPD `H₀`, valid pair, with exact initial gradient and constants. |
| `two_quadratic_formula` | `disp/009` | Definition unfolds to the exact printed maximum. |
| `paperRegularAt_iff` | `proposition/art:examples-two-quadratics` | Complete literal open-neighborhood smooth/two-branch predicate expansion. |
| `planarHypotheses_iff` | same | Every field of the native planar record, including actual-subdifferential affine correctness. |
| `finiteMaxHypotheses_iff` | same | Every finite-max record field: objective, branches, representation, contours and original-index positive affine balance. |
| `two_quadratic_objective_geometry` | same | Unique attained minimum, every compact sublevel, exact switching curve, full-space differentiability locus and line specialization `a=c`. |
| `two_quadratic_planar_hypotheses` | same | Literal article conjunction on every positive sublevel, with neighborhood alternative fully written out and `C_aff∩K⊆argmin F`. |
| `two_quadratic_finite_max_hypotheses` | same | Both original branches active, actual gradients `(0,±1)` and full finite-max hypotheses with half weights. |
| `two_quadratic_joint` | same | All objective geometry and universal convergence hold **before** quantifying over all prescribed initial states; every such state has an actual convergent full-BFGS run for the same family. |
| `two_quadratic_tie_determinant` | `disp/010` | The exact determinant of actual branch gradients on the tie curve. |
| `nonradial_runs` | `corollary/art:examples-nonradial-runs` | Every differentiable low start, every SPD matrix, every valid pair: same-state actual run and convergence, plus convergence of every low-start run. |
| `nonradial_initial_value` | same | Full-space derivative and exact `1001/10^6<1/100` at `(1/1000,0)`. |
| `gauge_formula` | `proposition/art:examples-no-step` | The literal three-linear maximum. |
| `gauge_no_step` | same | Full joint objective/initial-state/whole-ray obstruction; no differentiable weak-Wolfe positive endpoint for any `c₂<1`, including beyond the optimizer; no run from those data. |
| `gauge_covered_convergence` | same | The homogeneous convergence theorem applies to every admissible run on the gauge. |
| `gauge_ray_minimizer` | `prose/006` | The ray hits the minimizer at positive length `α=ε`, but no admissible infinite history has those initial data. |

The six proof environments are `PROOF` of their named statements, with core
supporting names recorded. All five proof displays are independently `LEAN`;
the other five displays are four `PART_OF` items and the literal two-quadratic
definition. Undisplayed connecting steps follow the coverage method's proof rule.

## 4. Important literal choices

1. **Arbitrary mixed sublevel retained.** `mixed_certificates` is not restricted
   to `b≥2/3`; only the displayed history uses `b=2/3`. The latter includes all
   its own certificates, avoiding an unrelated witness combination.
2. **Smallest eigenvalue genuinely covered.** The core supplied a singular
   matrix limit; the coverage module proves the attained exact least-Rayleigh
   characterization and geometric limit, and puts it into the joint history.
3. **Printed crossing estimate, not just its consequence.** The new proof uses
   the nonnegative difference identity
   `4((r−u)|w|−Sr)²/S` for the weighted Cauchy–Schwarz comparison, followed by
   `|w|²/S≤|w|` and the sublevel bound. The identities retain arbitrary actual
   endpoint gradients, with the introduced `y,t,S` as variables and their
   defining equations. Both sign cases cover all differentiable endpoints.
4. **Euclidean quadratic convention.** The wrapper explicitly identifies
   `Quadratic.objective` with `‖euclideanVector x‖²/2`, not the Pi norm square.
   Every sign in the article's certificate is accounted for: three by the
   record (`m>0`, `L≥0`, `δ>0`), `C≥0` explicitly, and the exact constants.
5. **Two-quadratic records are transparent.** Three expansion theorems, the
   literal article conjunction and the active-gradient facts make the native
   joint witness inspectable. Geometry and universal convergence are proved
   without any initial-state premise; the actual-history clause then quantifies
   over all prescribed differentiable starts, SPD metrics and valid constants.
6. **Three-quadratic quantifier preserved.** The proof calls
   `objective_exists_admissible_run` for the arbitrary low differentiability
   point and `fullBFGS_explicit_basin` for that same run. The numerical value
   calculation supplements this all-start theorem.
7. **Gauge interpretation.** The entire ray is covered, including the
   nondifferentiable continuation beyond zero. The terminal prose has its own
   theorem proving the ray's positive-length minimizer crossing and the
   absence of a prescribed-state infinite run.
8. **Scope-summary targets.** Every new geometry/local mathematical summary
   has a precise `SAME_AS` target and an explicit note on inherited hypotheses.
   The compact-gradient fact targets `C/02_M/prose/007`: its existing theorem
   states exactly the independent compact-subgradient bound, without requiring
   a certificate or planar geometry. This is a register reference, not a Lean
   import. The printed nonradial summary retains the cited corollary's
   differentiable-low-start qualification; the numerical start witnesses the
   every-matrix/every-pair existence assertion.

## 5. Compilation, audit and strict checks

All Lean processes were sequential, with `LEAN_NUM_THREADS=4`.

| Check | Result | Log |
|---|---|---|
| Final standalone coverage compilation | **PASS**, 6.96 s, zero errors/warnings | `Compile.log` |
| `#print axioms` on every new named wrapper/helper | **PASS**, 27/27, 17.28 s | `Audit.lean`, `Audit.log` |
| Three-file strict coverage | **PASS**, 171 items | `coverage_strict.log` |
| Full strict coverage | **PASS**, 2524 items; no external integration errors | `full_coverage_strict.log` |
| Canonical JSON, exact anchors, old-entry preservation, declarations/citations, imports, forbidden-device scan and axiom-log validation | **PASS** | `validate_static.py`, `Static.log` |

Every axiom result is exactly `[propext, Classical.choice, Quot.sound]`.
No proof placeholder, custom axiom, native decision device, unsafe mechanism,
debug option or linter suppression occurs. `Static.log` records the final
source/TeX/dependency hashes and proves that the audit covers all new names.

### Isolated-import detail

Simply placing the two supplied scratch roots first failed because Lean resolves
the common top-level `BfgsArticle` prefix through the first matching root and
does not search the second root for the other module. The owned scratch overlay
`coverage/BfgsArticle/` contains symlinks to:

- `calibrations/BfgsArticle/HypothesisExamples.olean`;
- `twoquadratic/BfgsArticle/TwoQuadraticExample.olean`;
- the existing `twoquadratic/BfgsArticle/AdmissibleRunExistence.olean` symlink.

It also holds only the newly compiled coverage olean. The two dependency
directories remain read-only. The final commands, from `bfgs_lean_article/`, are
reproducible as follows (logs used `/usr/bin/time -p` around these commands):

```sh
export S=/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/m42_20261016
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=4
lake env sh -c 'LEAN_PATH="$S/coverage:$S/calibrations:$S/twoquadratic:$LEAN_PATH" lean -o "$S/coverage/BfgsArticle/Coverage/Article/HypothesisExamples.olean" BfgsArticle/Coverage/Article/HypothesisExamples.lean'
lake env sh -c 'LEAN_PATH="$S/coverage:$S/calibrations:$S/twoquadratic:$LEAN_PATH" lean "$S/coverage/Audit.lean"'
```

From the repository root:

```sh
python3 editorial/lean_coverage/check_coverage.py --strict paper/appendices/hypothesis_examples.tex paper/sections/geometry.tex paper/sections/local.tex
python3 editorial/lean_coverage/check_coverage.py --strict
python3 "$S/coverage/validate_static.py"
```

Initial diagnostics are preserved in `compile01.log`–`compile04.log` (import
root resolution, followed by local algebra normalization fixes). The final
compile/audit logs above supersede them. A docstring line beginning with
`class of ...` was rephrased because the textual declaration scanner interpreted
it as a spurious declaration named `of`; the final source has precisely the 27
audited names.

## 6. Remaining work / coordinator handoff

No remaining implementation problem, TODO classification, discrepancy, missing
prose item or external resync requirement was found. No core helper is needed
for the added Rayleigh or intermediate-Cauchy assertions; they are proved locally
in the owned coverage module. The core source hashes are unchanged from the
supplied reports, so a later core fix pass should trigger the coordinator's
normal dependency recompilation and recheck.

Next is the independent coverage review, then a returned fix pass if needed.
Root import, package-wide compilation/audits, manuscript integration, generated
indices, TODO bookkeeping and commit/push are the coordinator's integration unit.

## Fix pass

**Completed 16 October 2026: R1 and R2 fixed exactly; optional O1 accepted and implemented.**
This pass began at HEAD `b783e4e6ec283239c80ba4faa1a63c7f669c47ef` after reading
`S/review_coverage/REVIEW.md` in full and the supplied `reference_findings.json`
and independently compiled `SpectralCheck.lean`. The independent review passed
all mathematics and literal correspondence. This section supersedes the initial
report's declaration counts, source hashes and current-check commands/results.

### Dispositions and exact changes

**R1 — fixed, documentation only.** In
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch07H.lean`, corrected exactly
the 18 introductory `Items`-table range cells from `reference_findings.json`.
The pre-insertion `24-28` component stays `24-28`. In
`editorial/lean_coverage/register/C_07_H.json`, changed only the notes of:

- `C/07_H/prose/031`: six shorthand references, to `341-342`, `350`,
  `350-351`, `357-358`, `374-375`, and `375`, for the respective named steps
  `values_dichotomy`, `q_not_bounded_away`, `potential_lower_bound`,
  `reciprocal_summable_of_weighted`, `bounded_away_of_pointwise`, and
  `finite_limit_zero`.
- `C/07_H/prose/058`: the two shorthand ranges now read
  `Lines 588-589: maxLinear_planar_zero_branch_iterates; 589-591:`.

The complete JSON equals the pre-fix JSON with exactly those eight requested
replacements. Every item range, classification and other field is preserved;
`resolved_discrepancies` is exactly preserved. All 84 explicit Chapter 7
file/range citations have the same coordinates as before this pass, so already
resynchronized references were not shifted again.

**R2 — fixed, documentation only.** Moved each existing citation, unchanged,
to the beginning of its declaration's docstring, followed by its original
mathematical description:

| Declaration under `BfgsCoverage.Companion.Ch07H` | Item | Current TeX range |
|---|---|---|
| `maxLinear_affine_free_no_run` | `C/07_H/prose/077` | `companion/chapters/07_H.tex:102-104` |
| `tilt_collinear_no_run` | `C/07_H/prose/078` | `companion/chapters/07_H.tex:104-106` |
| `tilt_two_values_no_run` | `C/07_H/prose/078` | `companion/chapters/07_H.tex:104-106` |
| `maxLinear_line_no_run` | `C/07_H/prose/079` | `companion/chapters/07_H.tex:107-109` |

The existing `TiltNoInfiniteRunQuestion` docstring is preserved. After stripping
Lean comments, **the entire Chapter 7 mathematical code is token-identical to
the pre-fix source**, including all statements, bodies, imports and examples.

**O1 — accepted, evidence strengthening.** Ported the independent review's two
actual-spectrum proofs into
`bfgs_lean_article/BfgsArticle/Coverage/Article/HypothesisExamples.lean`:

1. `BfgsCoverage.Article.HypothesisExamples.mixed_least_spectrum`:
   for every `k`,
   `IsLeast (spectrum ℝ (Mixed.run.H k)) ((1 / 2 : ℝ) ^ k)`.
2. `BfgsCoverage.Article.HypothesisExamples.mixed_spectral_limit`:
   the preceding actual-spectrum statement for every `k`, together with
   `Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0)`.

Both have item-first docstrings citing
`A/hypothesis_examples/proposition/art:examples-mixed`
(`paper/appendices/hypothesis_examples.tex:12-30`). The first proof uses the
same displayed matrices and `spectrum_diagonal`; the second reuses the existing
geometric limit. The existing attained-Rayleigh/eigenvector theorem and
`mixed_history` are preserved exactly. In fact, removing only the two new
declarations leaves **all 27 earlier mathematical declarations and all five
examples token-identical** to the pre-fix module. Its three imports are unchanged.

The existing mixed-proposition register item in
`editorial/lean_coverage/register/A_hypothesis_examples.json` now additionally
cites these two names and explains their direct-spectrum content. No item,
hypothesis, theorem conclusion or status was replaced; no new TeX claim/item
was introduced. The source introduction mentions the two new statements.

### Checks and artifacts

Fix-pass artifacts are under `S/coverage/fix_pass/`. `before/` and `before.json`
capture the pre-fix source/metadata and dependency hashes. The four repository
files written in this pass are the two coverage modules and the two registers
named above. The geometry/local registers, all four corresponding TeX files,
both mathematical-core sources and all three reviewed dependency oleans match
their pre-fix hashes. No TeX changed, so the independent review's PDF evidence
remains applicable.

| Check | Result | Artifact |
|---|---|---|
| Article coverage compile with isolated reviewed dependencies | **PASS**, 17.63 s, no errors/warnings | `article_compile.log` |
| Chapter 7 coverage compile | **PASS**, 11.34 s, no errors/warnings | `chapter7_compile.log` |
| New spectral declarations: signatures and `#print axioms` | **PASS**, 2/2, 3.50 s | `SpectralAudit.lean`, `spectral_audit.log` |
| Four assigned files, strict coverage | **PASS**, 294 items | `assigned_coverage_strict.log` |
| Full strict coverage | **PASS**, 2529 items, no integration errors | `full_coverage_strict.log` |
| Exact R1 replacements, item-first R2 citations, comment-stripped code preservation, canonical JSON, all mechanical/prose/docstring ranges and snapshot guards | **PASS** | `static_checks.log` |

Both new declarations depend exactly on
`[propext, Classical.choice, Quot.sound]`. The earlier unchanged declarations'
completed axiom audit was retained. Every Lean invocation was sequential with
`LEAN_NUM_THREADS=4`; both changed modules were freshly compiled. The owned
`S/coverage` import overlay was used for both compilations and the new audit.
For Chapter 7's existing imports, three additional read-only links in that
overlay point to the already-built `Global.olean`, `Energy.olean` and
`Master.olean`. No reviewed core dependency was rebuilt, and no git mutation or
Lake build/update/clean/exe occurred.

Final hashes:

| File | SHA-256 |
|---|---|
| `Coverage/Article/HypothesisExamples.lean` | `4b805cd70301cb362c0d0867b8a3178d680256eb37316937ac17661c418201dd` |
| `Coverage/Companion/Ch07H.lean` | `7aed2198fed67c059d6c8162977241b4695d9b5b0fbe17699aba0fcff732d9cb` |
| `A_hypothesis_examples.json` | `e6b6d0b88e40d92d5a7ebedee743a8efcf68f3edca48c7409ac0b1cbb24e6c59` |
| `C_07_H.json` | `5023fdca985a890c58906076dd3e631e5afdc270debcc3ec1d1899c68b3e0ba8` |

### Final counts and completion

- Article coverage module: **29 named theorems** (27 reviewed originals plus
  two direct-spectrum theorems), with the original five non-vacuity examples.
- Appendix register: **29 items** — LEAN 12, DEFINITION 1, PART_OF 4,
  PROOF 6, SAME_AS 5, NON_CLAIM 1. O1 does not change these item counts.
- Four assigned registers: appendix 29, geometry 62, local 80, Chapter 7 123;
  **294 items** in total. Their combined statuses are DEFINITION 5, LEAN 149,
  NON_CLAIM 32, OPEN 3, PART_OF 17, PROOF 22, SAME_AS 66.
- Complete M42 addition scope, including the coordinator's five Chapter 7
  items: **54 items** — LEAN 14, DEFINITION 1, PART_OF 4, PROOF 7,
  SAME_AS 25, NON_CLAIM 2, OPEN 1. These are the independent review's unchanged
  classification counts.
- Full repository: **2529 items** (668 article, 1861 companion), with statuses
  DEFINITION 192, LEAN 1134, NON_CLAIM 449, OPEN 13, PART_OF 124, PROOF 92,
  SAME_AS 525. There is no new TODO or DISCREPANCY.

R1, R2 and O1 are fully disposed of. No implementation blocker remains. The
agent is ready for the coordinator's next instruction.

### Verification paragraph for the coordinator's durable records

The M42 coverage fix pass at `b783e4e` resolved review findings R1 and R2 by
correcting exactly 18 Chapter 7 index ranges, eight shorthand references in two
register notes, and four item-first docstrings; Chapter 7's mathematical code,
all item ranges, all 84 explicit file citations and historical resolved
discrepancies were preserved. Accepted O1 added
`BfgsCoverage.Article.HypothesisExamples.mixed_least_spectrum` and
`mixed_spectral_limit`, proving directly that `2^{-k}` is the least element of
the actual real spectrum and tends to zero, alongside the unchanged attained
Rayleigh/eigenvector and joint-history results. Both changed modules compile
without diagnostics; both new declarations use only the standard three axioms.
Canonical JSON and exact item/source ranges pass, as do assigned-file strict
coverage (294 items) and full strict coverage (2529 items). The article module
now has 29 named coverage theorems; the 54 M42 item classifications are unchanged.
No TeX or mathematical-core source/dependency changed in this fix pass.
