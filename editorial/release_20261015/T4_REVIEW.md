# Independent review of the October correspondence revision (T4 rows), and its fix pass

Independent review of the 77 rows of `CHANGES.json` (release run, step 4), with the receipt, the refreshed
component reviews and the claim ledger, by an agent, Claude in OpenCode, on 15 October 2026, on scratch clones of
`5b5c273` with the uncommitted revision. The review text below is unchanged; the scratch paths it names (`S/...`,
`clone/`, `tools/`, `tests/`, `fixes/` and the logs) are not kept. The fix pass, by the agent that wrote the rows, is
the last section.

---

# Independent review of the October correspondence revision (T4, release-run step 4)

Reviewer: Claude (OpenCode subagent), 15 October 2026, 08:39–09:40 PDT. Brief: `S/prompts/review_t4.md` plus the
coordinator's five points. R = `/Users/yxie/Projects/bfgs-nonsmooth`, HEAD `5b5c273`, revision uncommitted (six
modified files and the untracked receipt; their sha256 equal the row author's FINAL_REPORT, recorded in
`sha256_R_start.txt` and again at the end: unchanged). S = `/private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode`;
everything cited below is in `S/review_t4/`. Nothing in R was edited and no writing script ran there; the first
`git status`/`git log` in R ran without `GIT_OPTIONAL_LOCKS=0` (at most a stat refresh of `.git/index`, no content
change), every later git query of R used it. No Lean, no `lake`; the September checkout was not touched. Work clone:
`clone/` (`git clone --no-hardlinks R`, the seven files copied, scratch commit `a1bd4d9`).

## Verdict: sound with fixes — 2 must-fix rows (C072, C031), 4 should-fix rows (C059, C062, C036, C042), 2 should-fix items outside the rows

The table is right in substance. Its 77 rows are exactly the 77 changed units (`--propose`: 77 matching, nothing
stale, uncovered or unresolved); every unit key and change type is right; every changed piece inside a unit was traced
to the commit that made it and to a correction item whose TODO text (and reader point R-x-y) describes it: no change
lacks an item and no item is unrelated. The Lean statements of the changed claims (list under task 1) were read and
state the new TeX with its hypotheses and quantifier order. Receipt, refreshed reviews and ledger change only where intended; `--check` passes
and fails on every negative test. Defects are in the review texts and one coverage list: C072 claims that a cited item
carries the slopes sentence of Appendix D, but none does (its item is not cited); C031 claims a Lean dependency that
cannot exist; C059, C062 (scope review), C036 and C042 are incomplete or imprecise. All proposed fixes were applied in
the scratch clone: `--write`, assembler, `--check` PASS; every test suite still passes (`fixes/`).

## Findings and exact fixes

All row fixes are scripted in `fixes/apply_fixes.py` (run from the repository root; `--optional` adds O-1 to O-3);
results: `fixes/CHANGES.must_should.json`, `fixes/CHANGES.all_fixes.json` (diff `fixes/CHANGES.all_fixes.diff`).
Then `refresh_correspondence.py --write`, `(cd editorial && python3 assemble_claim_ledger.py)`, `--check`.

### Must fix

**M-1, C072** (`appendix:paper/appendices/lower_curvature.tex`). Line 26, "Use the slopes $g_0,g_1,g_2$ and the
function $G$ of Section~\ref{art:failure}" (M35, R-F-5), lies in no other unit (`tools/outside.py`: the lines of the
appendix outside every other unit are 13–16, 26, 62–63, 65, 67, 76, 81, 219), so C072 is its only row, and its review
says these edits are "carried by the cited items". For line 26 none is cited. The item that carries it is
`A/lower_curvature/disp/001` (DEFINITION, $Q_\mu=\tfrac\mu2\|x\|^2+G$; note "Corrected on 15 October 2026 (M35): the
sentence introducing the display takes g₀, g₁, g₂ and G from Section art:failure"). The other lines are carried by cited
items (prose/010, 011, disp/004, prose/008, 041, 042, 009, 013). Fix:
- `coverage`: insert after `A/lower_curvature/prose/011`:
  `{"item": "A/lower_curvature/disp/001", "status": "DEFINITION", "sha256": "04e584a0520c7a34"}`;
- `principal_lean`: insert `"BfgsCoverage.Article.LowerCurvature.quadratic_def"` after `"BfgsVerification.LUniform.Admissible"`;
- `review`: replace `(e.g. LowerCurvature.branch_second_differentiability, LUniform.Admissible, normalized_coordinates_def)`
  by `(e.g. LowerCurvature.branch_second_differentiability, LUniform.Admissible, quadratic_def for the slopes and G of Section 6 in Q_mu, normalized_coordinates_def)`.
The FINAL_REPORT sentence on these edits ("covered by the complete-text row C072, which cites the items carrying them")
becomes true with this fix.

**M-2, C031** (`proof:art:minor-hierarchy`). The review says "its Lean proof uses MatrixAlgebra.gram_compression as the
text does". False: `Coverage/Article/Energy.lean` imports no coverage module (rule 6 of the coverage method) and never
mentions `gram_compression`; `Energy.minor_hierarchy` is proved by the library's `principalMinorHierarchy`, which uses
`BFGSCompression.compressed_inverseBFGS_bound_generic` (`PrincipalHierarchy.lean:68`; the register note of
`A/energy/proof/003` says so). Fix:
- `principal_lean`: `["BfgsCoverage.Article.MatrixAlgebra.gram_compression", "BfgsVerification.BFGSCompression.compressed_inverseBFGS_bound_generic", "BfgsCoverage.Article.Energy.minor_hierarchy"]` (all reachable from `A/energy/proof/003`);
- `review`: replace `The argument is unchanged; its Lean proof uses MatrixAlgebra.gram_compression as the text does, and Energy.minor_hierarchy states the theorem.`
  by `The argument is unchanged; Energy.minor_hierarchy states the theorem, and its Lean proof (the library's principalMinorHierarchy) uses the library's compression bound BFGSCompression.compressed_inverseBFGS_bound_generic where the text cites Lemma art:gram-compression, which MatrixAlgebra.gram_compression states.`

### Should fix

**S-1, C059** (`root:exposition.N2.active_gradients`). R-A-4 replaced "whitening" three times; the review names two, and
the third ("(or $\lambda_3A^Te_2\ne0$ after that change)", line 33) is register item `A/verification/prose/015` (LEAN,
note "Corrected on 15 October 2026 (M38): 'after that change' for 'after whitening'"), touched by the changed lines but
not cited (`tools/gaps.py`). The Lean name is already right (`whitened_active_gradients` covers lines 30–34). Fix:
`coverage` insert after `A/verification/prose/013`: `{"item": "A/verification/prose/015", "status": "LEAN", "sha256": "2084e6d816495932"}`;
`review`: replace `of Appendix D (M38, R-A-4).` by
`of Appendix D, to which "after that change" (before "after whitening") also refers (M38, R-A-4).`

**S-2, C062** (`root:exposition.N2.secants`): the record keeps the scope review "The certified orbit changes among
distinct fixed slopes", the wording M41 (R-A-11) removed from the article because the orbit is given by the
stable-manifold proposition, not certified numerically. Fix (point 3 below): add
`"scope_review": "Subtract the existing actual endpoint gradients mu*x+g_i and mu*(x+s)+g_j to obtain y=mu*s+(g_j-g_i). The perturbed orbit of Proposition art:quadratic_failure changes among distinct fixed slopes; its convergence implies s tends to zero. This describes that orbit, not a generic switching failure."`
and in `review` replace `which names the orbit meant (M41, R-A-11);` by
`which names the orbit meant (M41, R-A-11), and the record's scope review says "The perturbed orbit of Proposition art:quadratic_failure" instead of "The certified orbit";`.
(`--write` then changes this record's `scope_review` in `root_contract_review.json` and the record's `review` in the ledger, one line each.)

**S-3, C036** (`proof:art:planar-field`): "PlanarGeometry.transversality_contradiction … state the renamed displays":
display `disp/010` is stated by `transversality_limits`; `transversality_contradiction` is the next, undisplayed step
(it derives `False`, `PlanarGeometry.lean:1270`). Fix: in `principal_lean` replace
`BfgsCoverage.Article.PlanarGeometry.transversality_contradiction` by `BfgsCoverage.Article.PlanarGeometry.transversality_limits`
(in disp/010's `lean`); in `review` replace `PlanarGeometry.transversality_contradiction, branch_cocoercivity` by
`PlanarGeometry.transversality_limits, branch_cocoercivity`.

**S-4, C042** (`proof:art:radial-equivalence`): "radialNumerator_swap and Global.curvature_eq_errors state the added
identities": only $(g-h)^Tr_x=T-N$ was added; `curvature_eq_errors` states $T=D_F(z,x)+D_F(x,z)$, an unchanged step
(`Global.lean:444`, lines 68–69). Fix `review`: replace
`RadialCertificate.radialNumerator_swap and Global.curvature_eq_errors state the added identities and Global.radial_equivalence the theorem.`
by `RadialCertificate.radialNumerator_swap states the added identity (g-h)^T r_x=T-N, Global.curvature_eq_errors the identity T=D_F(z,x)+D_F(x,z) that the case split uses, and Global.radial_equivalence the theorem.`

**S-5, register note (outside the rows; before step 6, since T3 binds registers and ledger):**
`C/research_story/prose/029` (cited by C057) says "…as the article's abstract (A/master/prose/009) says it, except that
the abstract still has "at the accumulation point" (M30, open for the article)". False since `6e06960` (no
"accumulation point" left in `paper/master.tex`); the ledger copies the note. Fix: delete the clause from ", except
that" to "open for the article)", then `check_coverage.py --strict` and the assembler. No T4 re-run needed (notes are
not hashed; the receipt does not pin registers or the ledger).

**S-6, `editorial/verify_release_inputs.py` without PDFs** (point 4): fix now, with the tested patch below.

### Optional

- **O-1, C058**: the next clause's subject changed ("it does not subsume" → "they do not subsume"); its item
  `C/research_story/prose/018` (SAME_AS `C/07_H/prose/044`) is touched but not cited. Fix: add
  `{"item": "C/research_story/prose/018", "status": "SAME_AS", "sha256": "fe8e3056df82ac8f"}`,
  `principal_lean` `["BfgsCoverage.Companion.Ch07H.two_piece_finite_termination"]` (required once the item is cited),
  review end `…is not subsumed, now with the alternatives as its subject, is unchanged in substance (C/research_story/prose/018, SAME_AS C/07_H/prose/044, Ch07H.two_piece_finite_termination).`
- **O-2, C066** and **O-3, C052**: say in the review that the changed lines lie in no register item (texts in
  `apply_fixes.py`, F7, F8; see point 2).
- **O-4, register notes with another M number than the TODO**: `A/lower_curvature/disp/005` "(M41): comma at the end
  of the display" (R-F-7 is M39; row C010 rightly cites M39); `A/energy/disp/025` "(M39): m P̄⁻¹" and
  `A/energy/proof/005` "(M35, M39) … m P̄⁻¹" (R-B-11 is M38; row C022 rightly cites M38).
- **O-5, receipt text**: `"normalization": "All whitespace removed; no notation aliases."` (`refresh_correspondence.py`
  l. 1114) predates MF3/OP8: `norm()` keeps one space ending a control word before a letter, and control spaces.
  Proposed: `'Whitespace removed, except one space that ends a control word before a letter and a control space; no notation aliases.'`
  The script is pinned by the receipt: only together with a `--write`.
- **O-6**: `companion/PROOF_CORRESPONDENCE.html` shows no October row ids (the ledger does; SF6 asked the ledger only).
- **O-7, test suites**: `tooling/t4_negative_tests.sh` cases 3 (`unlisted_proof`) and 6 (`unlisted_algorithm`) now fail
  through the stale-row path, since all 28 proofs and the algorithm are listed rows. An unlisted-edit test needs an
  unchanged unit, e.g. the passage at `failure.tex` "for the same candidate length" (`tests/review_negatives.sh`).

## Answers to the coordinator's five points

**1. C005, C030, C072 cite both LR-P3d ("Paper understates the Lean result…") and M6: keep both; no fix.** The net
diff from `3e8b5c6` contains two distinct changes. (a) The range: Proposition `art:quadratic_failure`, the appendix
opening and the persistence step of Lemma `art:lower_hyperbolic` now cover every admissible pair instead of
$c_1=10^{-4}$, $c_2=1/2$. That is LR-P3d (`5476ba7`), whose "Done" text names exactly these three places. (b) The
uniformity: state, neighbourhood and orbit chosen before the pair ("for all admissible pairs at once", "the same run",
"chosen before the pair"). That is M6 (`5cd2cf8`), whose text for the proposition only says that it "now chooses its
initial state before the pair", which presupposes (a). Neither text alone describes the net change; P3d's own
intermediate wording is gone, but its range is in the final text. P3d's parts that M6 reverted (copy step with fixed
constants) are rightly not cited (C049). The third-pass item "Lower-curvature failure for every admissible pair at once."
restates M6 and need not be added.

**2. C052, C054, C066: consistent with the README rule and honest; no register item to split or add.** The rule's
second clause ("when register items cover the changed lines, at least one of them is cited") is empty when no item
covers them, and every cited item lies in the unit; the tool applies it the same way. C052: lines 192–193 are the lead-in
of display (26); `A/failure/disp/010` (LEAN, `Failure.cone_orbit`, for exactly $0<c_1\le1/3$, $c_1<c_2<1$, read in
Lean) carries the range, and its note records the M32 correction of that sentence: the right item. C054: `disp/016`'s
note says "With lines 241 and 246-247", and `disp/017` (`lower_plateau_bi`, every $\ell$, $\ell=0$ included, read in
Lean) certifies the $\ell=0$ sentence: right. C066: line 36 is a question; the change is the figure reference (M35,
R-A-10). `A/geometry/prose/016` is a sound choice: the register item of the figure
(`A/geometry/figure/art:gradient-geometry`, outside the unit, so not citable) names prose/009, 010 and 016 as the items
covering the drawn labels, the right panel's "Certified nonstationary seed" among them. The coverage method does not ask for items for questions or lead-ins
(proofs: undisplayed connecting steps; the display item states the lead-in's hypothesis). For transparency, O-2/O-3
add one clause to each review.

**3. C062: replacement scope review** (S-2): "Subtract the existing actual endpoint gradients mu*x+g_i and
mu*(x+s)+g_j to obtain y=mu*s+(g_j-g_i). The perturbed orbit of Proposition art:quadratic_failure changes among distinct
fixed slopes; its convergence implies s tends to zero. This describes that orbit, not a generic switching failure."
Tested: `--write`/`--check` PASS; the root record and the ledger record change in this field only.

**4. `verify_release_inputs.py` without PDFs: fix now.** Reproduced: `FileNotFoundError` at l. 390
(`sha(ROOT/d['pdf'])`), exit 1, no `release_integrity.json`, all other results lost (fail-closed; the line dates from
September). The M-1/M-2 fixes need a new `--write` anyway, which re-pins the script at no extra cost. Patch
(`fixes/vri_pdf_fix.diff`):

```diff
 for d in read('editorial/logs/document_checks.json')['documents']:
- record(d['document']+' PDF matches successful resolved, overflow-free build',sha(ROOT/d['pdf'])==d['sha256'] and not d['errors'] and not d['overfull_warnings'],{'pages':d['pages'],'sha256':d['sha256']})
+ details={'pages':d['pages'],'sha256':d['sha256']}
+ try:matches=sha(ROOT/d['pdf'])==d['sha256']
+ except OSError as error:matches=False;details['error']=type(error).__name__+': '+str(error)
+ record(d['document']+' PDF matches successful resolved, overflow-free build',matches and not d['errors'] and not d['overfull_warnings'],details)
```

Tested in the clone: with PDFs (after `build.sh`) the JSON output is identical to the unpatched script's (22/23 PASS);
without PDFs both PDF checks are recorded FAIL with the error, the other 21 results are kept, the JSON is written, exit 1;
then `--write`, assembler, `--check` PASS (the receipt pins the new hash). If the coordinator prefers not to touch
reviewed tooling now, record instead, under "Release receipts are now stale" of `TODO_LEAN_REVIEW.md`: "- [ ]
`editorial/verify_release_inputs.py` stops with FileNotFoundError at the PDF check (l. 390) when the PDFs are not built,
before writing `editorial/logs/release_integrity.json`, so the other results are lost (fail-closed; the run builds first).
Fix: record the check as FAIL with the error (patch in the T4 row review); the receipt of T4 pins the script, so
`--write` and the assembler follow."

**5. The adapted test copies do not weaken the tests.** Reproduced in my clone: originals 17/18 and 8 ok/5 bad;
adapted 18/18 and 13/13. The negative copy changes only case 5's edit (current anchor of C066 instead of the September
one; same expected failure "Current anchors do not resolve"); the original's failure was a precondition failure
(`py_sub` asserts the absent September anchor, nothing is edited, `--check` passes). Scenarios: A' exercises an
unresolved anchor of an already rewritten row (C066 reported without a current change, re-proposed as stale under its
own id, write, check, record anchor); B' sets `scope_review` on C066 explicitly (the original set it on "the last row",
now macro row C077, hence "Only a root row may replace a scope_review"); C' is the original C on an unchanged root unit
(skeleton row, change type `anchor`); D and E are unchanged. One path of the original A was no longer exercised: a
first-time lost anchor whose passage text changed (skeleton row → stale → change `changed`). I added it as scenario A''
(`tests/scenario_A2x.sh`, on `root.introduction.mechanism`): 6/6 ok. See also O-7.

## The brief's tasks

**1. Rows.** Method: `tools/dossier.py` computes, with the script's own `unit_specs`/`compute_units`/`nhash`, every
unit at the eight commits from `3e8b5c6` to `5b5c273` and the word diff per commit (`dossier.json`); commit → item:
`5476ba7` LR-P3d, `721c324` M1–M5, `5cd2cf8` M6, `613cb77` M7–M11, `14085d0` companion (M8, W39), `6e06960` M30–M41;
each chunk was matched against the TODO text and the reader findings (`READING_*.md`, `TRIAGE.md`).
`tools/gaps.py` lists, per row, the unit's items that are touched by the changed lines or carry a "Corrected" note but
are not cited; `tools/outside.py` the appendix lines outside other units; `tools/decl.py` prints Lean statements.
Results: unit keys and change types right (74 `changed`, 3 `added` macros); correction items right for every row (no
change without an item, none unrelated); coverage: right file, final status, current hash, in the unit, own item for
statement/display/float/proof rows (tool-checked), plus M-1, S-1, O-1; Lean: read the statements of
`Failure.failure_polyhedral`, `cone_orbit`, `seed_cycle`, `trial_table`, `positive_interval_derivatives`,
`seed_matrices_steps`, `NegativeLower.local_failure_lower`, `LowerCurvature.lower_hyperbolic`,
`quadratic_failure_initial_point` (and its proof from `LUniform.uniform_global_failure`), `copy_runs_from_one`,
`lower_plateau_bi`, `Verification.seed_ray`, `perturbed_orbit_secants`, `whitened_active_gradients`,
`Master.centered_representation_needs_containment`, `Energy.reciprocal_sum_superlinear_of_minimizer`, `run_bounds`,
`minor_hierarchy`, `Global.nonradial_example_condition_fails`, `curvature_eq_errors`,
`RadialCertificate.radialNumerator_swap`, `Geometry.benchmark_centered_global`, `mixed_inward_remainder`,
`Ch13L.branch_regularity`, `PlanarGeometry.transversality_limits`/`_contradiction`,
`AdmissibleBFGSRun.steps_tendsto_zero_of_strict_contour`: each states the new TeX with its hypotheses (range of
$(c_1,c_2)$, order of quantifiers: objective, starts, orbit and neighbourhood before the pair; initial point in $V$;
$t\ge0$; $\ell\ge1$ resp. every $\ell$). Also checked: macro rows against the macro code (the unstarred
`\preprintcite` prints the same text; LL18, JM25v2 were unused at `3e8b5c6`); Figure 2's ratios against
`figures/cycle_trials.tex` (22/4.6, 2.5/4.2, 23/21). Edits outside every unit (`outside_all.txt`) all have a recorded
item (D1 for the date line). Per-row table: `rows_table.md` (68 OK, 2 must, 4 should, 3 optional).

**2. Receipt and refreshed reviews** (`tools/reviewdiff.py`, against `5b5c273`): positive — only
`article_sha256` (6 files), locations, one `article_statement` (art:planar-max), proof locations, two deduction anchors
(C067, C071) and annotations (21 statements, 2 displays, 5 deductions); negative — `article_file_sha256` (4 files),
`line`, proof start/end lines and passage hashes, annotations (43 labels); root — `article_file_sha256` (7 files), one
anchor (C066), 13 locations, annotations (12 records); each review gains `october_correspondence_revision`. All other
fields, including every immutable September subtree, are equal (as JSON values; `--check` also compares the bytes)
to `5b5c273`, which equals `3e8b5c6`. Receipt:
status PASS, 77 rows; `script_sha256`, manifest, `CHANGES.json`, 18 active inputs, 2 companion inputs,
`verify_release_inputs.py`, `assemble_claim_ledger.py`, `active_tex_sources.py`, `extract_items.py` and the three outputs
equal the current file hashes (the README's list); 25 statements, 45 displays, 1 float, 2 passages, 9 macros, 14
root/deduction passages preserved; 29 immutable subtrees (O-5 on its normalization text).

**3. Ledger** (`tools/ledgerdiff.py`): only locations, 3 anchors, proof locations, `october_revision` on 75 article
and 3 companion frontmatter records (receipt path right), `october_revision_changes` inside 5 deduction reviews.
Every row id except C020, C072–C077 (no review record, by design) appears; counts unchanged (119 records, 2475 items,
3225 names). The HTML changes in 23 locations only.

**4. Negative tests** (clone `a1bd4d9`; `tests/review_negatives.sh`, log `review_negatives.log`): 29/29 fail as
expected — rows dropped (C036, C072, C077, C071: "Unlisted change" / "Current anchors do not resolve"); coverage hash
changed (C036, one hex digit of C005): "Coverage item hash differs"; principal names of another item, swapped between
rows, emptied; one character in a listed statement, in the slopes sentence (stale C072), in passage C052, in C056's
companion line, in a listed macro, a control-word merge in C022 (stale); one character in an unlisted passage,
display, macro ("Unlisted change"); rows for unchanged units, wrong change type; coverage outside the unit, statement row
without its own item, only an untouched item; unknown/reworded Lean-review title; `scope_review` on a non-root row;
review edited or pinned checker edited without `--write` (stale receipt). Pass after `--write`, by design (README
"Limits"): an unrelated but existing correction item (C001 → W1), an irrelevant but reachable principal name, a row
reduced to one touched item (C063 with only prose/003, although prose/006 and prose/009 carry other changes), an edit
outside every unit (Figure 1 caption "excludes zero" → "contains zero"); `t4_adversarial.py` likewise A4, A11, A11b.
Reused suites: adapted negatives 18/18, adapted scenarios 13/13, A'' 6/6, `t4_adversarial.py` all expected failures
(A1, A2, A5–A10b, A12, A13, A16 ×10, A17) and A15 deterministic. All suites pass again on the fixed table.

**5. `verify_release_inputs.py` in the clone:** without PDFs: crash (point 4). After `bash editorial/build.sh`
(6 s, 49 + 108 pages): 22/23 PASS — the three "Reviewed source contracts" checks PASS; "Reused Lean cache binding"
PASS in source-only scope (nothing linked); FAIL only "October Lean evidence bound to the frozen sources" (audit of
`9f03d7c`, Lean files changed since), as expected until step 6. Same 22/23 with all fixes and the patch applied.

## Tests run

| Test | Result |
|---|---|
| `--check` on the clone of R's state | PASS (77 rows) |
| `--propose` | 77 matching, 0 stale/uncovered/unresolved/unmatched |
| `tests/review_negatives.sh` | 29/29 expected FAIL; 4 documented limits pass after `--write` |
| adapted `t4_negative_tests` / original | 18/18 / 17/18 (case 5 precondition) |
| adapted `t4_scenarios` / original | 13/13 / 8 ok, 5 bad (September anchor) |
| `tests/scenario_A2x.sh` (new path) | 6/6 |
| `review_tooling/t4_adversarial.py` | all expected FAIL; A4, A11, A11b pass by design; A15 deterministic |
| `verify_release_inputs.py` without PDFs / after `build.sh` | crash / 22/23 (Lean evidence FAIL, expected) |
| patched `verify_release_inputs.py` without / with PDFs | 20/23 recorded, JSON written / output identical to unpatched |
| all fixes + patch: `--write`, assembler, `--check`, `check_coverage.py --strict`, `generate_companion.py --check` | PASS, exit 0, PASS |
| all suites on the fixed table (branch `final`, `4efcb34`); the two negative suites again on `final2` (`1224afe`, final optional texts); must+should table alone (`ms_check`) | as above; 29/29 and 18/18; `--write`, `--check` PASS |

Files: `REVIEW.md`, `PROGRESS.md`, `rows_table.md`, `dossier.json`, `outside_all.txt`, `tools/`
(`rc.py`, `dossier.py`, `show.py`, `gaps.py`, `outside.py`, `outside_all.py`, `decl.py`, `reviewdiff.py`,
`ledgerdiff.py`), `tests/` (scripts and logs), `fixes/`, `clone/` (scratch branches; `final2` = every fix + patch).

## Appendix: per-row verdicts

"Changed at": the commits at which the unit's normalized text changed; a later commit may have reverted an edit, e.g. LR in C049 (LR = `5476ba7` LR-P3d, M1-5 = `721c324`, M6 = `5cd2cf8`, M7-11 = `613cb77`, comp = `14085d0`, M30-41 = `6e06960`). LR-P3d = `TODO_LEAN_REVIEW.md: Paper understates the Lean result for the global lower-curvature failure.`

| Row | Unit | Changed at | Correction items | Coverage (status) | Verdict |
|---|---|---|---|---|---|
| C001 | `statement:art:failure_polyhedral` | M30-41 | M32 | failure/corollary/art:failure_polyhedral (LEAN) | OK |
| C002 | `statement:art:local-failure-lower` | M6, M30-41 | M6, M41 | negative_lower/theorem/art:local-failure-lower (LEAN) | OK |
| C003 | `statement:art:lower_hyperbolic` | M6, M30-41 | M6, M38, M39 | lower_curvature/lemma/art:lower_hyperbolic (LEAN) | OK |
| C004 | `statement:art:planar-max` | M30-41 | M39 | local/corollary/art:planar-max (LEAN) | OK |
| C005 | `statement:art:quadratic_failure` | LR, M6, M30-41 | LR-P3d, M6, M33, M39 | lower_curvature/proposition/art:quadratic_failure (LEAN) | OK |
| C006 | `statement:art:seed_cycle` | M1-5, M7-11, M30-41 | M1, M2, M11, M38 | failure/lemma/art:seed_cycle (LEAN) | OK |
| C007 | `display:art:closure_identity` | M30-41 | M39 | seed_certificate/disp/010 (LEAN) | OK |
| C008 | `display:art:inward-to-radial` | M1-5, M30-41 | M3, M39 | global/disp/007 (LEAN) | OK |
| C009 | `display:art:lower_return` | M1-5 | M3 | lower_curvature/disp/006 (DEFINITION) | OK |
| C010 | `display:art:lower_return_substep` | M30-41 | M39 | lower_curvature/disp/005 (DEFINITION) | OK |
| C011 | `display:art:mixed-inward-remainder` | M30-41 | M39 | geometry/disp/001 (LEAN) | OK |
| C012 | `display:art:query_box` | M30-41 | M39 | seed_certificate/disp/013 (LEAN) | OK |
| C013 | `display:art:root_arithmetic` | M30-41 | M39 | seed_certificate/disp/004 (LEAN) | OK |
| C014 | `display:art:seed_query_bounds` | M1-5 | M1 | failure/disp/009 (LEAN) | OK |
| C015 | `display:art:shape_certificate` | M30-41 | M39 | lower_curvature/disp/008 (LEAN) | OK |
| C016 | `display:art:upper_local_model` | M1-5 | M1 | failure/disp/024 (LEAN) | OK |
| C017 | `float:art:cycle-figure` | M30-41 | M39 | failure/figure/art:cycle-figure (NON_CLAIM) | OK |
| C018 | `float:art:regularity-map` | M1-5, M6, M30-41 | M4, M6, M30, M39 | failure/table/art:regularity-map (SAME_AS), failure/prose/058 (SAME_AS) | OK |
| C019 | `float:art:trial_table` | M7-11 | M11 | failure/table/art:trial_table (LEAN) | OK |
| C020 | `algorithm:line_search` | M30-41 | M34 | failure/prose/071 (SAME_AS) | OK |
| C021 | `proof:art:centered` | M30-41 | M34, M39, M41 | global/proof/003 (PROOF) | OK |
| C022 | `proof:art:certificate` | M30-41 | M35, M38, M39 | energy/proof/005 (PROOF), energy/disp/025 (LEAN) | OK |
| C023 | `proof:art:failure_polyhedral` | M30-41 | M39 | failure/proof/001 (PROOF) | OK |
| C024 | `proof:art:gram-compression` | M30-41 | M34, M38, M39 | matrix_algebra/proof/001 (PROOF), matrix_algebra/disp/006 (LEAN) | OK |
| C025 | `proof:art:homogeneous` | M30-41 | M39, M41 | global/proof/005 (PROOF) | OK |
| C026 | `proof:art:homogeneous-examples` | M30-41 | M39 | global/proof/006 (PROOF) | OK |
| C027 | `proof:art:local-centered` | M30-41 | M39 | local/proof/004 (PROOF) | OK |
| C028 | `proof:art:local-failure` | M30-41 | M39 | failure/proof/003 (PROOF) | OK |
| C029 | `proof:art:localization` | M1-5, M30-41 | M3, M39 | local/proof/001 (PROOF), local/disp/001 (LEAN), local/disp/002 (LEAN) | OK |
| C030 | `proof:art:lower_hyperbolic` | LR, M1-5, M6, M30-41 | LR-P3d, M3, M6, M38, M39, M41 | lower_curvature/proof/001 (PROOF), lower_curvature/disp/010 (LEAN), lower_curvature/disp/011 (LEAN) | OK |
| C031 | `proof:art:minor-hierarchy` | M30-41 | M35, M39 | energy/proof/003 (PROOF) | **must M-2** |
| C032 | `proof:art:mixed-benchmark` | M30-41 | M39 | global/proof/004 (PROOF) | OK |
| C033 | `proof:art:nonradial-example` | M30-41 | M39 | local/proof/008 (PROOF) | OK |
| C034 | `proof:art:planar-cluster` | M30-41 | M34, M39 | local/proof/005 (PROOF) | OK |
| C035 | `proof:art:planar-convergence` | M30-41 | M39 | local/proof/006 (PROOF) | OK |
| C036 | `proof:art:planar-field` | M1-5, M30-41 | M3, M38, M39, M40, M41 | planar_geometry/proof/001 (PROOF), planar_geometry/disp/010 (LEAN), planar_geometry/disp/015 (LEAN), planar_geometry/disp/017 (LEAN), planar_geometry/disp/018 (LEAN) | should S-3 |
| C037 | `proof:art:planar-max` | M30-41 | M39 | local/proof/007 (PROOF) | OK |
| C038 | `proof:art:plq` | M30-41 | M39 | local/proof/003 (PROOF) | OK |
| C039 | `proof:art:polyhedral` | M30-41 | M34, M38, M39 | local/proof/002 (PROOF), local/disp/004 (LEAN) | OK |
| C040 | `proof:art:quadratic_failure` | M1-5, M6, M30-41 | M3, M6, M33, M38, M39, M40, M41 | lower_curvature/proof/002 (PROOF) | OK |
| C041 | `proof:art:radial-convergence` | M30-41 | M34, M39 | global/proof/002 (PROOF) | OK |
| C042 | `proof:art:radial-equivalence` | M1-5, M30-41 | M3, M34, M35, M39, M41 | global/proof/001 (PROOF) | should S-4 |
| C043 | `proof:art:reciprocal-growth` | M1-5, M30-41 | M3, M34, M39 | energy/proof/004 (PROOF), energy/disp/017 (LEAN), energy/disp/020 (LEAN) | OK |
| C044 | `proof:art:reference-energy` | M30-41 | M39 | energy/proof/002 (PROOF) | OK |
| C045 | `proof:art:root_certificate` | M30-41 | M39 | seed_certificate/proof/001 (PROOF) | OK |
| C046 | `proof:art:run-invariants` | M30-41 | M39 | energy/proof/001 (PROOF) | OK |
| C047 | `proof:art:seed_cycle` | M30-41 | M34, M38, M39, M41 | seed_certificate/proof/002 (PROOF) | OK |
| C048 | `proof:art:upper_scalar_lemma` | M30-41 | M34, M39 | failure/proof/002 (PROOF) | OK |
| C049 | `passage:all_query_copy_induction_and_one_fixed_identity_normalization` | LR, M6, M30-41 | M6, M33, M39, M41 | lower_curvature/prose/027 (LEAN), lower_curvature/prose/028 (LEAN), lower_curvature/prose/029 (LEAN) | OK |
| C050 | `passage:finite_rational_query_certificate_argument` | M1-5, M30-41 | M1, M38, M39 | seed_certificate/disp/015 (DEFINITION), seed_certificate/disp/013 (LEAN), seed_certificate/prose/010 (LEAN) | OK |
| C051 | `passage:four_branch_strong_convexity_regularity_minimizer_and_Hessian_proof` | M30-41 | M41 | lower_curvature/prose/022 (LEAN) | OK |
| C052 | `passage:infinite_actual_trial_tree_induction_from_the_finite_certificate` | M30-41 | M32 | failure/disp/010 (LEAN) | optional O-3 |
| C053 | `passage:objective_regularity_and_local_model_before_the_main_induction` | M1-5 | M1 | failure/disp/024 (LEAN) | OK |
| C054 | `passage:scalar_regularity_and_plateau_proof` | M30-41 | M41 | lower_curvature/disp/016 (LEAN), lower_curvature/disp/017 (LEAN) | OK |
| C055 | `root:art:positive-outcomes` | M30-41 | M31, M39 | geometry/table/art:positive-outcomes (NON_CLAIM), geometry/prose/027 (SAME_AS), geometry/prose/029 (SAME_AS), geometry/prose/031 (LEAN), geometry/prose/032 (SAME_AS) | OK |
| C056 | `root:companion.lower.actual_branch_regularity` | M30-41 | M30 | 13_L/prose/083 (LEAN) | OK |
| C057 | `root:companion.story.negative` | comp | M8, M30 | research_story/prose/029 (SAME_AS) | OK |
| C058 | `root:companion.story.positive` | comp | W39 | research_story/prose/017 (NON_CLAIM) | optional O-1 |
| C059 | `root:exposition.N2.active_gradients` | M7-11, M30-41 | M8, M38 | verification/prose/012 (LEAN), verification/prose/013 (LEAN), verification/prose/017 (LEAN) | should S-1 |
| C060 | `root:exposition.N2.homogeneity` | M7-11 | M9 | verification/prose/004 (LEAN) | OK |
| C061 | `root:exposition.N2.partition` | M30-41 | M41 | verification/prose/008 (SAME_AS) | OK |
| C062 | `root:exposition.N2.secants` | M30-41 | M41 | verification/prose/019 (LEAN) | should S-2 |
| C063 | `root:root.abstract.three_contributions` | M1-5, M7-11, M30-41 | M5, M7, M8, M30, M41 | master/prose/003 (SAME_AS), master/prose/004 (SAME_AS), master/prose/006 (SAME_AS), master/prose/009 (SAME_AS) | OK |
| C064 | `root:root.energy.budget_interpretation` | M7-11 | M10 | energy/prose/012 (LEAN) | OK |
| C065 | `root:root.geometry.mixed_ridge` | M30-41 | M35, M39 | geometry/prose/004 (LEAN), geometry/disp/001 (LEAN) | OK |
| C066 | `root:root.geometry.seed_balance` | M30-41 | M35 | geometry/prose/016 (LEAN) | optional O-2 |
| C067 | `deduction:1` | M30-41 | M35 | global/prose/016 (NON_CLAIM), global/prose/019 (LEAN) | OK |
| C068 | `deduction:10` | M30-41 | M31, M39 | geometry/prose/029 (SAME_AS) | OK |
| C069 | `deduction:2` | M30-41 | M41 | global/prose/024 (LEAN) | OK |
| C070 | `deduction:3` | M30-41 | M39 | local/prose/011 (NON_CLAIM) | OK |
| C071 | `deduction:7` | M30-41 | M38 | local/prose/027 (LEAN) | OK |
| C072 | `appendix:paper/appendices/lower_curvature.tex` | LR, M1-5, M6, M7-11, M30-41 | LR-P3d, M3, M6, M8, M30, M32, M33, M35, M38, M39, M40, M41 | lower_curvature/prose/010 (LEAN), lower_curvature/prose/011 (SAME_AS), lower_curvature/disp/004 (DEFINITION), lower_curvature/prose/008 (DEFINITION), lower_curvature/prose/041 (DEFINITION), lower_curvature/prose/042 (DEFINITION), lower_curvature/prose/009 (LEAN), lower_curvature/prose/013 (DEFINITION), lower_curvature/proposition/art:quadratic_failure (LEAN), lower_curvature/lemma/art:lower_hyperbolic (LEAN) | **must M-1** |
| C073 | `appendix:paper/appendices/seed_certificate.tex` | M1-5, M30-41 | M1, M34, M38, M39, M41 | seed_certificate/proof/002 (PROOF), seed_certificate/disp/015 (DEFINITION), seed_certificate/prose/010 (LEAN), seed_certificate/disp/004 (LEAN), seed_certificate/disp/010 (LEAN), seed_certificate/disp/013 (LEAN) | OK |
| C074 | `macro:\bfgs@@preprintcite` | added | M40 | — (macro row) | OK |
| C075 | `macro:\bfgs@preprintcite` | added | M40 | — (macro row) | OK |
| C076 | `macro:\bfgsdefinepreprint` | added | M40 | — (macro row) | OK |
| C077 | `macro:\preprintcite` | M30-41 | M40 | — (macro row) | OK |

---

## Fix pass

By the agent that wrote the rows (Claude in OpenCode), 15 October 2026, in the repository at `5b5c273` with the
uncommitted revision, then tested in a fresh scratch clone with the new files committed (not kept). Each change below
was checked against the TeX, the register items and the Lean files before it was applied. The resulting
`CHANGES.json` is byte-identical to the reviewer's tested `CHANGES.all_fixes.json` (must, should and optional row
fixes), and `editorial/verify_release_inputs.py` to the reviewer's patched version.

| Finding | What was changed, or why not | Rows / files |
|---|---|---|
| M-1 | Coverage `A/lower_curvature/disp/001` added (DEFINITION, `04e584a0520c7a34`; its note records the M35 change of the slopes sentence), principal name `BfgsCoverage.Article.LowerCurvature.quadratic_def`, and the review names `quadratic_def` for the slopes and G of Section 6 in Q_mu. | C072 |
| M-2 | Principal names `MatrixAlgebra.gram_compression`, `BfgsVerification.BFGSCompression.compressed_inverseBFGS_bound_generic`, `Energy.minor_hierarchy`; the review now says that the Lean proof is the library's `principalMinorHierarchy`, which uses that compression bound where the text cites Lemma `art:gram-compression`. Checked: `Coverage/Article/Energy.lean` imports no coverage module; `minor_hierarchy` applies `principalMinorHierarchy`, which calls `compressed_inverseBFGS_bound_generic` (`PrincipalHierarchy.lean:68`). | C031 |
| S-1 | Coverage `A/verification/prose/015` added (LEAN, `2084e6d816495932`, the third "after that change"); the review mentions it. | C059 |
| S-2 | `scope_review` of `root.exposition.N2.secants` replaced by the reviewer's text ("The perturbed orbit of Proposition art:quadratic_failure changes among distinct fixed slopes; …"); the review says so. After `--write`, the root record and its ledger record change in this field only. | C062 |
| S-3 | `transversality_limits` (it states display `disp/010`, `PlanarGeometry.lean:1210`) replaces `transversality_contradiction` (the next, undisplayed step) in the principal names and the review. | C036 |
| S-4 | The review now says that `radialNumerator_swap` states the added identity (g-h)^T r_x=T-N and `curvature_eq_errors` the unchanged identity T=D_F(z,x)+D_F(x,z) (`global.tex:68-69`) that the case split uses. | C042 |
| S-5 | Note of `C/research_story/prose/029` in `editorial/lean_coverage/register/C_research_story.json`: the clause "except that the abstract still has "at the accumulation point" (M30, open for the article)" is deleted (the abstract says "at the minimizer" since `6e06960`); canonical JSON (`indent=1`, `ensure_ascii=False`), one line changed. `check_coverage.py --strict` exit 0; the assembler then changed the item's coverage record in the ledger and one line of `PROOF_CORRESPONDENCE.html`. | register |
| S-6 (point 4) | `editorial/verify_release_inputs.py`: the reviewer's 4-line patch. Without built PDFs the two PDF checks are recorded FAIL with the error and the report is written (20/23 in the clone; before: `FileNotFoundError`, no report); with the PDFs its output is identical to the unpatched script's (22/23). The receipt pins the new hash. | script |
| O-1 | Applied: coverage `C/research_story/prose/018` (SAME_AS `C/07_H/prose/044`, `fe8e3056df82ac8f`), principal name `BfgsCoverage.Companion.Ch07H.two_piece_finite_termination`, and a clause in the review. | C058 |
| O-2 | Applied: the review says that the changed line, a question, lies in no register item, and why `A/geometry/prose/016` is cited. | C066 |
| O-3 | Applied: the review says that the changed lead-in lines lie in no register item and that `A/failure/disp/010` carries the range. | C052 |
| O-4 | Not applied: the notes of `A/lower_curvature/disp/005` ("M41" for R-F-7, an M39 point) and of `A/energy/disp/025` and `A/energy/proof/005` ("M39" for R-B-11, an M38 point) are in registers outside the files of this fix pass; the rows cite the right items (C010: M39; C022: M38). Left to the coordinator. | none |
| O-5 (release point B) | Applied: the receipt's `normalization` text in `refresh_correspondence.py` now says what `norm` does (whitespace removed, except that whitespace after a control word and before a letter stays one space and a control space stays a backslash and one space; no notation aliases). The README's "Units" paragraph and the script's docstring already said so; the key `equal_after_whitespace_removal` of the preserved units is kept. | script |
| O-6 | Not applied: `PROOF_CORRESPONDENCE.html` lists no October row ids; the assembler is outside the files of this fix pass, and the ledger carries the ids (SF6 asked for the ledger). | none |
| O-7 | The row author's adapted negative tests gain case 3b, an edit of the unchanged negative-review passage at `failure.tex` "for the same candidate length" (expected "Unlisted change"); cases 3 and 6 still test the stale-row path. | tests |
| Point 1 | Kept: C005, C030 and C072 cite LR-P3d and M6. | none |
| Point 2 | Kept: the coverage of C052, C054 and C066 (with the clauses of O-2 and O-3). | none |
| Point 3 | See S-2. | C062 |
| Point 5 | Scenario A'' is now part of the row author's adapted scenarios and was rerun. | tests |
| Release point A | `README.md`, "Release host": run `validate_archive.py` from the workspace without `--lean-cache-root`; that option expects a complete `bfgs_lean_stage1` directory (its frozen sources, Lake files and dependency checkouts are compared with the extraction), and the APFS copy holds only `.lake` and `.toolchain`. | README |
| README contents | `CHANGES.json` (77 rows), `mapping_refresh.json` and this file are listed; the count of the final table is noted. | README |

Checks in the repository after the fixes: `refresh_correspondence.py --propose` 77 rows matching, nothing stale,
uncovered or unresolved; `--write` PASS (25 statements and 45 labeled displays unchanged; 77 listed changes);
`(cd editorial && python3 assemble_claim_ledger.py)` (119 article records, 2475 coverage items, 3225 Lean names);
`--check` PASS; `check_coverage.py --strict` exit 0; `generate_companion.py --check` PASS. Compared with the
revision before the fix pass, the positive and negative reviews are unchanged, the root review changes in C062's
`scope_review` only, and the ledger in that record's `review` and in the note of `C/research_story/prose/029`.

Tests in a fresh scratch clone with every changed file committed: `--check` PASS; `verify_release_inputs.py` without
PDFs 20/23 with the report written; `bash editorial/build.sh` regenerates chapters, shared appendix and ledger byte
for byte (only the three build logs change); `verify_release_inputs.py` 22/23, the three "Reviewed source contracts"
checks PASS, only "October Lean evidence bound to the frozen sources" fails (audit of `9f03d7c`; until step 6),
output identical to the first pass; `--write` and the assembler leave the tree unchanged; adapted negative tests
19/19 (with 3b); adapted scenarios 18/18 (A', B', A'', C', D, E, clean tree); the reviewer's negative suite 29/29,
with its 4 documented limits passing after `--write`, by design.
