# Further skeptical review, 12 September 2026

Baseline: dbe14e9aacacd72d84a4bd9a457bb503e1aee4bc, with clean tracked files. The preceding completed release is preserved in release/history/20260912_narrative. The request was to continue until the paper was satisfactory; the preceding green status was not used as a substitute for a fresh reading.

## Pass 1: mathematical scope and proof completeness

Fresh separate reviews covered the actual-matrix principal-minor/reciprocal/energy chain, inward and moving-planar positive geometry, and both deterministic negative constructions. Reviewers expanded the actual formal contracts and read the printed arguments. The negative review also independently reproduced the printed root, all nine query rows, shape-Jacobian/spectral signs, and scalar interpolation bounds using exact rational diagnostics. These computations are review evidence, not imported proof premises. No material proof gap or overclaim was found in the theorem set. See core_critique, positive_critique and negative_critique MD/JSON.

One introductory summary did omit the bounded-gradient and vanishing-predicted-decrease conditions of the correctly stated reciprocal theorem. This is corrected explicitly. All 31 theorem, lemma, proposition, corollary and definition blocks remain byte-identical to the baseline; statement_preservation.json records the complete comparison. The objective, line search, actual-gradient convention, local versus global scope, counterexample parameter ranges, and different regularity regimes are unchanged.

The proof now identifies the augmented gradient determinant, makes the finite-candidate preimage choice explicit before choosing a stable orbit, and transfers the scalar failure of second differentiability to the branch functions by line restriction. No assumption has been added. The existing middle-update proof was retained without an extra equivalent rank-one display because it already supplies the full algebraic route. Scope review of the actual diff is recorded separately.

The unchanged fourteen article geometry declarations were freshly compiled with the pinned toolchain and subjected to a stricter structural dependency traversal, including mutual inductives and recursor rules. It found the same 26,496-declaration closure and exact theorem types as the preceding audit. All roots agree in type and value with the kernel-checked environment and separately agree with Lean's ordinary axiom collector. Only propext, Classical.choice and Quot.sound occur. This strengthens the explicit audit procedure; it does not report an actual defect in an earlier theorem or establish foundational consistency.

## Pass 2: narrative, novelty and readability

A fresh 47-page editorial reading identified six ranked recommendations in narrative_critique.md. N01 is the summary qualification above. N02 and N06 are closed by consolidating repeated benchmark explanations, deterministic exclusions and verification administration. N04 is closed by matching the theorem reference and removing duplicate proof-heading words in the article. N05 is closed by integrating unpublished references grammatically and citing the local stable-manifold theorem precisely: Dyatlov 2018v1, Section3.5 Theorem3/Remark4 with Section3.1 rescaling. The primary HTML was freshly inspected for this locator and the access limits are recorded in LITERATURE_LEDGER.json.

N03, an optional move of scalar interpolation into an article appendix, was deliberately not selected. The current main-text construction is complete and readable; moving it would not reduce total length and would interrupt the present definition-to-embedding sequence elsewhere. Both purposeful figures and all three tables remain. No main result or proof was moved to the companion. The 46-page article still exceeds the original 30–35-page aim; JOURNAL_FIT.md records the reason and the lack of any claim of editor approval or SIOPT compliance.

## Pass 3: build, visual and reproducibility integrity

Both PDFs build with resolved references and no overfull boxes: 46 and107 pages. During new companion image inspection, the shared appendix exposed a class difference: svjour3 adds an optional proof title, whereas amsthm replaces it. The generated companion now restores its 'Proof of' prefix while keeping the article's nonduplicated heading. This is a documented layout transformation, not a duplicate hand-edited proof.

Final image review and fresh source-archive validation have separate hash-bound records. Until those records pass and the source/release milestones are pushed, this file is a work record rather than a completion receipt. These are AI-assisted author-side reviews, not independent human peer review. Human source/novelty review, authorship metadata, responsibility/disclosure approval and submission/deposit decisions remain reserved.

## Final correspondence refinement

The scalar restriction clause is now also an exact Lean endpoint. The new
`ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction` conjoins
the unchanged full identity-initialized failure target with failure of
Fréchet-derivative differentiability for each of the three actual whitened
branches. Its3theorems/37,525transitive dependencies passed the strict audit;
the article and companion narrative both map to this endpoint. The revised
companion remains107pages; all changed pages were seen and every carried
approval is bound to exact page-image hashes. The article remains46pages with
its complete fresh visual/text approval.

Source/proof milestone7072ac033abb8ac8a1373850142f2fb4cec7f951 was committed.
The first push failed with an HTTP broken pipe and the unchanged remote was
verified. A command-local HTTP/1.1 retry succeeded; `git ls-remote` confirmed
that exact commit. Both failure and success receipts are retained. No force
push, history rewrite, remote change or persistent Git configuration was used.

A further audit-method review found that the old reuse record bound source
inputs and package revisions but did not seal the reused library object bytes.
The new cache binding is designed to record the actual rehashed incremental
build and exact object/source/trace/compiler files, with read-only checks
before and after extraction replay. It preserves the explicit trust in the
compiler, Lake, execution environment and prior cache creation; no clean
Mathlib rebuild or foundational-consistency proof is claimed. Its actual
completion evidence is separate from this description of the method.

Final cache_binding_04 passed: 8,853 objects, all paired source paths, 32,470 cached files, and 7,382 independently recomputed existing Lake output hashes. The ordinary pinned build and the later read-only check both passed. All nine dependency revisions are clean. Seven adverse-input guard tests passed. No successful --rehash or empty-cache build is asserted. All 153 final PDF pages are approved by actual visual review, with unchanged companion pages carried only by exact pixel hashes. The manuscript is satisfactory as an author-review candidate; the current source archive replay and final push remain execution gates.

Final fresh extraction satisfaction_20260912_01 passed all 38 recorded commands. Both final PDFs are byte-identical to the reviewed 46/107-page outputs; all 153 rendered pages and paginated text match, references resolve and no overfull boxes remain. All four supplements were freshly compiled with complete structural/axiom audits and the same reviewed contracts. The exact pinned cache passed before/after byte checks and ordered search-path comparisons. The current 21-check gate and unchanged historical-baseline wrapper passed. Temporary extraction files were removed. Source freeze 573306b is pushed; the archive is 119,243,872 bytes, SHA-256 64633451de2c70cb1b97af49abc5ac65a9d549460d4e597e100a88685403aaba. The manuscript and reproducibility work are complete; only recording the final release commit/push remains in this execution.
