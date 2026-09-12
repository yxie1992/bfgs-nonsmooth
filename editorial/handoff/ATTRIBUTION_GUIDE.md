# Attribution and prior-work workflow

## Starting point and limits

The corrected `latex.zip` includes an integrated attribution revision and a detailed `bibliography.tex`. It references a separate `literature_audit/` directory that was not part of this ZIP. Locate that directory and its latest records in the repository before recreating work.

The names and keys below are **source-derived starting points**, not a fresh independent literature review. Verify actual primary texts for load-bearing claims, particularly exact theorem numbers, hypotheses, authorship and publication status. Use the version that was actually read. Preserve reported access limits instead of converting them into full-text review claims.

## Organize prior work by its role in the argument

### 1. Classical smooth-BFGS analysis and the matrix foundation

Starting keys: `FND_P76`, `FND_BN89`, `FND_N92`, `FND_JJM24AW`, `FND_JJM26EX`, `FND_JM25`, `FND_CV13`, `FND_Z05`.

Explain the antecedents of trace/determinant and potential arguments. Separate standard Gram, determinant, Schur-complement, and scalar-product tools from the precise adjacent-degree principal-minor inequality and the particular reciprocal consequences proved here. Do not infer novelty of an identity because it has a different notation or a Lean proof.

Do not merge papers on exact line search with those on Armijo–Wolfe. The supplied bibliography explicitly distinguishes such pairs. Preserve that separation when shortening the related-work section.

### 2. Unmodified BFGS on nonsmooth objectives

Starting keys: `LO`, `GL18`, `XW`, `BG`.

The corrected source credits Guo–Lewis for Euclidean-norm convergence and Xie–Wächter for the two-piece finite-escape theorem. Retain these as known special cases/antecedents. Attribute empirical motivation, algorithm specifications, and conditional criticality results to the appropriate sources rather than to a generic list of authors.

For Gebken, distinguish assumed iterate/matrix behavior from statements derived without those assumptions. Recheck exact locators: the corrected bibliography differentiates the published paper from its preprint and gives different numbering.

The author's earlier paper is ordinary prior work for this purpose. Cite it precisely and identify what the new statements extend; do not erase it or imply its established theorem is new.

### 3. Earlier failures and modified methods

Starting keys: `NEG_LO08`, `NEG_LZ15`, `NEG_M04`, `NEG_M07`, `NEG_M14`, `NEG_DAI02`, `NEG_DAI13`, `NEG_AO21`, `NEG_DIAO26`, `YVGS10`, `GR91`.

For each comparison, record the full tuple:

    objective class and regularity;
    full / limited-memory / partitioned / modified method;
    exact / weak-Wolfe / strong-Wolfe / implementation-specific search;
    accepted differentiability, null steps, or other exceptions;
    initialization quantifier;
    global versus local failure;
    failed conclusion (value, stationarity, iterate, finite termination);
    any generic/probability or numerical-robustness assertion.

Use that tuple to compare statements. “There were already BFGS counterexamples” and “there were no convex examples” are both too broad without this review.

The source bibliography includes a very recent preprint comparison under `NEG_DIAO26`; verify availability, date, current version and actual theorem scope before citing it. Do not convert a preprint into a journal article or imply a complete proof audit from an abstract. Likewise, older access-limited sources must remain marked as such.

### 4. Geometry and standard analytic tools

Starting keys: `geom_Lewis2002`, `LL`, `geom_LSS2019`, `geom_DDJ2026`, `geom_LSS2025`, `LW`, `BDLS`, `WW`, `geom_BauschkeCombettes2010`, `geom_Bogosel2023`, `DY`, `NEG_RUMP10`.

Credit VU/partial-smoothness and constant-rank geometry, stratified critical-value arguments, local convex cocoercivity, normal-angle formulas, contraction/root-enclosure methods, and stable-manifold theory where used.

A geometric lemma derived from established machinery may be useful without being a new foundational discovery. The manuscript's affine-critical-value argument should be framed that way unless the completed literature comparison establishes a stronger distinction.

The published Lewis–Liang–Tian author list and the earlier Lewis–Liang preprint are different version records. Do not assign a theorem number from one to the other. Results for bundle/Newton/proximal methods are context, not convergence theorems for unmodified BFGS.

## The attribution ledger

For every load-bearing literature statement, record:

- Stable paper-claim ID and exact manuscript sentence.
- Source key, full bibliographic identity, DOI/arXiv version and actual access path.
- Source theorem/proposition/page locator in that exact version.
- What was read: full relevant proof, theorem statement, abstract, metadata, or secondhand exposition.
- Exact relevant assumptions and conclusion.
- Relationship: exact prior result; known special case; generalization; analogous method; standard ingredient; distinct result; or unresolved priority.
- The difference supporting any novelty wording.
- Date checked and unresolved access or interpretation issue.

The template is intentionally uncompleted. A paper's title is not evidence of theorem content. A “no exact match found” search outcome is not proof of novelty. Prefer restrained phrasing such as “we establish the following statement” over unsupported superlatives.

## Writing the related-work section

Do not copy long audit annotations into the article. Use a compact synthesis:

1. Established positive results and the gap addressed.
2. Earlier failure results and the exact distinction of this construction.
3. Algebraic and geometric tools and what is new in their use here.
4. Formal verification as a companion to the mathematical contribution.

At the point of use, cite a standard theorem with the actual version locator. Introduce our new result immediately afterward with a precise difference. Replace `[SM]`, `[SD]`, etc. by ordinary article/companion cross-references, not fictional independent publications.

Maintain the detailed audit in the companion/repository. The journal bibliography should be clean bibliographic data, not a running diary of searches. Access restrictions can go into the audit and, where they materially limit a comparison, a short honest qualification in the prose.

## Authorship and AI assistance

This work involved assistance with mathematical development, code, and formalization—not merely spelling. Prepare an accurate disclosure from the actual record, naming only tools/versions genuinely known. Distinguish AI research assistance from the Lean kernel's checking role. Do not claim that a formal proof removes human accountability.

Follow the current publisher policy in `JOURNAL_POLICY.md` and obtain human approval of final disclosure, author list and responsibility statements. Do not list an AI system as an author. Do not fabricate affiliations, funding, consent, ORCIDs, or the statement that humans have independently checked every argument.

A possible draft structure, for author review rather than automatic attestation:

> AI-assisted tools were used in [documented activities]. The mathematical statements and proofs were reviewed against the formal development described in Section [reference]. [Author-approved accountability statement required by the selected journal.] The formalization certifies the specified mathematical contracts; it does not certify bibliographic priority or the correctness of every natural-language comparison.

Replace bracketed content with verified facts and author-approved statements before submission. Missing author approval belongs in the author-action file, not a false declaration of completed review.
