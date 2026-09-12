# Journal-policy snapshot and editorial consequences

Checked 12 September 2026 against the official pages below. Recheck before final formatting or submission. This is a limited authoring-policy check, not submission authorization or an exhaustive policy audit. Journal-specific instructions take precedence over generic publisher pages and sample supplement templates.

## Official facts relevant to this handoff

### Mathematical Programming

The journal encourages concision without stating a general regular-article page cap in this section. It excludes extended text, mathematical proofs and code from journal-published Supplemental Material. Separate Additional Material can be supplied to help referees but is not reviewed or published by the journal. The page specifies a 150–250-word abstract and requires documentation of substantive LLM use. Its LaTeX section contains a journal-specific template override: inspect the complete instructions, not just the generic template recommendation.

Source: https://link.springer.com/journal/10107/submission-guidelines
Relevant headings: “MANUSCRIPT LENGTH AND ONLINE SUPPLEMENTAL MATERIAL,” “Title Page,” and “Text / Additional Information.”

### SIAM Journal on Optimization

SIOPT states a 25-page policy in SIAM format, with longer papers exceptional. Its editorial policy says it does not accept supplements except when requested during review, and does not publish them with the article. Author instructions require an abstract of at most 250 words, inline figures, and keywords/MSC codes.

Sources:
- https://epubs.siam.org/journal/siopt/editorial-policy
- https://epubs.siam.org/journal/siopt/instructions-for-authors

Do not confuse SIOPT with SICON, SIMA, SIMODS or the generic SIAM supplement template.

### SIAM AI-use policy

The official policy is version 2.0, effective May 2026. It requires human authorship/accountability, disclosure of substantive AI use in Acknowledgements or Declarations, and the responsibility statement specified there. It expressly addresses theorem/proof creation, code, citations and reproducible figures—not just prose editing. Authors must review the cited work and remain responsible for mathematical and computational content. Human approval is needed for the manuscript's attestations.

Source: https://epubs.siam.org/artificial-intelligence

### SIAM macro source

Retrieve the current official package rather than copying an old class filename from a prior project. The general author page supplies the download and documentation; the selected journal's policy governs which parts apply.

Source: https://epubs.siam.org/journal-authors

## Editorial consequences for this project

These are recommendations derived for this project, not additional publisher rules:

1. Make the main article proof-complete for the results it advertises. Put essential technical proofs in the article's own appendices when needed.
2. Treat the complete companion report, formal source and audit as an archival repository/research document—not automatically as a journal supplement or as material referees must validate separately.
3. Default to a Mathematical Programming-style regular article for the broad unified story. An initial 30–35-page editorial budget is a planning choice, not a declared journal limit.
4. Prepare a separate SIOPT feasibility note if relevant. A longer exception must be identified honestly. Do not label a long document compliant merely because it uses a SIAM class.
5. If the selected full proof set cannot fit a readable paper, narrow the article's contribution set while preserving other incomparable results in the companion. Do not remove a key lemma and write only “see companion.”
6. Cite a stable archival release when authorized. Do not mint a DOI, post a preprint, create a public repository, submit materials, or contact editors without the author's separate decision.
7. Keep an editable author-review disclosure and metadata/action list. Unknown affiliations, funding, conflicts, consent and repository URLs are not facts to invent.
8. Explain overlaps among article, companion, previous preprints and the author's prior paper according to the selected journal's actual instructions.

## Record the final policy decision

The repository's `editorial/JOURNAL_FIT.md` should record the target, exact official URLs and access date, chosen template/version, actual page count, proof location strategy, companion status, AI/reproducibility statement status, and genuine author actions. Any deviation needs a reason; no self-review can guarantee editorial acceptance.
