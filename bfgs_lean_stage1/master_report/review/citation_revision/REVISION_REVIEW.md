# Citation and attribution revision

This revision implements the requested literature attribution in the corrected
master report. The preceding corrected edition and its literature audit remain
available in Git. The citation baseline is commit
`06ee12f7e7661437b8481fcab3b5bd26cff60130`; the separately frozen literature
comparison baseline is recorded in `literature_audit/BASELINE.json`.

The revision adds 41 localized attribution paragraphs, expands the bibliography
to 38 external works, corrects five pieces of novelty wording, and adds an
attribution chapter to the frontmatter. It credits known special cases and
standard mathematical ingredients, distinguishes neighboring counterexamples
by their assumptions, updates publication details and authorship, and keeps
unresolved priority questions explicit. Similarity to published techniques does
not establish causal provenance for AI-generated text.

The edit ledger now has 114 guarded replacements. Removing the marked
attribution paragraphs and reversing the five wording edits recovers all 14
baseline chapters byte for byte. All 172 original span classifications and
formal export lists, the complete declaration index, all Lean sources, and
pinned toolchain/package inputs remain unchanged. The source map retains the
original research sources and distinguishes bibliographic notes as editorial
assertions; no citation supplies a proof term or an additional mathematical
axiom. There was no new Lean compilation for this citation-only revision.
The release gate checks the existing actual compiler/axiom records against their
recorded input hashes.

The literature validator now reads exact historical report bytes from its
recorded Git commit when the current corrected report has changed. It still
checks every frozen hash and original span location; it does not reinterpret
old comparison records as referring to the new page or line numbers. This
requires the recorded commits to be present in local Git history.

Independent reviews are recorded in
[attribution_peer_review.md](attribution_peer_review.md),
[geometry_attribution_review.md](geometry_attribution_review.md),
[validation_peer_review.md](validation_peer_review.md), and
[visual_peer_review.md](visual_peer_review.md). Bibliographic metadata and
source-access qualifications are reviewed in
[bibliography_review.md](../../authoring/citation_revision/bibliography_review.md).
The geometry review's two small wording corrections were integrated before the
final render. Earlier review hashes identify the exact intermediate snapshots
they reviewed; the final preservation and release checks bind the delivered
edition.

The first two PDF renders failed on a small bibliography line overflow. Their
actual logs and failure summaries are preserved as `render_attempt1*`,
`render_attempt2*` and `latex_attempt*.log`. A paragraph break in the Powell
reference repaired the overflow; warning tolerances were not relaxed. The final
render passed with 98 pages and 53,197 extracted words, no selected TeX warnings,
no empty pages and no words outside page bounds. The system Python lacked
Pillow for visual evidence preparation; the bundled Python with Pillow then
prepared the images successfully.

Two reviewers actually inspected all 98 pages in seven contact sheets and 13
enlarged samples. The exact PDF and image hashes are in
[VISUAL_REVIEW.json](../../render/VISUAL_REVIEW.json). No clipping or overlapping
content was observed. An inherited cosmetic repetition of subsection numbers
in U.5 is disclosed in the visual record. The PDF's edition date reflects the
11 September literature cutoff; UTC execution timestamps record the actual
render and review times independently.

The read-only validations are recorded in `source_proof_index.json`,
`preservation_check.json`, `negative_guards.json`, `index_ui.json`,
`pre_seal_gate.json` and `final_gate.json`. The final gate checks the complete
artifact manifest in addition to the mathematical preservation, source/proof
mapping, existing audit evidence, corruption rejection, index behavior and PDF
records. Old `review/release/` logs and the closed compiler evidence remain
historical records of the preceding edition.
