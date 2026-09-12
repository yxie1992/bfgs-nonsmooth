# Rigorous corrected master report

The corrected edition integrates the reviewed mathematics with its Lean proofs.
Read [the PDF](../output/pdf/Rigorous_BFGS_Master_Report.pdf) and the
[searchable claim/proof index](PROOF_INDEX.html). The index is a standalone HTML
file; open it in a browser with JavaScript enabled. It includes the exact types,
universe parameters, axioms, source links and project proof dependencies.
Definition source excerpts make named proposition targets inspectable; long
proofs remain available through the complete source links.

Portable LaTeX and complete source/evidence ZIPs can be produced with
`python3 packaging/make_archives.py` from the repository root; see
[the archive instructions](../../packaging/README.md). The release manifest
excludes macOS `.DS_Store` files and Python cache directories, which are local
metadata rather than report or proof artifacts.

The claim register covers all **14 modules, 172 original spans and 4,323 original
chapter lines**. Its **3,087 distinct linked exports** lead to **8,249 indexed
declarations** in their complete project dependency closure. These index counts
are distinct from the full audit's **9,781 safe declarations**, including
**7,954 theorems**, across the main and supplemental modules. Definitions,
hypotheses, mixed evidence passages and explicit open questions are classified
separately from proved assertions.

The permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. The audit rejects custom mathematical axioms, `sorryAx`, missing
dependencies and unsafe/partial artifacts reachable from a safe declaration.
It includes private and generated declarations missed by the old namespace-only
inventory. This identifies the actual foundations used; it does not prove the
consistency of Lean or those foundations. See [the exact audit scope](audit/AUDIT_COVERAGE_AND_LIMITATIONS.md).

Original research sources and the closed milestone 19/20 evidence are preserved.
The corrected edition discloses false unrestricted formulas, missing
qualifications, replacement examples and alternative formal proof routes.
Unsupported historical execution claims are withdrawn. Explicit research
questions remain questions, not theorems certified by this edition.

## Citation and attribution revision

The current 98-page edition adds **41 attribution notes** and makes **five
corrections to unqualified novelty wording**. Its bibliography contains **38
external works** (**53 keys**, including 15 internal topic labels). Its ledger now contains **114
guarded edits**. The comparison notes distinguish established results, proof
techniques and neighboring theorems; they are editorial scholarship, not
additional assertions certified by Lean. The affine-fiber selector's exact
publication priority remains unresolved.

Removing the notes and reversing the five wording corrections recovers all 14
preceding mathematical chapters byte-for-byte. Every span's formal export list
and the complete declaration index are unchanged. No new Lean compiler run was
needed or performed for these citation-only changes; the delivered earlier
compiler and axiom evidence remains the proof evidence. The revision's checks,
reviews and rendering attempts are recorded in
[review/citation_revision/](review/citation_revision/). Earlier release logs
retain their historical dates and scope.

## Reproduce

Run the complete read-only release validation from `bfgs_lean_stage1/`:

```sh
python3 scripts/verify_rigorous_master_report.py
```

This checks the recorded compiler/axiom evidence, source-to-proof index,
corruption-rejection tests, citation preservation, PDF build and visual record,
and exact final artifact manifest. It requires Python 3, Node.js and the full
Git history. The immutable preservation comparison reads the preceding edition
at commit `06ee12f7e7661437b8481fcab3b5bd26cff60130`; an exported source archive
or shallow clone lacking that commit is insufficient. The citation check can
also be run alone:

```sh
python3 scripts/verify_report_attributions.py
```

For a fresh Lean build:

```sh
bash scripts/bootstrap.sh
python3 master_report/audit/run.py --check
python3 master_report/audit/run.py --run
python3 scripts/build_rigorous_master_report.py --check
```

`--check` reads the delivered compiler evidence; `--run` performs a new pinned
build and all-declaration audit in a new timestamped directory. The original
bootstrap/central checker writes its historical output paths, so preserve closed
evidence before using that route in the delivered checkout. The new standalone
audit leaves the closed records unchanged. Perform fresh runs in a separate
checkout when you also want to validate the delivered seal: adding
`master_report/audit/runs/` changes the sealed file inventory. The delivered
manifest intentionally rejects such an altered artifact tree until a new release
is reviewed and sealed.

To assemble and render the edition:

```sh
python3 scripts/build_rigorous_master_report.py
python3 scripts/render_rigorous_master_report.py --raster
```

The renderer requires `latexmk`, `pdflatex`, `pdfinfo`, `pdftotext` and
`pdftoppm`. It writes the final PDF under `output/pdf/`, actual build logs under
`master_report/render/`, and temporary page images under `tmp/pdfs/master21/`.
Its fixed publication timestamp makes PDF metadata reproducible; actual
execution times are recorded independently. Visual inspection is documented
separately from compiler and text-bound checks. The authored attribution notes
are already incorporated in the guarded edit ledger. Do not rerun
`scripts/apply_report_attributions.py` on this edition: it is the recorded,
one-use migration from the baseline, not a report assembly step.

## Evidence and source correspondence

- [FINAL_REVIEW.md](FINAL_REVIEW.md): release review, evidence and trust boundaries.
- [MANIFEST.json](MANIFEST.json): complete final artifact hashes.
- [render/VISUAL_REVIEW.json](render/VISUAL_REVIEW.json): inspection record bound to the current 98-page PDF.
- [STATUS.json](STATUS.json): exact completion scope and open boundaries.
- [CLAIMS.json](CLAIMS.json): every original source span and its reviewed exports.
- [BIBLIOGRAPHIC_NOTES.json](BIBLIOGRAPHIC_NOTES.json): the 41 editorial source
  comparisons, explicitly separated from Lean assertions.
- [authoring/citation_revision/BASELINE.json](authoring/citation_revision/BASELINE.json):
  the immutable preceding edition and preservation hashes.
- [review/citation_revision/](review/citation_revision/): current attribution,
  preservation, index, render and final gate evidence.
- [SOURCE_MAP.json](SOURCE_MAP.json): exact old/new edits and full character maps.
- [DECLARATION_INDEX.json](DECLARATION_INDEX.json): checked types and complete
  project dependency closure for the indexed claims.
- [BUILD_INPUTS.json](BUILD_INPUTS.json): all inputs affecting textual assembly.
- [audit/](audit/README.md): actual pinned compiler and axiom evidence, exact
  copied supplemental sources, and the public reproduction runner.
- [latex/master.tex](latex/master.tex): editable generated LaTeX edition.

`edits/` and `authoring/` are the authored editorial inputs. The assembly tool
rejects ambiguous anchors, missing exports, orphan edits, missing project
dependencies and altered source hashes. Python and the HTML index do not supply
mathematical proof results to Lean.
