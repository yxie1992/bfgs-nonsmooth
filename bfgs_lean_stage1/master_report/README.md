# Rigorous corrected master report

The corrected edition integrates the reviewed mathematics with its Lean proofs.
Read [the PDF](../output/pdf/Rigorous_BFGS_Master_Report.pdf) and the
[searchable claim/proof index](PROOF_INDEX.html). The index is a standalone HTML
file; open it in a browser with JavaScript enabled. It includes the exact types,
universe parameters, axioms, source links and project proof dependencies.
Definition source excerpts make named proposition targets inspectable; long
proofs remain available through the complete source links.

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

## Reproduce

Run the complete read-only release validation from `bfgs_lean_stage1/`:

```sh
python3 scripts/verify_rigorous_master_report.py
```

This checks the recorded compiler/axiom evidence, source-to-proof index,
corruption-rejection tests, PDF build and visual record, and exact final artifact
manifest. It requires Python 3 and Node.js. For a fresh Lean build:

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
separately from compiler and text-bound checks.

## Evidence and source correspondence

- [FINAL_REVIEW.md](FINAL_REVIEW.md): release review, evidence and trust boundaries.
- [MANIFEST.json](MANIFEST.json): complete final artifact hashes.
- [render/VISUAL_REVIEW.json](render/VISUAL_REVIEW.json): inspection of the final 92-page PDF.
- [STATUS.json](STATUS.json): exact completion scope and open boundaries.
- [CLAIMS.json](CLAIMS.json): every original source span and its reviewed exports.
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
