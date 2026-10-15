# Line-by-line reading of the article, 15 October 2026

Step 2 of the plan in `AGENTS.md`, after the Lean coverage was complete. Six reader
agents (Claude in OpenCode), each with one group of files, read the article line
by line on a copy of commit `c8db802`, before the corrections M7–M11. All line
numbers in the reports are those of that commit. The readers checked every proof
step, hypothesis, reference, symbol and number (recomputed with exact arithmetic
where possible), compared the statements with the Lean coverage registers, and
looked at the rendered pages of the PDF built from that commit. They ran no Lean
and changed no file.

| Report | Files |
|---|---|
| `READING_A.md` | `master.tex` (title, abstract), `sections/introduction.tex`, `statements/*.tex`, `sections/geometry.tex` (with `figures/gradient_geometry.tex`), `sections/verification.tex`, `bibliography.tex`, `preprint_references.tex` |
| `READING_B.md` | `sections/energy.tex`, `appendices/matrix_algebra.tex` |
| `READING_C.md` | `sections/global.tex` |
| `READING_D.md` | `sections/local.tex`, `appendices/planar_geometry.tex` |
| `READING_E.md` | `sections/failure.tex` (with its figures), `appendices/seed_certificate.tex` |
| `READING_F.md` | `appendices/lower_curvature.tex` |

Each finding (`R-<reader>-<n>`) gives the place, the quoted text, a category
(error, gap, hypothesis, reference, notation, number, language, typesetting), a
severity (major, minor, cosmetic), an explanation, the exact replacement with the
number of occurrences of the old text, and the register items concerned. No reader
found a major error. Paths starting with `$S/` refer to the readers' scratch
directory, which is not kept.

`TRIAGE.md` holds the coordinator's decision on every finding. The accepted
findings are grouped as M30–M41 in `TODO_MANUSCRIPT_REVIEW.md`, which tracks how
they are applied.
