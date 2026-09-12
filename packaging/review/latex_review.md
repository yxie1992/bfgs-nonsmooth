# Standalone LaTeX archive review — intermediate snapshot

**PASS for the intermediate archive identified below.** A subsequent complete-package seal correction may rebuild the ZIP at a later commit. This record does not certify that later ZIP until its manifest and TeX/PDF payloads are independently matched to this compiled sample.

- Archive: `dist/BFGS_corrected_report_LaTeX.zip`
- Source commit: `70a60d4e627a7897e3f820397d57d71d0de785e1`
- Size: **1,043,963 bytes**
- SHA-256: `d40aafbe5573eafca73d16713ad0271cb9901bedc5d365a6ab38af415ede6de0`

The review used its own fresh extraction under `dist/`. All 33 ZIP members passed CRC, unique safe-path, regular-file-mode and exact manifest/SHA-256 checks. The archive contains exactly 30 TeX sources (main document, bibliography, 14 chapters and 14 coverage tables), the reviewed PDF, README and inventory. Every TeX source and the PDF matched its byte content at the recorded Git commit. All 29 TeX input targets resolve internally; no external figure or BibTeX input is needed.

The actual command `latexmk -pdf -interaction=nonstopmode -halt-on-error master.tex` completed with exit code **0** in approximately three seconds. The final TeX log contains no unresolved references/citations, selected warnings, overfull boxes or underfull boxes. Both compiled and reference PDFs have **98 pages**. Their `pdftotext -layout` outputs are byte-identical, SHA-256 `911cf367680875e67d6e90239ef8677c50d0e870e8ccf3875990cb56325c078e`.

The bounds check covers **53,197 extracted words** and found no empty pages or words outside page bounds. The first wrapper encountered 57 XML-disallowed control characters emitted by Poppler for mathematical glyphs. That failed wrapper record is retained in `latex_validation_attempt1.json`. The subsequent bounds-only check uses the report renderer's documented replacement with U+FFFD in an in-memory parsing copy; it changes neither PDF nor raw tool output. Compilation and text comparison had already passed and were not rerun or relabeled.

Exact commands, execution times, exit codes, output hashes and results appear in `latex_validation.json`. Raw command outputs and the final TeX log are retained as `latex_*.log`; `latex_bounds_recheck.py` reproduces the corrected bounds parsing from those outputs. Only this review's temporary extraction was removed after preserving the logs. No source, archive, reference PDF, Lean proof or other agent's directory was modified.

This is a compilation, packaging and text/bounds check. It is not a new Lean audit, an external-paper proof verification, or an independent visual inspection of every newly compiled page.
