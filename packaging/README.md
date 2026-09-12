# Portable source archives

Run from a clean committed checkout:

```sh
python3 packaging/make_archives.py
```

The script creates these local delivery artifacts under `dist/`:

- `BFGS_corrected_report_LaTeX.zip`: the corrected report's main LaTeX file,
  bibliography, all chapter and coverage inputs, reference PDF, instructions and
  checksums. This is sufficient for standalone typesetting.
- `BFGS_complete_source_and_verification.zip`: the exact committed repository
  snapshot, including original research sources, Lean sources, pinned dependency
  records, corrected report and all recorded proof/review evidence. A
  self-contained Git bundle and restoration helper support the historical
  baseline comparisons without copying local Git configuration or hooks.
- `ARCHIVES.json`: source commit, archive sizes, hashes and content checks.

Both ZIPs preserve the original filesystem layout beneath the repository's
original folder name, `BFGS-non-smooth/`. For example:

```text
BFGS-non-smooth/
  bfgs_lean_stage1/
    master_report/latex/master.tex
    master_report/latex/chapters/...
    master_report/latex/coverage/...
    master_report/latex/bibliography.tex
    output/pdf/Rigorous_BFGS_Master_Report.pdf
```

The small LaTeX package selects only the files needed for typesetting and the
reference PDF, while retaining each selected file's original path. The complete
package retains every committed path. Neither package flattens the LaTeX tree
or relocates the PDF. Supplemental archive instructions and `_archive/` metadata
are separate from the original source files. Compile by entering
`bfgs_lean_stage1/master_report/latex/` before invoking `latexmk`.

The packager reads `git archive HEAD`, not the working directory recursively.
It rejects a dirty tracked tree, forbidden cache/temporary path components,
compiled artifacts and nonregular committed files. Untracked files, raw `.git`,
`.lake`, `.toolchain`, `.cache`, `tmp` and `audit/scratch` are excluded. The
bundle advertises only the selected release HEAD and its committed ancestors;
unrelated local refs, reflogs and dangling objects are excluded.

Compiler output and historical review logs are evidence, so those tracked files
are retained. Every ZIP member is checked for CRC, SHA-256, size and expected
path. The inventory excludes its own entry to avoid a circular self-hash.
Packaging does not delete anything from the original project.

The complete archive's `ARCHIVE_README.md` explains history restoration and the
read-only report/literature validation commands. Fresh Lean compilation requires
downloading the pinned compiler and dependencies again, and should use a
separate extraction to preserve the delivered evidence. Merely restoring the
archive and checking recorded evidence requires no Lean installation.

Delivery ZIPs and temporary extraction tests are ignored in Git under `dist/`.
The packaging scripts and final validation records are versioned here. A ZIP's
source commit is recorded explicitly; a later commit of packaging-test records
does not change which report and proof sources that ZIP contains.
