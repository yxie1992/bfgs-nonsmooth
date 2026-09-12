# Artifact-validation history

The first `validate.py --write-manifest` attempt rejected the README link to `MANIFEST.json` before creating that file. The assertion was: `Broken local Markdown link ... README.md ... MANIFEST.json`. This was a generator ordering issue, not a missing research result or changed report input.

The validator now creates the manifest after checking the registers and before checking local links. A subsequent ordinary validation checks the delivered manifest without writing it. The final actual output is recorded in `validation.log`. The separate edition-integrity command completed successfully and its actual JSON output is preserved in `edition_integrity.json`; it checks existing compiler/axiom evidence and does not perform a fresh Lean build.

After the user authorized integrating citations into the master report, baseline readers were updated to verify the original report bytes at the recorded Git commit when the working edition differs. The historical BASELINE.json, claim comparisons and original integrity evidence are unchanged. This preserves reproducibility of the historical audit while permitting an explicitly reviewed new edition.
