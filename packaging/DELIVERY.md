# Validated ZIP delivery

Source snapshot: `1d891fd26627baa06122c8021cb34ad8b85ee392`. The report/PDF and Lean proof sources
are unchanged by packaging. This snapshot includes the reviewed portability fix
for three macOS metadata files accidentally present in the prior artifact seal.

Both ZIPs now preserve the original `BFGS-non-smooth/` folder and every
repository-relative source path. The small package keeps its LaTeX sources at
`bfgs_lean_stage1/master_report/latex/` and its reference PDF at
`bfgs_lean_stage1/output/pdf/`. Archive instructions and `_archive/` metadata are
supplemental; original files are not moved or renamed. Earlier layout validation
records remain historical; the current checks are under `review/original_paths/`.

| Archive under `dist/` | Bytes | Purpose |
|---|---:|---|
| `BFGS_corrected_report_LaTeX.zip` | 1,045,724 | Standalone 30-file LaTeX source, reference PDF and build instructions |
| `BFGS_complete_source_and_verification.zip` | 66,938,517 | Exact committed project, proof/audit evidence and restorable release history |

The complete archive has 3,198 members, including all 3,194 committed files and
four distribution metadata/helper files. Its inventory binds all payload files
by SHA-256. Untracked files, raw `.git`, `.DS_Store`, `.lake`, `.toolchain`, `.cache`,
`tmp`, `audit/scratch` and compiled artifacts are excluded. Recorded compiler and
review logs are preserved as evidence.

At the start of packaging, the working directory occupied approximately 8.5 GB:
`.lake` about 5.9 GB, `.toolchain` 1.5 GB, `.cache` 276 MB and `audit/scratch`
583 MB. These installed dependencies and disposable working files account for
most of its size. Packaging did not delete original files. Only the fresh
packaging-test extraction directories were removed after preserving their logs.

The actual standalone LaTeX compilation returned exit 0 and produced 98 pages,
with no final TeX warnings or overflow. The extracted layout text exactly
matched the reference PDF. Final archive TeX/PDF payloads were independently
checked byte-for-byte against those actually compiled inputs; only archive
metadata changed between the intermediate and final ZIPs.

The updated complete ZIP was extracted independently and its release history
restored under the original folder name. The unchanged restoration helper was
also tested in the prior delivery under both Git default-branch settings
(`main` and `master`). Both historical baseline commits were available. The unmodified public report gate and
literature validator passed without the Lean compiler or dependencies installed
in that extraction. Restoration refused an existing repository without changing
its HEAD. These are checks of delivered source/evidence and packaging, not a
fresh Lean compilation.

See [the archive checksums](review/original_paths/ARCHIVES.json),
[complete-package validation](review/original_paths/complete_validation.json),
[final LaTeX validation](review/original_paths/latex_validation.json), and the
[portability review](review/portability_peer_review.md). The initial failed
extraction and intermediate TeX validation wrapper error remain explicitly
recorded alongside their successful corrections.

The ZIPs are local delivery artifacts in the ignored `dist/` directory. Scripts
and review logs are committed; the later delivery-record commit is separate
from the immutable source snapshot identified inside each ZIP. Use the
[packaging instructions](README.md) to produce archives from a future clean
commit. Restoring downloaded dependencies for a new Lean build requires network
access and can recreate the several-GB installation size.
