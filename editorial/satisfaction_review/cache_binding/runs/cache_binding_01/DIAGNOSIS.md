# Preserved failed rehash attempt

The actual `lake --rehash build BfgsVerification` failed on the pinned
ProofWidgets `widgetJsAll` extra dependency. No successful rehash build or
cache seal is claimed for this run.

The pinned ProofWidgets checkout tracks `widget/package-lock.json.hash` as
15032582431581979733. Rehashing the unchanged lockfile produced
110023375396192760. The diagnostic using pinned Lake's
`computeTextFileHash` confirms the latter value directly. The rehash attempt
changed only that tracked sidecar in the dependency's Git status. Its exact
original HEAD bytes were restored, with the diff and before/after receipts
retained; the package then had a clean Git status. No JavaScript output or
trace was invented or changed to make the build pass.

The current JS `lake.trace` is byte-identical to `./js/lake.trace` in the
already cached official ProofWidgets4.tar.gz release. Its SHA-256 is
37380981568d4047ae48c2b08decaebf0fcccb24f5f040a10634a10f250f522d and its
recorded dependency hash is 2956727721270439600. Restoring this same release
trace would not repair the rehash freshness check.

**Diagnostic limitation:** the standalone `WidgetHashDiagnosis` scripts also
print a simple fold of the listed input hashes under the label “JS target
dependency hash.” This label is too strong: it does not reproduce the full
Lake Job trace aggregation. In particular, the fold with the captured pinned
sidecar is 7637830097726777816, which does not equal the release trace. Those
fold values are retained as failed diagnostic reasoning and are not used by
the cache-binding validator. Only the direct lockfile hash, actual compiler
error, source build rule, tracked-file diff and byte comparisons support the
diagnosis. The subsequent successful alternative must have a separate run.

The selected alternative preserves all pinned sources and build guards. It
runs the ordinary pinned Lake build and independently recomputes the binary
Lake hash of every enumerated `.olean`, comparing every present
`.olean.hash` before and after that build. A SHA-256 manifest additionally
binds objects, paired sources/traces/hash files, compiler executables and
the actual command evidence. This is trusted incremental provenance, not a
clean source rebuild or independent kernel checking of every imported object.
