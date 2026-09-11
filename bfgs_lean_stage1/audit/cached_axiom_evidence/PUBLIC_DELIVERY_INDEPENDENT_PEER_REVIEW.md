# Independent review of the public cached-axiom delivery

PASS, 11 September 2026. The 36-file public bundle and its four scripts were
read and independently tested in a private fixture. This review supplements
the earlier case-by-case comparison of `CachedAxiomGraph` with pinned Lean
4.19.0 `Lean.Util.CollectAxioms`. No main file was edited and no duplicate long
ordinary audit was run.

The reviewed static evidence manifest hash is
`f3b0e685c910ca39a346c0dcfea74346ad10178e6ef68f285b5c10e7ded45a74`.
`peer_public_delivery_hashes.json` records all 36 exact payload hashes. The
actual public copies were checked byte-for-byte against those reviewed hashes.

The public baseline validator was executed with an audit hook rejecting reads
of both the original excluded scratch tree and any delivered `audit/scratch`
subtree. It verifies all 7,684 completed ordinary seventeenth theorem types and
axiom sets against the cached extraction, the 7,486 earlier theorem types/sets,
all 152 ordinary scoped axiom sets, seven graph cases and static evidence
hashes. Independently, the stored ordinary seventeenth Audit, STATUS, actual
7,684-declaration inventory and complete axiom log were compared byte-for-byte
with the actual pushed commit
`1f8208745a50b721c4a12a39dc0bd8b5445fff1b`. Thus the baseline is bound to the
closed ordinary release, not merely to internally consistent copied data.

The candidate preparer was run against the complete, actually registered
251-target ordinary tail in the private fixture. Preparation left its Audit
unchanged. The candidate is exactly the reviewed cached prefix concatenated
with the entire current tail. It retains every old tail byte and every new
target print, inhabitant and ordinary axiom command. Public adoption validation
accepted the exact candidate and rejected independent prefix and tail changes.
A changed baseline evidence file was also rejected by its hash check.

The actual main candidate supplied by root has SHA256
`366022802f207e3f9918c0eac847fc1eb72feaba2a3270dbe80e11d53d579c27`.
Its 69,384-byte preserved tail has SHA256
`3d8bba696ac108f08f4e49bd4b2a3519626e33500304f39f411ebaf0781559c3`.
The reviewed prefix has SHA256
`17822927a0943fc7b9756272c724220fadc232f70f1ff3d4405e270359bfe568`.
These are provenance checks; the complete current gate still performs actual
compilation and target checks after adoption.

The current snapshot helper was read in full. It enumerates every actual
`BfgsVerification` theorem, adds the two scopes' 170 actual names (including
non-theorems), builds the same reviewed graph, rejects missing checked constants
and checked/elaboration type mismatches, and emits actual types and axiom sets.
The public current validator requires equality with the complete central
theorem-name set and every actual signature/axiom set. It retains every frozen
seventeenth report, compares all 18 new ordinary-scoped axiom sets, checks the
exact three delivered source hashes and two target pairs, and checks all 251
registered target signatures. The standard scope helper requires every expected
name exactly once and rejects any nonstandard axiom. It does not substitute an
allowed-axiom subset check for equality to the ordinary baseline.

The optional ordinary-reproduction script was executed in preparation-only
mode. Its generated audit has the exact original standard collector prefix
and the complete current tail, without changing Audit or the checker. Its
`--run` branch invokes Lean and compares every actual theorem type and axiom
set with the cached snapshot. No claim is made here that this optional slow
current audit was executed. Similarly, current eighteenth comparisons are
post-adoption/post-full checks, not fabricated preflight results.

No binding, root-resolution, scratch-input or tail-preservation defect was
found. Historical paths in copied METHOD/review records are explicitly
historical provenance. Runtime inputs are delivered public files. Dynamic
adoption/snapshot logs remain separate from immutable reviewed evidence and
must be retained with the final source freeze and release manifest. This is
audit-tooling evidence; it supplies no mathematical axiom, assumed result or
unchecked computation to any Lean proof.

Independent executable evidence is in `peer_public_delivery_validation.log`
and `peer_validate_public_delivery.py`. The earlier mathematical algorithm
review remains in `INDEPENDENT_PEER_REVIEW.md`.
