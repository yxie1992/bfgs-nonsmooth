# Cached collector: adopted full-gate review

Independent post-gate verification: **PASS**.

The actual adopted `Audit.lean` has SHA-256 `366022802f207e3f9918c0eac847fc1eb72feaba2a3270dbe80e11d53d579c27`. Its prefix equals the independently reviewed shared-graph collector. Its entire remaining tail is byte-identical to the ordinary audit captured immediately before adoption, including all 249 prior targets and both actual Module M additions. The captured ordinary audit retains the complete milestone17 tail. No source check was discarded during prefix replacement.

The completed milestone18 transcript and declaration inventory contain exactly 7,704 actual theorem records. An independent comparison checked every printed type and every transitive axiom set against the freshly extracted snapshot, and checked all 251 registered target signatures and their successful central status flags. It also checked the ordinary scoped axiom output for every one of the 18 new declarations and the hashes of all three new proof files. There are no omitted or unexpected axiom reports.

Every one of the 7,684 theorem types and axiom sets from the closed ordinary milestone17 audit remains unchanged. The broader comparison also preserves all 7,721 prior cached theorem/definition/field records. The ordinary milestone17 inventory, transcript and status were bound to the pushed release `1f8208745a50b721c4a12a39dc0bd8b5445fff1b` in the public delivery review. Earlier exhaustive comparison covered all 7,486 prior theorem records and all 152 milestone17 scoped declarations as well.

The new snapshot contains 7,704 theorem roots plus 40 additional scoped declarations. It reported no missing checked constants. Graph construction, reverse reachability and actual-type extraction took 16,090 milliseconds; that measurement excludes imports and the remaining full-audit commands.

The full milestone18 gate uses the reviewed cached collector. A second complete ordinary-collector traversal of all 7,704 current theorems was not required for this milestone: exhaustive ordinary comparison already covers the 7,684 unchanged theorems, and the 18 new scoped declarations have fresh ordinary-collector evidence. `scripts/reproduce_standard_axiom_audit.py --run` remains available for that optional complete traversal while preserving every current tail check. Kernel compilation, source checks and target checks remain part of the full gate.

Evidence:

- `audit/cached_axiom_candidate_independent_validation.log`
- `audit/cached_axiom_post_gate_independent_validation.log`
- `audit/cached_axiom_evidence/current_validation.log`
- `audit/cached_axiom_evidence/current_cached_stats.json`
- `audit/cached_axiom_evidence/INDEPENDENT_PEER_REVIEW.md`
- the public delivery peer review and its frozen hashes

This review made no changes to main proof sources, the adopted audit, or the checker.
