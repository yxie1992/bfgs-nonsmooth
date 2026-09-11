# Experimental cached axiom graph: independent read-only review

Read `CachedAxiomGraph.lean` against the pinned Lean 4.19.0 source
`Lean/Util/CollectAxioms.lean`, and read the graph invocation in
`ProposedAudit.lean`. No algorithmic defect was found in the intended use on
the constructed checked-environment dependency graph. This is a tooling
review, not a new mathematical theorem or authorization to replace the
currently running frozen audit.

The direct dependency cases match the standard collector exactly: axioms and
quotient primitives are terminal; definitions, theorems and opaque constants
traverse both type and value; constructors and recursors traverse only their
type; inductive declarations traverse their type and all constructors. Both
implementations use `env.checked.get.find?`, avoiding substitution of a
possibly inconsistent elaboration-environment body.

The construction records the whole outgoing-edge array before descending into
dependencies. A revisit can therefore suppress recursion without caching an
incomplete *axiom result*. After the complete graph is built, reverse
reachability from each actual axiom reaches exactly its transitive users. The
visited-index worklist handles self-cycles and mutual cycles, including cycles
with an axiom only reachable through a later edge. The problematic shortcut of
memoizing partially completed per-node DFS axiom sets is absent.

The review concerns graphs produced by `visit`, whose indices, names and edge
arrays are coherent; it does not claim that every arbitrary externally
constructed `GraphState` is well formed. `ProposedAudit` throws on any missing
reachable constant and on a checked/elaboration type mismatch at an audit
root. Those checks make the intended preconditions explicit. The proposed
root selection remains the actual `BfgsVerification` theorem constants, and
the remaining ordinary `#print axioms` and exact-target commands are retained.

Axiom arrays must be compared as sets, because graph enumeration can change
their order. The displayed proposal sorts them before output. I read the
closed owner validation: every 7,486 prior actual theorem type and axiom set
matches, every 152 new scoped axiom set matches, no reachable name is missing,
and seven cycle cases pass. The recorded command work is 17,040 ms for 61,417
vertices and 2,678,188 edges. These are the author's complete equivalence tests,
not a fresh independent execution or a sample extrapolation by this reviewer.

Adoption should retain those exhaustive comparisons and the ordinary audit
commands, preserve the current frozen gate, and record the tooling change
separately. No reduction in mathematical theorem or transitive-axiom scope is
justified by the performance improvement.
