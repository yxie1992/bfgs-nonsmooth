# Rigorous master edition: completion contract

The goal is a coherent corrected report with reviewed mathematical statements,
faithful Lean proofs, a complete source/proof index, actual pinned compiler
results and transitive axiom evidence. The original research sources and the
closed milestone19/20 evidence remain unchanged.

1. Reconcile every original source span, including substantive unnamed claims,
   against exact Lean exports. Fill explicit index gaps where the older register
   delegated a mapping to another document. Classify definitions, assumptions,
   open questions and historical evidence separately from proved assertions.
2. Integrate all corrections into a new LaTeX edition. State actual hypotheses
   in place, retain valid restricted statements, remove unsupported historical
   execution claims and identify newly constructed examples. Explain changed
   proof routes and link the actual formal proof chain.
3. Audit every declaration belonging to the project modules, including private
   and compiler-generated names outside the project namespace. Audit theorem
   proofs, mathematical definitions and their dependencies. Distinguish generated
   unsafe implementation artifacts from kernel-visible mathematical axioms.
   Admit no unchecked mathematical axiom or placeholder into a proof.
4. Compile the report and verify its layout. Generate a searchable claim/proof
   index containing exact theorem statements, definitions, source locations and
   axiom sets; printed summaries link to the full index.
5. Independently review source correspondence, changed mathematics, declaration
   coverage and reproducibility. Freeze source and artifact hashes, update this
   edition's status, review, commit and push.

“Verified” means that Lean checks the formal proof under the stated hypotheses
and permitted standard foundations. It does not mean that Lean's consistency
has been proved, that every informal sentence was translated literally, that a
different formal proof route was the original argument, or that an explicitly
open question or unsupported past event has become a theorem.

The present audit has identified a real coverage distinction: the old central
gate enumerated namespace-prefixed theorem declarations. Completing the stronger
module-wide audit was a required gate; the delivered actual run has now passed.
