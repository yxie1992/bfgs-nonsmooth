# Negative scaling supplement

Run from the repository root:

```sh
python3 editorial/narrative_rebuild/negative_formal/verify.py --run-id NEW_UNIQUE_ID
```

The driver uses the project's pinned Lean 4.19.0 toolchain and Lake search path, compiles `../negative_scaling.lean` into an ignored build directory, and audits every declaration owned by that module, including generated helpers. It compares the toolchain, Lake inputs and canonical declaration index to the existing sealed baseline. This is a fresh supplemental compile and audit, not a fresh rebuild of every imported original library module; root's full-library audit is separate evidence.

The source proves mathematical covariance of the actual full inverse-BFGS update under spatial factor λ and objective factor σ, including strict and nonstrict Armijo–weak-Wolfe comparison equivalences. It asserts no orbit existence, local objective representation, derivative formula for an unspecified objective, positive-definiteness conclusion, or containment of queries. Actual D/L construction exports supply their concrete local values and derivatives and every-query containment.

The independent checked-environment traversal includes declaration types, definition/proof/opaque values, mutual inductive types, constructors, and all recursor reduction rules. It rejects missing, unsafe and partial reachable declarations and every axiom except `propext`, `Classical.choice`, and `Quot.sound`. It checks exact root type/value agreement and per-root agreement of an independent ordinary dependency traversal with `Lean.collectAxioms`.

Run `20260912_covariance_01` passed with 11 module-owned declarations and 10,697 transitive checked declarations. `declarations.json` records exact pretty-printed signatures, direct/structural dependencies, source ranges, axiom sets and safety flags. `dependency_graph.json` retains the full graph. `SUMMARY.json` records actual commands/log hashes, source and pinned-input hashes, compiler version and scope. The empty compile log is an actual warning-free compiler result.

The three allowed axioms are Lean's standard propositional extensionality, classical choice, and quotient soundness foundations. Whitelisting and dependency inspection establish which foundations the proof uses; they do not prove those foundations consistent from within themselves. No custom mathematical axiom or admitted proof is accepted.
