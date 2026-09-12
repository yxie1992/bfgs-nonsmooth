# Actual branch regularity supplement

This isolated module closes the final sentence of the article's lower-curvature theorem for its actual three scalar-ridge branches, both before and after the one fixed whitening transformation. The combined endpoint also includes the entire unchanged original `LWhitening.SmoothLocalFailureTarget`. No original Lean file is modified.

The meaning of second differentiability is `DifferentiableAt ℝ (fderiv ℝ f) 0`. The proof chooses `v = parameter⁻¹ • center`, verifies `dot slope v = 1`, evaluates the actual branch derivative on the line `t • v`, and subtracts the smooth quadratic contribution. This would make the scalar derivative differentiable at zero, contradicting the original proved scalar obstruction. The original exact whitening derivative equivalence transfers the result.

Reproduce from the repository root with a new run identifier:

```sh
python3 editorial/satisfaction_review/branch_formal/verify.py --run-id branch_regularity_replay_01
```

The retained `branch_regularity_01` run passed with three owned theorem declarations and 37,525 declarations in the complete type/value/constructor/mutual-inductive/recursor-rule dependency closure. All reachable mathematical axioms are `propext`, `Classical.choice`, or `Quot.sound`. The auditor rejects unchecked, unsafe, partial and unapproved-axiom dependencies and checks exact root type/value agreement plus agreement with Lean's ordinary axiom collector. It is metadata tooling, not an input to the proofs.

The runner is adapted from the strict positive supplement runner without weakening its guards. It checks the 761 frozen original audit inputs, compiler version, source identities before and after execution, logs every command and both output streams, and retains exact declaration signatures and the full dependency graph. Original library objects are reused: this is a fresh supplement compile/audit, not a fresh original-library build. Compiled objects are ignored; source and compiler/audit logs stay in the repository. `development/compile_01.log` and `compile_02.log` retain exploratory toolchain/elaboration feedback, while the successful retained run is the authoritative completion evidence.
