# Module L Jacobian display precision

Source: unchanged `BFGS_MASTER_REPORT_LaTeX/report/chapters/L.tex`, lines168–180. This scope was independently reviewed in scratch and is now delivered in main after milestone13. It supplements, and does not alter, the released broad interval/spectral proof.

The new final contract is `BfgsVerification.LShapePrecision.actualJacobianPrecision : ActualJacobianPrecisionTarget`. Its only inputs are the fixed original source definitions. It has no supplied root, assumed matrix entries, assumed derivative, assumed numerical enclosure, or external-computation result.

The actual derivative is the Frechet derivative of `LShapeDerivative.shapeMap seedC seedD` at its original shape center `(0,1)`. `actualEntry_eq_jacobian` proves its coordinate entry equals the jet-generated `jacobian seedC seedD i j`, using the already proved `shapeMap_hasFDerivAt`. The generic fine certificate proves bounds for the original formula uniformly on a finer rational box containing the entire original radius-10^-30 algebraic root box. The actual seed is instantiated using the original `AlgebraicSeed.root_spec`; no decimal root is substituted for it.

The generated theorem proves each of the following entries has error at most `1/(2*10^20) = 5e-21`:

| Entry (one-based) | Checked central value |
| --- | --- |
| J11 | 1.11239862507328953465 |
| J12 | 0.64597010273159772922 |
| J21 | 0.75150157042749849873 |
| J22 | 0.49051368858317536674 |

The original four printed values all have absolute error strictly less than `10^-15`. Thus their use as approximate displays is justified. If the source intends rounding to the nearest fifteen digits after the decimal point, the corrected display is

```text
[1.112398625073290  0.645970102731598]
[0.751501570427498  0.490513688583175]
```

The final contract proves all four corrected entries have error strictly less than half of one fifteen-decimal unit. It also proves that the original lower-left entry `0.751501570427499` exceeds the actual entry by **more** than `1/(2*10^15)`, so this last-digit distinction is not a floating-point inference. The discrepancy is about 0.50127 units in the last printed decimal place; it does not change any of the source spectral intervals or signs. The original research source is preserved, and this note records the precision correction separately.

`LShapeFineCertificate.lean` uses the same actual three-update semantic jet construction as the previously released `generate_l_shape_certificate.py`. The changes are explicit rational endpoints: input box resolution10^-30, outward intermediate arithmetic resolution10^-40, and final enclosures of radius5e-21. Each column has229 semantic jet nodes and778 scalar interval nodes. Every arithmetic bound, reciprocal sign, expression linkage, and final inequality is emitted as Lean proof syntax and checked in the kernel. Python only selects proof candidates; it is not in the logical dependency chain. Re-running the historical external automatic-differentiation program is unnecessary.

The generated source compiles with only redundant-tactic warnings inherited from the released generator's semantic linkage strategy. The two-module scope contains16 explicit declarations and one exact source contract. The scoped audit consists of actual compiler logs, printed types, `#print axioms` for every declaration, a strict `Meta.isDefEq` target check, byte-identical candidate regeneration, and frozen source hashes. `bash audit/verify_l_shape_precision.sh` reproduces this scope against the pinned main dependencies. `audit/validate_l_shape_precision.py` checks the scope evidence but does not substitute for Lean.

The frozen two-module scope passed its actual builds, all sixteen type/axiom checks, byte-identical regeneration, and the exact target contract. See `l_shape_precision_validation.log`. Only `propext`, `Classical.choice`, and `Quot.sound` occur in transitive axiom reports. The complete source map records main scoped verification. A subsequent central whole-project release audit remains root-owned. No principal theorem statement requires weakening or a new assumption.
