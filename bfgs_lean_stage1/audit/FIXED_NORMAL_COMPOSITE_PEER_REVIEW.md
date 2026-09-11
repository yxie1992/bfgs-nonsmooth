# Independent review: U.6 and the fully coupled composite family

Result: no mathematical or theorem-statement defect found in the reviewed source snapshot. The scope is the actual tangential-curvature convergence theorem U.6, its local basin, the fully strongly convex composite illustration U.1.1, and the literal U.2 segment prerequisites. This is an independent source/statement review; compiler and transitive-axiom evidence is maintained separately in the `fixed_normal_composite_*` and prerequisite logs.

## Exact source hypotheses

The global U.6 theorem uses a finite convex actual objective and `AdmissibleBFGSRun`, compact initial sublevel inside an open structural neighborhood, convex smooth summand with local C1,1 regularity, finite convex scalar summand with local C1,1 regularity only away from zero, and the actual local equality `F = ψ + h(a·x-b)`. The normal is Euclidean unit. The projected strong convexity is exactly convexity of `ψ - μ‖P_S x‖²/2`, with positive μ. The optimizer is unique and lies on the exceptional plane. Convexity of the structural neighborhood is already included in the `ConvexOn` hypotheses.

The only strict-contour premise is for levels strictly above the minimum and no greater than the actual initial value. No iterate, matrix, step, gradient-field or transport convergence is a final premise. No full normal curvature bound, singular normal derivative bound, globally smooth interface, or regularity of BFGS matrices is added. The local theorem chooses one positive ε before quantifying over actual runs; neither its choice nor the source hypotheses depend on the SPD initialization or valid fixed line-search constants.

## Proof-chain checks

- `FixedNormalSegments` derives a nonempty nontrivial compact normal segment and its full affine line from the actual subdifferential. Distinct actual supports follow from nondifferentiability. The final segment theorem includes the unit normal; the more general intermediate line identities need no hidden rank premise.
- `FixedNormalCocoercivity` uses the global convex objective's supporting inequalities to compare smooth points in potentially disconnected smooth regions. Local test balls and compact bounds supply one common constant. In the cutoff-strip theorem, a nonzero destination cutoff and a sufficiently small actual step put both endpoints in the same compact set separated from the closed exceptional levels. The argument never divides by a normal step or presupposes a positive full-curvature lower bound.
- The arbitrary-linear-map projected supporting inequality is derived from convex combinations and a one-sided limit. Its actual-run specialization is source U.16. Adding the convex normal summand transfers the projected strong convexity from ψ to F.
- The smooth summand is subtracted from every actual support by a convex-remainder chord argument. Tangentially constant functions have only normal supports; hence the exact common projection and scalar contribution monotonicity are proved even if the normal summand is nondifferentiable. Compact cocoercivity of ψ and projection contraction then prove U.17 for actual endpoint supports.
- Local C1,1 regularity of F off the exceptional plane is obtained by the actual derivative chain rule and local Lipschitz composition. It is not assumed globally.
- The tangential-frame theorem derives the actual projected secant and residual estimates. The residual bound is the source U.15 estimate with `‖P_S s‖²`, discharged by U.16. The normal-difference-zero case is inherited from the previously reviewed exact cutoff slope identity, without a division-domain restriction.
- The convergence proof first derives the finite objective limit from the lower bound. Under a putative positive gap, literal strict contour geometry derives vanishing full steps. Projected strong support monotonicity shows that a zero tangential support on the optimizer plane is the optimizer. The constructed cutoff, whole compact cluster-set visibility, actual full-BFGS residual recurrence and reciprocal-mean contradiction finish the proof. Thus the intermediate theorem's secant/step inputs are discharged by the final theorem.
- `FixedNormalFullComposite` treats the fully coupled strong-convexity illustration separately. It assumes strong convexity of F itself, proves its projected version by the orthogonal Pythagorean identity, derives full-step convergence from strong convexity, and reuses the same actual composite secant proof. It does not infer tangential strong convexity of ψ from strong convexity of F.
- The four final target definitions reproduce their corresponding theorem hypotheses and conclusions. End-to-end exports use the actual theorem types directly.

The source's infinite-spike construction, RS failure and variable-jump example in U.7 remain separate obligations; this review does not claim those examples from the composite theorem alone. The original report source was not modified.

## Reviewed source hashes

- `BfgsVerification/FixedNormalSegments.lean`: `bc97a282deccb23652d37fe7e0f97182dbbbd2f383f3ca00fe1129e91d111d41`
- `BfgsVerification/FixedNormalCocoercivity.lean`: `9f53d0c02c141cdf9b6b759dd6961fc8303363484926f87eef801433864332f4`
- `BfgsVerification/FixedNormalTangentialStrong.lean`: `a2fecaeb01bc5a4cfe3ec68afa6588e9cecb1d2fb552e445337f5526475c706c`
- `BfgsVerification/FixedNormalCompositeCalculus.lean`: `eacad823ff1d77b936b7403516488afdd31ea005fe5ebabecce566fbd20fffcc`
- `BfgsVerification/FixedNormalCompositeSmooth.lean`: `e5368c50a2042747a557c82f9d0d327c0dbf82deeea3416f4385f7aabf306189`
- `BfgsVerification/FixedNormalTangentialFrames.lean`: `90673b0c1e8976695167f2b64432fadc3c81fbff4c833bf804682e0c33c57403`
- `BfgsVerification/FixedNormalCompositeConvergence.lean`: `48c41035b6e2326c9c4eca657ac46cde0f35bcc985862e446dfa0dedae19be20`
- `BfgsVerification/FixedNormalCompositeLocal.lean`: `9adbcfb077b568a8750710344f96c5b94fe78fbb9e5bdd9d33150b6ccbe1ff7a`
- `BfgsVerification/FixedNormalFullComposite.lean`: `5461531c05e004b0c49279486cb20fd177021ac4e21195d951eefbc3284e9d64`
- `BfgsVerification/FixedNormalCompositeTargets.lean`: `5a3b5681fb591e0246c49e2ab6401dd18fcc1cea8d3457c60b3b8f5c20d0c86e`
- `BfgsVerification/FixedNormalCompositeEndToEnd.lean`: `8c4e7757932fc3138d973533956ccf212e2b552b1e477ca782f733dae458acc5`
